package main

import (
	"errors"
	"flag"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"math/rand"
	"os"
	"runtime"
	"runtime/debug"
	"sort"
	"strings"
	"time"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/ring/ringqp"
	bfv "github.com/tuneinsight/lattigo/v6/schemes/bgv"
)

// This program implements a homomorphic linear transformation for sparsely packed
// BFV ciphertexts using the n x n matrix U computed from the basis polynomials
//
//   1,
//   X^{step} - X^{N-step},
//   X^{2*step} - X^{N-2*step},
//   ...,
//   X^{(n-1)*step} - X^{N-(n-1)*step},
//
// where step = (N/2)/n.
//
// The matrix U is formed exactly as in the user's previous program:
// for each basis polynomial, decode its plaintext polynomial to BFV slots and keep
// the first n slots as one row of U.
//
// Given an input sparse-packed ciphertext encrypting
//
//   1_r ⊗ (x_0, ..., x_{n-1}),   r = N / n,
//
// the program applies the homomorphic linear map
//
//   v -> v * U,
//
// using cyclic diagonal decomposition and a baby-step giant-step (BSGS) strategy.
// Each diagonal is itself sparsely packed across N slots.
//
// After decryption, the program interprets the output slot vector as a BFV plaintext
// via EncodeRingT and checks whether the sparse polynomial coefficients at
// positions 0, step, 2*step, ..., (n-1)*step match the original input slots.
//
// Lattigo v6 implements BFV through the unified schemes/bgv package.

type CoeffTerm struct {
	Index int
	Value int64
}

type BasisPolyInfo struct {
	Name              string
	Support           []CoeffTerm
	SlotsCentered     []int64
	SlotsMod          []uint64
	FirstNSlotsCenter []int64
	FirstNSlotsMod    []uint64
}

type BSGSStats struct {
	PlainCipherMults int
	Rotations        int
	BabyRotations    int
	GiantRotations   int
	Additions        int
	G                int
	B                int
}

type TimingInfo struct {
	BuildBasis     time.Duration
	BuildDiagonals time.Duration
	KeyGen         time.Duration
	Encrypt        time.Duration
	HomomorphicLT  time.Duration
	DecryptDecode  time.Duration
	CoeffInspect   time.Duration
	Total          time.Duration
}

type PreprocessingTiming struct {
	LUTBuild              time.Duration
	SlotToCoeffMatrix     time.Duration
	SlotToCoeffDiagonals  time.Duration
	SlotToCoeffPlaintexts time.Duration
	PolyPlaintexts        time.Duration
	KeyGen                time.Duration
	TargetSecretBuild     time.Duration
	EvaluationKeyGen      time.Duration
	Total                 time.Duration
}

type ProgressLogger struct {
	Enabled bool
	Start   time.Time
}

func newProgressLogger(enabled bool) *ProgressLogger {
	return &ProgressLogger{Enabled: enabled, Start: time.Now()}
}

func (pl *ProgressLogger) Logf(format string, args ...interface{}) {
	if pl == nil || !pl.Enabled {
		return
	}
	msg := fmt.Sprintf(format, args...)
	fmt.Printf("[progress +%v] %s\n", time.Since(pl.Start).Round(time.Millisecond), msg)
}

var globalProgress *ProgressLogger
var globalProgressBlocks bool

func progressf(format string, args ...interface{}) {
	if globalProgress != nil {
		globalProgress.Logf(format, args...)
	}
}

var globalPolyLTBabySteps = -1
var globalPolyLTGiantSteps = -1

func choosePolyLTBSGS(ell int) (g int, b int, err error) {
	if ell <= 0 {
		return 0, 0, fmt.Errorf("ell must be positive, got %d", ell)
	}
	baby := globalPolyLTBabySteps
	giant := globalPolyLTGiantSteps
	switch {
	case baby <= 0 && giant <= 0:
		g = int(math.Ceil(math.Sqrt(float64(ell))))
		b = (ell + g - 1) / g
	case baby > 0 && giant <= 0:
		g = baby
		if g > ell {
			g = ell
		}
		b = (ell + g - 1) / g
	case baby <= 0 && giant > 0:
		b = giant
		if b > ell {
			b = ell
		}
		g = (ell + b - 1) / b
	case baby > 0 && giant > 0:
		g = baby
		b = giant
		if g <= 0 || b <= 0 {
			return 0, 0, fmt.Errorf("invalid LT BSGS parameters: baby=%d giant=%d", baby, giant)
		}
		if g*b < ell {
			return 0, 0, fmt.Errorf("LT BSGS parameters are too small: baby=%d giant=%d but baby*giant=%d < ell=%d", g, b, g*b, ell)
		}
	}
	if g <= 0 || b <= 0 {
		return 0, 0, fmt.Errorf("invalid LT BSGS split: g=%d b=%d", g, b)
	}
	return g, b, nil
}

func formatPolyLTBSGSSetting(v int) string {
	if v <= 0 {
		return "auto"
	}
	return fmt.Sprintf("%d", v)
}

func isPow2(x int) bool {
	return x > 0 && (x&(x-1)) == 0
}

func log2Pow2(x int) int {
	if !isPow2(x) {
		panic(fmt.Sprintf("x=%d is not a power of two", x))
	}
	return bits.TrailingZeros(uint(x))
}

type AutoProfileSpec struct {
	Name      string
	LogN      int
	BaseQ0    int
	RepeatedQ int
	LogP      []int
	MaxDepth  int
}

var autoProfiles = []AutoProfileSpec{
	{Name: "BFV-128-N12-D1", LogN: 12, BaseQ0: 39, RepeatedQ: 31, LogP: []int{39}, MaxDepth: 1},
	{Name: "BFV-128-N13-D4", LogN: 13, BaseQ0: 42, RepeatedQ: 33, LogP: []int{44}, MaxDepth: 4},
	{Name: "BFV-128-N14-D9", LogN: 14, BaseQ0: 44, RepeatedQ: 34, LogP: []int{44, 44}, MaxDepth: 9},
	{Name: "BFV-128-N15-D19", LogN: 15, BaseQ0: 43, RepeatedQ: 34, LogP: []int{45, 45, 45, 45}, MaxDepth: 19},
}

func (p AutoProfileSpec) BuildLiteral(depth int, plainMod uint64) (bfv.ParametersLiteral, error) {
	if depth < 1 {
		return bfv.ParametersLiteral{}, fmt.Errorf("depth must be at least 1, got %d", depth)
	}
	if depth > p.MaxDepth {
		return bfv.ParametersLiteral{}, fmt.Errorf("profile %s supports depth at most %d, got %d", p.Name, p.MaxDepth, depth)
	}
	logQ := make([]int, depth+1)
	logQ[0] = p.BaseQ0
	for i := 1; i <= depth; i++ {
		logQ[i] = p.RepeatedQ
	}
	return bfv.ParametersLiteral{
		LogN:             p.LogN,
		LogQ:             logQ,
		LogP:             append([]int(nil), p.LogP...),
		PlaintextModulus: plainMod,
	}, nil
}

func chooseAutoProfileForLogNDepth(logN, depth int) (AutoProfileSpec, error) {
	for _, p := range autoProfiles {
		if p.LogN == logN {
			if depth > p.MaxDepth {
				return AutoProfileSpec{}, fmt.Errorf("automatic parameter selection for logN=%d supports depth at most %d, but this run needs at least %d; please pass a longer -logq explicitly", logN, p.MaxDepth, depth)
			}
			return p, nil
		}
	}
	return AutoProfileSpec{}, fmt.Errorf("no automatic parameter profile for logN=%d; please pass -logq and -logp explicitly", logN)
}

func maxInt(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func monomialConsumedDepth(s int) int {
	if s <= 0 || !isPow2(s) {
		panic(fmt.Sprintf("s=%d must be a positive power of two", s))
	}
	switch s {
	case 1:
		return 0
	case 2:
		return 1
	default:
		return bits.TrailingZeros(uint(s)) + 1
	}
}

func autoDepthForWrappedPolyEval(r, d int) (int, error) {
	if !isPow2(d) {
		return 0, fmt.Errorf("d=%d must be a power of two", d)
	}
	if d <= r || d > r*r || d%r != 0 {
		return 0, fmt.Errorf("Algorithm 5 requires r < d <= r^2 and r|d, got d=%d, r=%d", d, r)
	}
	s := d / r
	consumed := log2Pow2(r) + monomialConsumedDepth(s) + 1
	return consumed + 1, nil
}

func parseBitList(spec string) ([]int, error) {
	spec = strings.TrimSpace(strings.NewReplacer("，", ",", "；", ";").Replace(spec))
	if spec == "" {
		return nil, errors.New("empty bit-size list")
	}
	parts := strings.Split(spec, ",")
	out := make([]int, len(parts))
	for i, part := range parts {
		part = strings.TrimSpace(part)
		if part == "" {
			return nil, fmt.Errorf("empty bit-size entry at position %d", i)
		}
		if _, err := fmt.Sscan(part, &out[i]); err != nil {
			return nil, fmt.Errorf("failed to parse bit-size entry %q: %w", part, err)
		}
		if out[i] <= 0 {
			return nil, fmt.Errorf("bit-size entry at position %d must be positive, got %d", i, out[i])
		}
	}
	return out, nil
}

func validateLTLevel(level, maxLevel int, name string) error {
	if level == -1 {
		return nil
	}
	if level < 1 {
		return fmt.Errorf("%s must be -1 or at least 1, got %d", name, level)
	}
	if level > maxLevel {
		return fmt.Errorf("%s=%d exceeds MaxLevel=%d", name, level, maxLevel)
	}
	return nil
}

func chooseLiteral(logN int, plainMod uint64, logQBits, logPBits []int) (bfv.ParametersLiteral, error) {
	if logN < 3 {
		return bfv.ParametersLiteral{}, fmt.Errorf("logN=%d is too small; Lattigo requires N >= 8", logN)
	}

	if len(logQBits) < 2 {
		return bfv.ParametersLiteral{}, fmt.Errorf("need at least two Q moduli for the leveled SlotToCoeff path, got LogQ=%v", logQBits)
	}
	if len(logPBits) == 0 {
		return bfv.ParametersLiteral{}, errors.New("need at least one P modulus for BFV-side key switching")
	}

	return bfv.ParametersLiteral{
		LogN:             logN,
		LogQ:             append([]int(nil), logQBits...),
		LogP:             append([]int(nil), logPBits...),
		PlaintextModulus: plainMod,
	}, nil
}

func centeredFromUint(v uint64, mod uint64) int64 {
	if v <= mod/2 {
		return int64(v)
	}
	return int64(v) - int64(mod)
}

func toUintMod(v int64, mod uint64) uint64 {
	m := int64(mod)
	v %= m
	if v < 0 {
		v += m
	}
	return uint64(v)
}

func reduceCentered(v int64, mod uint64) int64 {
	return centeredFromUint(toUintMod(v, mod), mod)
}

func mulMod(a, b, mod uint64) uint64 {
	return (a * b) % mod
}

func parseVector(s string) ([]int64, error) {
	s = strings.TrimSpace(s)
	if s == "" {
		return nil, nil
	}
	parts := strings.Split(s, ",")
	out := make([]int64, len(parts))
	for i, part := range parts {
		part = strings.TrimSpace(part)
		if part == "" {
			return nil, fmt.Errorf("empty entry at position %d", i)
		}
		var v int64
		if _, err := fmt.Sscan(part, &v); err != nil {
			return nil, fmt.Errorf("failed to parse x[%d]=%q: %w", i, part, err)
		}
		out[i] = v
	}
	return out, nil
}

func splitNumericFields(s string) []string {
	return strings.FieldsFunc(s, func(r rune) bool {
		switch r {
		case ',', ';', '\n', '\r', '\t', ' ':
			return true
		default:
			return false
		}
	})
}

func parseUintTableFlexible(spec string) ([]uint64, error) {
	spec = strings.TrimSpace(spec)
	if spec == "" {
		return nil, nil
	}
	parts := splitNumericFields(spec)
	out := make([]uint64, len(parts))
	for i, part := range parts {
		if _, err := fmt.Sscan(part, &out[i]); err != nil {
			return nil, fmt.Errorf("failed to parse table entry %q: %w", part, err)
		}
	}
	return out, nil
}

func readUintTableFromFile(path string) ([]uint64, error) {
	if strings.TrimSpace(path) == "" {
		return nil, nil
	}
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	return parseUintTableFlexible(string(data))
}

func makeDefaultMessages(n int, p uint64) []uint64 {
	out := make([]uint64, n)
	for i := range out {
		out[i] = uint64(i) % p
	}
	return out
}

func makeRandomMessages(n int, p uint64, seed int64) []uint64 {
	rng := rand.New(rand.NewSource(seed))
	out := make([]uint64, n)
	for i := range out {
		out[i] = uint64(rng.Int63n(int64(p)))
	}
	return out
}

func sampleTruncatedDiscreteGaussian(n int, sigma float64, bound int64, seed int64) []int64 {
	if bound <= 0 {
		panic(fmt.Sprintf("invalid Gaussian truncation bound %d", bound))
	}
	rng := rand.New(rand.NewSource(seed))
	out := make([]int64, n)
	for i := range out {
		if sigma <= 0 {
			out[i] = 0
			continue
		}
		for {
			v := int64(math.Round(rng.NormFloat64() * sigma))
			if abs64(v) < bound {
				out[i] = v
				break
			}
		}
	}
	return out
}

func generateRandomLWECiphertexts(msgMod []uint64, secret []int64, alpha, t uint64, noises []int64, aSeed int64) ([]LWECiphertext, []uint64, error) {
	if len(msgMod) != len(noises) {
		return nil, nil, fmt.Errorf("len(msgMod)=%d != len(noises)=%d", len(msgMod), len(noises))
	}
	if len(secret) == 0 {
		return nil, nil, errors.New("empty LWE secret")
	}
	rng := rand.New(rand.NewSource(aSeed))
	out := make([]LWECiphertext, len(msgMod))
	xMod := make([]uint64, len(msgMod))
	for i := range msgMod {
		a := make([]uint64, len(secret))
		for j := range a {
			a[j] = uint64(rng.Int63n(int64(t)))
		}
		phase := toUintMod(int64(alpha)*int64(msgMod[i])+noises[i], t)
		inner := uint64(0)
		for j, aj := range a {
			inner += mulSignedMod(aj, secret[j], t)
			if inner >= t {
				inner %= t
			}
		}
		out[i] = LWECiphertext{A: a, B: (inner + phase) % t}
		xMod[i] = phase
	}
	return out, xMod, nil
}

func buildSecretBlockSlots(secret []int64, blockStart, rho, m int, mod uint64) []uint64 {
	out := make([]uint64, rho*m)
	for row := 0; row < rho; row++ {
		idx := blockStart + row
		var v int64
		if idx < len(secret) {
			v = secret[idx]
		}
		vm := toUintMod(v, mod)
		base := row * m
		for col := 0; col < m; col++ {
			out[base+col] = vm
		}
	}
	return out
}

func buildMaskBlockSlots(lweCts []LWECiphertext, blockStart, rho, m int, mod uint64) []uint64 {
	out := make([]uint64, rho*m)
	for row := 0; row < rho; row++ {
		coord := blockStart + row
		base := row * m
		for col := 0; col < m; col++ {
			if coord < len(lweCts[col].A) {
				out[base+col] = negateMod(lweCts[col].A[coord], mod)
			} else {
				out[base+col] = 0
			}
		}
	}
	return out
}

func preprocessEncryptedSecretBlocks(params bfv.Parameters, encoder *bfv.Encoder, enc *rlwe.Encryptor, secret []int64, m int) ([]*rlwe.Ciphertext, error) {
	if len(secret) == 0 {
		return nil, errors.New("empty LWE secret")
	}
	if m <= 0 || params.MaxSlots()%m != 0 {
		return nil, fmt.Errorf("invalid m=%d for MaxSlots=%d", m, params.MaxSlots())
	}
	rho := params.MaxSlots() / m
	blocks := (len(secret) + rho - 1) / rho
	out := make([]*rlwe.Ciphertext, blocks)
	for ell := 0; ell < blocks; ell++ {
		vals := buildSecretBlockSlots(secret, ell*rho, rho, m, params.PlaintextModulus())
		pt, err := encodeBatchedPlaintextAtMaxLevel(params, encoder, vals)
		if err != nil {
			return nil, fmt.Errorf("failed to encode encrypted-secret block %d: %w", ell, err)
		}
		ct, err := enc.EncryptNew(pt)
		if err != nil {
			return nil, fmt.Errorf("failed to encrypt secret block %d: %w", ell, err)
		}
		out[ell] = ct
	}
	return out, nil
}

func homomorphicPackLWECiphertexts(params bfv.Parameters, eval *bfv.Evaluator, secretBlocks []*rlwe.Ciphertext, lweCts []LWECiphertext, m int) (*rlwe.Ciphertext, error) {
	if len(lweCts) != m {
		return nil, fmt.Errorf("len(lweCts)=%d != m=%d", len(lweCts), m)
	}
	if len(secretBlocks) == 0 {
		return nil, errors.New("no encrypted secret blocks")
	}
	rho := params.MaxSlots() / m
	var accRows *rlwe.Ciphertext
	for ell, ctS := range secretBlocks {
		mask := buildMaskBlockSlots(lweCts, ell*rho, rho, m, params.PlaintextModulus())
		term, err := mulPlainRescale(eval, ctS, mask)
		if err != nil {
			return nil, fmt.Errorf("packing plaintext-ciphertext multiplication for secret block %d failed: %w", ell, err)
		}
		if accRows == nil {
			accRows = term
		} else {
			alignCiphertextLevels(eval, accRows, term)
			accRows, err = eval.AddNew(accRows, term)
			if err != nil {
				return nil, fmt.Errorf("packing add for secret block %d failed: %w", ell, err)
			}
		}
	}
	if accRows == nil {
		return nil, errors.New("packing accumulator is nil")
	}
	ctInner, err := sparseRotateAndSum(params, eval, accRows, m, rho)
	if err != nil {
		return nil, fmt.Errorf("packing row-sum failed: %w", err)
	}
	bVec := make([]uint64, m)
	for i := range lweCts {
		bVec[i] = lweCts[i].B
	}
	bPacked := repeatVector(bVec, rho)
	ctOut, err := eval.AddNew(ctInner, bPacked)
	if err != nil {
		return nil, fmt.Errorf("adding replicated b-vector failed: %w", err)
	}
	return ctOut, nil
}

func parseAffineSpec(spec string) (uint64, uint64, error) {
	parts := strings.Split(spec, ":")
	if len(parts) != 2 {
		return 0, 0, fmt.Errorf("affine spec %q must have the form affine:a,b", spec)
	}
	ab := strings.Split(parts[1], ",")
	if len(ab) != 2 {
		return 0, 0, fmt.Errorf("affine spec %q must have two parameters a,b", spec)
	}
	var a, b uint64
	if _, err := fmt.Sscan(strings.TrimSpace(ab[0]), &a); err != nil {
		return 0, 0, fmt.Errorf("failed to parse affine parameter a in %q: %w", spec, err)
	}
	if _, err := fmt.Sscan(strings.TrimSpace(ab[1]), &b); err != nil {
		return 0, 0, fmt.Errorf("failed to parse affine parameter b in %q: %w", spec, err)
	}
	return a, b, nil
}

func buildFunctionTable(p uint64, funcSpec, inlineTable, filePath string) ([]uint64, string, error) {
	var vals []uint64
	var err error
	if strings.TrimSpace(filePath) != "" {
		vals, err = readUintTableFromFile(filePath)
		if err != nil {
			return nil, "", fmt.Errorf("failed to read -func-file: %w", err)
		}
	} else if strings.TrimSpace(inlineTable) != "" {
		vals, err = parseUintTableFlexible(inlineTable)
		if err != nil {
			return nil, "", fmt.Errorf("failed to parse -func-table: %w", err)
		}
	}
	if len(vals) > 0 {
		if len(vals) != int(p) {
			return nil, "", fmt.Errorf("function table length must be exactly p=%d, got %d", p, len(vals))
		}
		for i := range vals {
			vals[i] %= p
		}
		return vals, "explicit lookup table", nil
	}

	tab := make([]uint64, p)
	spec := strings.ToLower(strings.TrimSpace(funcSpec))
	desc := spec
	switch {
	case spec == "", spec == "identity":
		for i := range tab {
			tab[i] = uint64(i)
		}
		desc = "identity"
	case spec == "square":
		for i := range tab {
			x := uint64(i)
			tab[i] = (x * x) % p
		}
		desc = "square"
	case spec == "cube":
		for i := range tab {
			x := uint64(i)
			tab[i] = (x * x % p) * x % p
		}
		desc = "cube"
	case spec == "neg":
		for i := range tab {
			if i == 0 {
				tab[i] = 0
			} else {
				tab[i] = p - uint64(i)
			}
		}
		desc = "negation"
	case strings.HasPrefix(spec, "affine:"):
		a, b, err := parseAffineSpec(spec)
		if err != nil {
			return nil, "", err
		}
		for i := range tab {
			tab[i] = (a*uint64(i) + b) % p
		}
		desc = fmt.Sprintf("affine map %d*x+%d mod %d", a, b, p)
	default:
		return nil, "", fmt.Errorf("unsupported -func %q: expected identity|square|cube|neg|affine:a,b or provide -func-table/-func-file", funcSpec)
	}
	return tab, desc, nil
}

func decodePhaseToMessageModP(phase, alpha, p, t uint64) uint64 {
	_ = t
	return ((phase + alpha/2) / alpha) % p
}

func powMod(a, e, mod uint64) uint64 {
	res := uint64(1 % mod)
	base := a % mod
	for e > 0 {
		if e&1 == 1 {
			res = mulMod(res, base, mod)
		}
		base = mulMod(base, base, mod)
		e >>= 1
	}
	return res
}

func distinctPrimeFactors(n uint64) []uint64 {
	factors := make([]uint64, 0)
	if n%2 == 0 {
		factors = append(factors, 2)
		for n%2 == 0 {
			n /= 2
		}
	}
	for d := uint64(3); d*d <= n; d += 2 {
		if n%d == 0 {
			factors = append(factors, d)
			for n%d == 0 {
				n /= d
			}
		}
	}
	if n > 1 {
		factors = append(factors, n)
	}
	return factors
}

func findPrimitiveRootPrime(mod uint64) (uint64, error) {
	if mod < 3 {
		return 0, fmt.Errorf("modulus %d is too small", mod)
	}
	order := mod - 1
	factors := distinctPrimeFactors(order)
	for g := uint64(2); g < mod; g++ {
		ok := true
		for _, q := range factors {
			if powMod(g, order/q, mod) == 1 {
				ok = false
				break
			}
		}
		if ok {
			return g, nil
		}
	}
	return 0, fmt.Errorf("failed to find primitive root modulo %d", mod)
}

func findPrimitiveRootPow2Field(mod uint64) (uint64, error) {
	order := mod - 1
	if order == 0 || (order&(order-1)) != 0 {
		return 0, fmt.Errorf("modulus %d does not have multiplicative group of power-of-two order", mod)
	}
	for g := uint64(2); g < mod; g++ {
		if powMod(g, order, mod) == 1 && powMod(g, order/2, mod) != 1 {
			return g, nil
		}
	}
	return 0, fmt.Errorf("failed to find primitive root modulo %d", mod)
}

func bitReversePermutation(a []uint64) {
	n := len(a)
	j := 0
	for i := 1; i < n; i++ {
		bit := n >> 1
		for ; j&bit != 0; bit >>= 1 {
			j ^= bit
		}
		j ^= bit
		if i < j {
			a[i], a[j] = a[j], a[i]
		}
	}
}

func nttForwardMod(a []uint64, root, mod uint64) []uint64 {
	out := append([]uint64(nil), a...)
	n := len(out)
	bitReversePermutation(out)
	for length := 2; length <= n; length <<= 1 {
		wlen := powMod(root, uint64(n/length), mod)
		half := length >> 1
		for i := 0; i < n; i += length {
			w := uint64(1)
			for j := 0; j < half; j++ {
				u := out[i+j]
				v := mulMod(out[i+j+half], w, mod)
				sum := u + v
				if sum >= mod {
					sum -= mod
				}
				diff := u
				if diff >= v {
					diff -= v
				} else {
					diff += mod - v
				}
				out[i+j] = sum
				out[i+j+half] = diff
				w = mulMod(w, wlen, mod)
			}
		}
	}
	return out
}

func nttForwardMixedPow2Odd(a []uint64, root, mod uint64) ([]uint64, error) {
	n := len(a)
	if n == 0 {
		return nil, errors.New("empty sequence")
	}
	if isPow2(n) {
		return nttForwardMod(a, root, mod), nil
	}
	twoPow := 1 << bits.TrailingZeros(uint(n))
	odd := n / twoPow
	if odd == 1 {
		return nttForwardMod(a, root, mod), nil
	}
	rootPow2 := powMod(root, uint64(odd), mod)
	rootOdd := powMod(root, uint64(twoPow), mod)
	subs := make([][]uint64, odd)
	for j1 := 0; j1 < odd; j1++ {
		sub := make([]uint64, twoPow)
		for j2 := 0; j2 < twoPow; j2++ {
			sub[j2] = a[j1+odd*j2]
		}
		subs[j1] = nttForwardMod(sub, rootPow2, mod)
	}
	oddPow := make([][]uint64, odd)
	for k1 := 0; k1 < odd; k1++ {
		oddPow[k1] = make([]uint64, odd)
		step := powMod(rootOdd, uint64(k1), mod)
		oddPow[k1][0] = 1
		for j1 := 1; j1 < odd; j1++ {
			oddPow[k1][j1] = mulMod(oddPow[k1][j1-1], step, mod)
		}
	}
	out := make([]uint64, n)
	for k2 := 0; k2 < twoPow; k2++ {
		twStep := powMod(root, uint64(k2), mod)
		v := make([]uint64, odd)
		tw := uint64(1)
		for j1 := 0; j1 < odd; j1++ {
			v[j1] = mulMod(subs[j1][k2], tw, mod)
			tw = mulMod(tw, twStep, mod)
		}
		for k1 := 0; k1 < odd; k1++ {
			acc := uint64(0)
			for j1 := 0; j1 < odd; j1++ {
				acc += mulMod(v[j1], oddPow[k1][j1], mod)
				if acc >= mod {
					acc %= mod
				}
			}
			out[k2+twoPow*k1] = acc % mod
		}
	}
	return out, nil
}

func buildLUTPolynomialCoefficientsPow2Exact(t, p uint64, funcTable []uint64) ([]uint64, error) {
	if len(funcTable) != int(p) {
		return nil, fmt.Errorf("function table length must be p=%d, got %d", p, len(funcTable))
	}
	alpha := t / p
	if alpha == 0 {
		return nil, fmt.Errorf("alpha=floor(t/p)=0 for t=%d, p=%d", t, p)
	}
	order := int(t - 1)
	if !isPow2(order) {
		return nil, fmt.Errorf("t-1=%d must be a power of two for the 9bit fast interpolation path", order)
	}
	root, err := findPrimitiveRootPow2Field(t)
	if err != nil {
		return nil, err
	}
	seq := make([]uint64, order)
	x := uint64(1)
	for j := 0; j < order; j++ {
		mHat := decodePhaseToMessageModP(x, alpha, p, t)
		seq[j] = mulMod(alpha, funcTable[mHat]%p, t)
		x = mulMod(x, root, t)
	}
	dft := nttForwardMod(seq, root, t)
	coeff := make([]uint64, order+1)
	y0 := mulMod(alpha, funcTable[0]%p, t)
	coeff[0] = y0
	for i := 1; i < order; i++ {
		coeff[i] = negateMod(dft[order-i], t)
	}
	coeff[order] = negateMod((y0+dft[0])%t, t)
	return coeff, nil
}

func buildLUTPolynomialCoefficientsGeneral(t, p uint64, funcTable []uint64) ([]uint64, error) {
	if len(funcTable) != int(p) {
		return nil, fmt.Errorf("function table length must be p=%d, got %d", p, len(funcTable))
	}
	alpha := t / p
	if alpha == 0 {
		return nil, fmt.Errorf("alpha=floor(t/p)=0 for t=%d, p=%d", t, p)
	}
	order := int(t - 1)
	root, err := findPrimitiveRootPrime(t)
	if err != nil {
		return nil, err
	}
	seq := make([]uint64, order)
	x := uint64(1)
	for j := 0; j < order; j++ {
		mHat := decodePhaseToMessageModP(x, alpha, p, t)
		seq[j] = mulMod(alpha, funcTable[mHat]%p, t)
		x = mulMod(x, root, t)
	}
	dft, err := nttForwardMixedPow2Odd(seq, root, t)
	if err != nil {
		return nil, err
	}
	coeff := make([]uint64, order+1)
	y0 := mulMod(alpha, funcTable[0]%p, t)
	coeff[0] = y0
	for i := 1; i < order; i++ {
		coeff[i] = negateMod(dft[order-i], t)
	}
	coeff[order] = negateMod((y0+dft[0])%t, t)
	return coeff, nil
}

func makeDefaultVector(n int) []int64 {
	out := make([]int64, n)
	for i := range out {
		out[i] = int64(i + 1)
	}
	return out
}

func makeRandomVector(n int, mod uint64, seed int64) []int64 {
	rng := rand.New(rand.NewSource(seed))
	out := make([]int64, n)
	for i := range out {
		out[i] = int64(rng.Int63n(int64(mod)))
	}
	return out
}

func sparsePackMod(base []uint64, N int) ([]uint64, int, error) {
	if len(base) == 0 {
		return nil, 0, errors.New("base vector is empty")
	}
	if N%len(base) != 0 {
		return nil, 0, fmt.Errorf("len(base)=%d must divide N=%d", len(base), N)
	}
	r := N / len(base)
	out := make([]uint64, N)
	for rep := 0; rep < r; rep++ {
		copy(out[rep*len(base):(rep+1)*len(base)], base)
	}
	return out, r, nil
}

func centeredSlice(v []uint64, mod uint64) []int64 {
	out := make([]int64, len(v))
	for i, x := range v {
		out[i] = centeredFromUint(x, mod)
	}
	return out
}

func symbolicBasisName(idx, N, step int) string {
	if idx == 0 {
		return "1"
	}
	k := idx * step
	return fmt.Sprintf("X^%d - X^%d", k, N-k)
}

func buildBasisPolynomialCoefficients(idx, N, step int, plainMod uint64) ([]uint64, []CoeffTerm) {
	coeffs := make([]uint64, N)
	terms := make([]CoeffTerm, 0, 2)

	if idx == 0 {
		coeffs[0] = 1
		terms = append(terms, CoeffTerm{Index: 0, Value: 1})
		return coeffs, terms
	}

	k := idx * step
	coeffs[k] = 1
	coeffs[N-k] = plainMod - 1
	terms = append(terms,
		CoeffTerm{Index: k, Value: 1},
		CoeffTerm{Index: N - k, Value: -1},
	)
	return coeffs, terms
}

func decodePolynomialToSlots(params bfv.Parameters, encoder *bfv.Encoder, coeffs []uint64) ([]int64, []uint64, error) {
	polyT := ring.NewPoly(params.N(), 0)
	copy(polyT.Coeffs[0], coeffs)
	scale := rlwe.NewScale(1)

	slotsCentered := make([]int64, params.MaxSlots())
	if err := encoder.DecodeRingT(polyT, scale, slotsCentered); err != nil {
		return nil, nil, err
	}

	slotsMod := make([]uint64, params.MaxSlots())
	if err := encoder.DecodeRingT(polyT, scale, slotsMod); err != nil {
		return nil, nil, err
	}

	return slotsCentered, slotsMod, nil
}

func buildBasisMatrixU(params bfv.Parameters, encoder *bfv.Encoder, N, n int, plainMod uint64) ([]BasisPolyInfo, [][]uint64, [][]int64, error) {
	step := (N / 2) / n
	basisInfo := make([]BasisPolyInfo, n)
	matrixMod := make([][]uint64, n)
	matrixCentered := make([][]int64, n)

	for idx := 0; idx < n; idx++ {
		coeffs, support := buildBasisPolynomialCoefficients(idx, N, step, plainMod)
		slotsCentered, slotsMod, err := decodePolynomialToSlots(params, encoder, coeffs)
		if err != nil {
			return nil, nil, nil, fmt.Errorf("DecodeRingT failed for basis %d: %w", idx, err)
		}

		basisInfo[idx] = BasisPolyInfo{
			Name:              symbolicBasisName(idx, N, step),
			Support:           support,
			SlotsCentered:     slotsCentered,
			SlotsMod:          slotsMod,
			FirstNSlotsCenter: append([]int64(nil), slotsCentered[:n]...),
			FirstNSlotsMod:    append([]uint64(nil), slotsMod[:n]...),
		}
		matrixMod[idx] = append([]uint64(nil), slotsMod[:n]...)
		matrixCentered[idx] = append([]int64(nil), slotsCentered[:n]...)
	}

	return basisInfo, matrixMod, matrixCentered, nil
}

// buildRightMulDiagonals builds cyclic diagonals for row-vector right multiplication.
//
// If y = x * U and rot_j(x)[k] = x[(k+j) mod n], then
//
//	y[k] = sum_j diag_j[k] * rot_j(x)[k]
//
// with
//
//	diag_j[k] = U[(k+j) mod n][k].
func buildRightMulDiagonals(U [][]uint64, plainMod uint64) ([][]uint64, [][]int64) {
	n := len(U)
	diagMod := make([][]uint64, n)
	diagCentered := make([][]int64, n)
	for j := 0; j < n; j++ {
		diagMod[j] = make([]uint64, n)
		diagCentered[j] = make([]int64, n)
		for k := 0; k < n; k++ {
			v := U[(k+j)%n][k] % plainMod
			diagMod[j][k] = v
			diagCentered[j][k] = centeredFromUint(v, plainMod)
		}
	}
	return diagMod, diagCentered
}

func repeatVector(v []uint64, times int) []uint64 {
	out := make([]uint64, len(v)*times)
	for i := 0; i < times; i++ {
		copy(out[i*len(v):(i+1)*len(v)], v)
	}
	return out
}

func repeatVectorCentered(v []int64, times int) []int64 {
	out := make([]int64, len(v)*times)
	for i := 0; i < times; i++ {
		copy(out[i*len(v):(i+1)*len(v)], v)
	}
	return out
}

func rotateLeftUint64(v []uint64, shift int) []uint64 {
	n := len(v)
	if n == 0 {
		return nil
	}
	shift %= n
	if shift < 0 {
		shift += n
	}
	out := make([]uint64, n)
	copy(out, v[shift:])
	copy(out[n-shift:], v[:shift])
	return out
}

func rotateLeftInt64(v []int64, shift int) []int64 {
	n := len(v)
	if n == 0 {
		return nil
	}
	shift %= n
	if shift < 0 {
		shift += n
	}
	out := make([]int64, n)
	copy(out, v[shift:])
	copy(out[n-shift:], v[:shift])
	return out
}

func vectorTimesMatrixMod(row []uint64, U [][]uint64, mod uint64) []uint64 {
	n := len(row)
	out := make([]uint64, n)
	for j := 0; j < n; j++ {
		var acc uint64
		for i := 0; i < n; i++ {
			acc = (acc + (row[i]%mod)*(U[i][j]%mod)) % mod
		}
		out[j] = acc
	}
	return out
}

func collectPositiveSparsePositions(n, step int) []int {
	out := make([]int, n)
	out[0] = 0
	for i := 1; i < n; i++ {
		out[i] = i * step
	}
	return out
}

func collectNegativeSparsePositions(n, N, step int) []int {
	out := make([]int, 0, n-1)
	for i := 1; i < n; i++ {
		out = append(out, N-i*step)
	}
	return out
}

func encodeSlotsToPolynomialCoefficients(params bfv.Parameters, encoder *bfv.Encoder, slots []uint64) ([]uint64, []int64, error) {
	pT := ring.NewPoly(params.N(), 0)
	if err := encoder.EncodeRingT(slots, rlwe.NewScale(1), pT); err != nil {
		return nil, nil, err
	}
	coeffsMod := append([]uint64(nil), pT.Coeffs[0]...)
	coeffsCentered := centeredSlice(coeffsMod, params.PlaintextModulus())
	return coeffsMod, coeffsCentered, nil
}

func extractCoefficientsAtPositions(coeffs []int64, positions []int) []int64 {
	out := make([]int64, len(positions))
	for i, pos := range positions {
		out[i] = coeffs[pos]
	}
	return out
}

func supportPositionsCentered(coeffs []int64) []int {
	out := make([]int, 0)
	for i, c := range coeffs {
		if c != 0 {
			out = append(out, i)
		}
	}
	return out
}

func buildPolynomialString(coeffs []int64, maxTerms int) string {
	type term struct {
		idx int
		val int64
	}
	terms := make([]term, 0)
	for i, c := range coeffs {
		if c != 0 {
			terms = append(terms, term{idx: i, val: c})
		}
	}
	if len(terms) == 0 {
		return "0"
	}
	if maxTerms > 0 && len(terms) > maxTerms {
		terms = terms[:maxTerms]
	}
	parts := make([]string, len(terms))
	for i, t := range terms {
		switch t.idx {
		case 0:
			parts[i] = fmt.Sprintf("%d", t.val)
		case 1:
			parts[i] = fmt.Sprintf("%d*X", t.val)
		default:
			parts[i] = fmt.Sprintf("%d*X^%d", t.val, t.idx)
		}
	}
	return strings.Join(parts, " + ")
}

func formatCoeffSupport(terms []CoeffTerm) string {
	parts := make([]string, len(terms))
	for i, term := range terms {
		parts[i] = fmt.Sprintf("(%d:%d)", term.Index, term.Value)
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

func matrixStringInt64(mat [][]int64) string {
	var sb strings.Builder
	sb.WriteString("[\n")
	for i := range mat {
		sb.WriteString("  ")
		sb.WriteString(fmt.Sprint(mat[i]))
		if i != len(mat)-1 {
			sb.WriteString(",")
		}
		sb.WriteString("\n")
	}
	sb.WriteString("]")
	return sb.String()
}

func uniqueRotationShiftsForBSGS(n int) []int {
	g := int(math.Ceil(math.Sqrt(float64(n))))
	b := (n + g - 1) / g
	set := map[int]struct{}{}
	for k := 1; k < g; k++ {
		set[k] = struct{}{}
	}
	for i := 1; i < b; i++ {
		shift := i * g
		if shift < n {
			set[shift] = struct{}{}
		}
	}
	out := make([]int, 0, len(set))
	for s := range set {
		out = append(out, s)
	}
	sort.Ints(out)
	return out
}

type PreprocessedBSGSPlaintexts struct {
	G         int
	B         int
	ShiftedPT []*rlwe.Plaintext
}

func encodeBatchedPlaintextAtMaxLevel(params bfv.Parameters, encoder *bfv.Encoder, values []uint64) (*rlwe.Plaintext, error) {
	pt := bfv.NewPlaintext(params, params.MaxLevel())
	if err := encoder.Encode(values, pt); err != nil {
		return nil, err
	}
	return pt, nil
}

func mulOperandNoRescale(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand) (*rlwe.Ciphertext, error) {
	out, err := eval.MulNew(ct, op)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func mulOperandRescale(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand) (*rlwe.Ciphertext, error) {
	out, err := mulOperandNoRescale(eval, ct, op)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(out, out); err != nil {
		return nil, err
	}
	return out, nil
}

func preprocessSlotToCoeffBSGSPlaintexts(params bfv.Parameters, encoder *bfv.Encoder, diagExt [][]uint64) (*PreprocessedBSGSPlaintexts, error) {
	n := len(diagExt)
	if n == 0 {
		return nil, errors.New("no diagonals provided")
	}
	N := len(diagExt[0])
	for j := range diagExt {
		if len(diagExt[j]) != N {
			return nil, fmt.Errorf("diagonal %d has inconsistent length", j)
		}
	}
	g := int(math.Ceil(math.Sqrt(float64(n))))
	b := (n + g - 1) / g
	shiftedPT := make([]*rlwe.Plaintext, n)
	for j := 0; j < n; j++ {
		giantShift := (j / g) * g
		shifted := rotateLeftUint64(diagExt[j], -giantShift)
		pt, err := encodeBatchedPlaintextAtMaxLevel(params, encoder, shifted)
		if err != nil {
			return nil, fmt.Errorf("failed to pre-encode SlotToCoeff diagonal %d: %w", j, err)
		}
		shiftedPT[j] = pt
	}
	return &PreprocessedBSGSPlaintexts{G: g, B: b, ShiftedPT: shiftedPT}, nil
}

func HomomorphicSparseLinearTransformBSGSPrecomp(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ct *rlwe.Ciphertext,
	pre *PreprocessedBSGSPlaintexts,
) (*rlwe.Ciphertext, BSGSStats, error) {
	var stats BSGSStats
	if pre == nil || len(pre.ShiftedPT) == 0 {
		return nil, stats, errors.New("nil or empty preprocessed SlotToCoeff diagonals")
	}
	n := len(pre.ShiftedPT)
	stats.G = pre.G
	stats.B = pre.B

	baby := make([]*rlwe.Ciphertext, pre.G)
	baby[0] = ct
	for k := 1; k < pre.G; k++ {
		rot, err := eval.RotateColumnsNew(ct, k)
		if err != nil {
			return nil, stats, fmt.Errorf("baby rotation by %d failed: %w", k, err)
		}
		baby[k] = rot
		stats.Rotations++
		stats.BabyRotations++
	}

	var acc *rlwe.Ciphertext
	for i := 0; i < pre.B; i++ {
		giantShift := i * pre.G
		var block *rlwe.Ciphertext
		for k := 0; k < pre.G; k++ {
			j := giantShift + k
			if j >= n {
				break
			}
			term, err := mulOperandRescale(eval, baby[k], pre.ShiftedPT[j])
			if err != nil {
				return nil, stats, fmt.Errorf("plaintext-ciphertext multiplication for diagonal %d failed: %w", j, err)
			}
			stats.PlainCipherMults++
			if block == nil {
				block = term
			} else {
				block, err = eval.AddNew(block, term)
				if err != nil {
					return nil, stats, fmt.Errorf("block add for diagonal %d failed: %w", j, err)
				}
				stats.Additions++
			}
		}
		if block == nil {
			continue
		}
		if giantShift != 0 {
			rot, err := eval.RotateColumnsNew(block, giantShift)
			if err != nil {
				return nil, stats, fmt.Errorf("giant rotation by %d failed: %w", giantShift, err)
			}
			block = rot
			stats.Rotations++
			stats.GiantRotations++
		}
		if acc == nil {
			acc = block
		} else {
			var err error
			acc, err = eval.AddNew(acc, block)
			if err != nil {
				return nil, stats, fmt.Errorf("accumulator add for giant block %d failed: %w", i, err)
			}
			stats.Additions++
		}
	}
	if acc == nil {
		return nil, stats, errors.New("accumulator is nil")
	}
	return acc, stats, nil
}

type PreprocessedMonomial struct {
	S             int
	Ell           int
	ConstVec      []uint64
	FirstMaskPT   *rlwe.Plaintext
	FirstConstVec []uint64
	CMaskPT       []*rlwe.Plaintext
	DConstVec     [][]uint64
}

func preprocessMonomialPlaintexts(params bfv.Parameters, encoder *bfv.Encoder, n int, coeffs [][]uint64) (*PreprocessedMonomial, error) {
	if len(coeffs) == 0 || len(coeffs[0]) == 0 {
		return nil, errors.New("coeffs is empty")
	}
	s := len(coeffs[0])
	r, ell, err := validateMonomialInputs(params, n, s, coeffs)
	if err != nil {
		return nil, err
	}
	slots := params.MaxSlots()
	T := params.PlaintextModulus()
	pre := &PreprocessedMonomial{S: s, Ell: ell}
	if s == 1 {
		pre.ConstVec = buildCoeffExtVector(coeffs, n, r, s, slots, T)
		return pre, nil
	}
	fVec := buildCoeffExtVector(coeffs, n, r, s, slots, T)
	cExt, dExt := buildBitMasks(n, r, s, slots)
	firstMask := hadamard(cExt[0], fVec, T)
	pre.FirstMaskPT, err = encodeBatchedPlaintextAtMaxLevel(params, encoder, firstMask)
	if err != nil {
		return nil, fmt.Errorf("failed to pre-encode first monomial mask: %w", err)
	}
	pre.FirstConstVec = hadamard(dExt[0], fVec, T)
	pre.CMaskPT = make([]*rlwe.Plaintext, ell)
	pre.DConstVec = make([][]uint64, ell)
	for i := 1; i < ell; i++ {
		pre.CMaskPT[i], err = encodeBatchedPlaintextAtMaxLevel(params, encoder, cExt[i])
		if err != nil {
			return nil, fmt.Errorf("failed to pre-encode monomial mask bit %d: %w", i, err)
		}
		pre.DConstVec[i] = append([]uint64(nil), dExt[i]...)
	}
	return pre, nil
}

func MonomialGenExtraPrecomp(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ct *rlwe.Ciphertext,
	n int,
	pre *PreprocessedMonomial,
	wantExtra bool,
) (*rlwe.Ciphertext, *rlwe.Ciphertext, MonomialTiming, error) {
	var timing MonomialTiming
	totalStart := time.Now()
	if pre == nil {
		return nil, nil, timing, errors.New("nil monomial precomputation")
	}
	s := pre.S
	_, ell, err := validateMonomialInputs(params, n, s, replicateSinglePolynomial(make([]uint64, s), n))
	_ = ell
	if err != nil {
	}
	if s == 1 {
		zero, err := zeroCiphertextFrom(eval, ct)
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed to build zero ciphertext: %w", err)
		}
		out, err := eval.AddNew(zero, pre.ConstVec)
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed to add constant vector: %w", err)
		}
		timing.Total = time.Since(totalStart)
		progressf("run complete in %v", timing.Total)
		return out, nil, timing, nil
	}
	powStart := time.Now()
	xPow := make([]*rlwe.Ciphertext, pre.Ell)
	xPow[0] = ct.CopyNew()
	for i := 1; i < pre.Ell; i++ {
		xPow[i], err = mulCtRelinRescale(eval, xPow[i-1], xPow[i-1])
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed to compute x^(2^%d): %w", i, err)
		}
	}
	timing.BuildPowers = time.Since(powStart)
	var extra *rlwe.Ciphertext
	if wantExtra {
		extra = xPow[pre.Ell-1].CopyNew()
	}
	yStart := time.Now()
	tmp, err := mulOperandRescale(eval, xPow[0], pre.FirstMaskPT)
	if err != nil {
		return nil, nil, timing, fmt.Errorf("failed first masked multiply: %w", err)
	}
	acc, err := eval.AddNew(tmp, pre.FirstConstVec)
	if err != nil {
		return nil, nil, timing, fmt.Errorf("failed first masked add: %w", err)
	}
	for i := 1; i < pre.Ell; i++ {
		tmp, err = mulOperandRescale(eval, xPow[i], pre.CMaskPT[i])
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed masked multiply at bit %d: %w", i, err)
		}
		factor, err := eval.AddNew(tmp, pre.DConstVec[i])
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed masked add at bit %d: %w", i, err)
		}
		acc, err = mulCtRelinRescale(eval, acc, factor)
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed ciphertext multiply at bit %d: %w", i, err)
		}
	}
	timing.BuildY = time.Since(yStart)
	timing.Total = time.Since(totalStart)
	return acc, extra, timing, nil
}

type PreprocessedParallelLT2 struct {
	Ell           int
	R             int
	G             int
	B             int
	ShiftedMaskPT []*rlwe.Plaintext
}

func preprocessParallelLT2(params bfv.Parameters, encoder *bfv.Encoder, A, B [][][]uint64, n, ell, r int) (*PreprocessedParallelLT2, error) {
	g, b, err := choosePolyLTBSGS(ell)
	if err != nil {
		return nil, err
	}
	pre := &PreprocessedParallelLT2{Ell: ell, R: r, G: g, B: b, ShiftedMaskPT: make([]*rlwe.Plaintext, ell)}
	for j := 0; j < ell; j++ {
		giantShift := (j / g) * g * n
		mask := buildMaskVector(A, B, j, n, ell, r)
		shiftedMask := rotateWithinHalves(mask, -giantShift)
		pt, err := encodeBatchedPlaintextAtMaxLevel(params, encoder, shiftedMask)
		if err != nil {
			return nil, fmt.Errorf("failed to pre-encode ParallelLT mask %d: %w", j, err)
		}
		pre.ShiftedMaskPT[j] = pt
	}
	return pre, nil
}

func parallelLT2FirstStageBSGSHoistedPrecomp(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ctIn *rlwe.Ciphertext,
	pre *PreprocessedParallelLT2,
	n, ell, r int,
	tm *AlgoTimings,
) (*rlwe.Ciphertext, error) {
	levelQ := ctIn.Level()
	levelP := params.MaxLevelP()
	startDec := time.Now()
	decomp := allocDecompBuffer(params, levelQ, levelP)
	eval.DecomposeNTT(levelQ, levelP, levelP+1, ctIn.Value[1], ctIn.IsNTT, decomp)
	tm.FirstStageDecompose += time.Since(startDec)
	startEval := time.Now()
	baby := make([]*rlwe.Ciphertext, pre.G)
	baby[0] = ctIn
	for k := 1; k < pre.G; k++ {
		rot := bfv.NewCiphertext(params, 1, levelQ)
		galEl := params.GaloisElementForColRotation(k * n)
		stRot := time.Now()
		if err := eval.AutomorphismHoisted(levelQ, ctIn, decomp, galEl, rot); err != nil {
			return nil, fmt.Errorf("alg2 bsgs baby rotation k=%d failed: %w", k, err)
		}
		tm.BabyRotations += time.Since(stRot)
		baby[k] = rot
	}
	var acc *rlwe.Ciphertext
	for i := 0; i < pre.B; i++ {
		giantShift := i * pre.G * n
		var block *rlwe.Ciphertext
		for k := 0; k < pre.G; k++ {
			j := i*pre.G + k
			if j >= ell {
				break
			}
			stMul := time.Now()
			term, err := eval.MulNew(baby[k], pre.ShiftedMaskPT[j])
			if err != nil {
				return nil, fmt.Errorf("alg2 bsgs term multiply i=%d k=%d j=%d failed: %w", i, k, j, err)
			}
			tm.PlaintextCipherMul += time.Since(stMul)
			if block == nil {
				block = term
			} else {
				if err := eval.Add(block, term, block); err != nil {
					return nil, fmt.Errorf("alg2 bsgs block add i=%d k=%d j=%d failed: %w", i, k, j, err)
				}
			}
		}
		if block == nil {
			continue
		}
		if giantShift == 0 {
			if acc == nil {
				acc = block
			} else if err := eval.Add(acc, block, acc); err != nil {
				return nil, fmt.Errorf("alg2 bsgs acc add i=%d failed: %w", i, err)
			}
		} else {
			rot := bfv.NewCiphertext(params, 1, block.Level())
			galEl := params.GaloisElementForColRotation(giantShift)
			stRot := time.Now()
			if err := eval.Automorphism(block, galEl, rot); err != nil {
				return nil, fmt.Errorf("alg2 bsgs giant rotation i=%d failed: %w", i, err)
			}
			tm.GiantRotations += time.Since(stRot)
			if acc == nil {
				acc = rot
			} else if err := eval.Add(acc, rot, acc); err != nil {
				return nil, fmt.Errorf("alg2 bsgs giant add i=%d failed: %w", i, err)
			}
		}
	}
	if acc == nil {
		return nil, errors.New("alg2 bsgs precomp accumulator is nil")
	}
	tm.FirstStageEval += time.Since(startEval)
	return acc, nil
}

func parallelLT2BSGSHoistedPrecomp(params bfv.Parameters, eval *bfv.Evaluator, ctIn *rlwe.Ciphertext, pre *PreprocessedParallelLT2, n, ell, r int) (*rlwe.Ciphertext, AlgoTimings, error) {
	var tm AlgoTimings
	start := time.Now()
	y, err := parallelLT2FirstStageBSGSHoistedPrecomp(params, eval, ctIn, pre, n, ell, r, &tm)
	if err != nil {
		return nil, tm, err
	}
	if err := parallelLT2SumColumns(params, eval, y, n, ell, r, &tm); err != nil {
		return nil, tm, err
	}
	tm.Total = time.Since(start)
	return y, tm, nil
}

type PreprocessedParallelLT3 struct {
	Short bool
	Pre1  *PreprocessedParallelLT2
	Pre2  *PreprocessedParallelLT2
}

func preprocessParallelLT3(params bfv.Parameters, encoder *bfv.Encoder, U [][][]uint64, n, ell, r int) (*PreprocessedParallelLT3, error) {
	pre := &PreprocessedParallelLT3{}
	if ell < r {
		A, B := splitUHorizontal(U, ell, r)
		p1, err := preprocessParallelLT2(params, encoder, A, B, n, ell, r)
		if err != nil {
			return nil, err
		}
		pre.Short = true
		pre.Pre1 = p1
		return pre, nil
	}
	A, B, C, D := splitUBlocks(U, r)
	p1, err := preprocessParallelLT2(params, encoder, A, D, n, r/2, r)
	if err != nil {
		return nil, err
	}
	p2, err := preprocessParallelLT2(params, encoder, B, C, n, r/2, r)
	if err != nil {
		return nil, err
	}
	pre.Pre1 = p1
	pre.Pre2 = p2
	return pre, nil
}

func preprocessParallelLT3Views(params bfv.Parameters, encoder *bfv.Encoder, U [][][]uint64, n, ell, r int) (*PreprocessedParallelLT3, error) {
	pre := &PreprocessedParallelLT3{}
	if ell < r {
		A, B := splitUHorizontalViews(U, ell, r)
		p1, err := preprocessParallelLT2(params, encoder, A, B, n, ell, r)
		if err != nil {
			return nil, err
		}
		pre.Short = true
		pre.Pre1 = p1
		return pre, nil
	}
	A, B, C, D := splitUBlocksViews(U, r)
	p1, err := preprocessParallelLT2(params, encoder, A, D, n, r/2, r)
	if err != nil {
		return nil, err
	}
	p2, err := preprocessParallelLT2(params, encoder, B, C, n, r/2, r)
	if err != nil {
		return nil, err
	}
	pre.Pre1 = p1
	pre.Pre2 = p2
	return pre, nil
}

func parallelLT3BSGSHoistedPrecomp(params bfv.Parameters, eval *bfv.Evaluator, ctIn *rlwe.Ciphertext, pre *PreprocessedParallelLT3, n, ell, r int) (*rlwe.Ciphertext, AlgoTimings, error) {
	var tm AlgoTimings
	start := time.Now()
	if pre.Short {
		y, t2, err := parallelLT2BSGSHoistedPrecomp(params, eval, ctIn, pre.Pre1, n, ell, r)
		if err != nil {
			return nil, tm, err
		}
		tm.AddStage(t2)
		startPost := time.Now()
		tauY, err := rowSwapCipher(params, eval, y)
		if err != nil {
			return nil, tm, fmt.Errorf("alg3 row swap failed: %w", err)
		}
		if err := eval.Add(y, tauY, y); err != nil {
			return nil, tm, fmt.Errorf("alg3 add y+tau(y) failed: %w", err)
		}
		tm.PostProcess += time.Since(startPost)
		tm.Total = time.Since(start)
		return y, tm, nil
	}
	y, t2a, err := parallelLT2BSGSHoistedPrecomp(params, eval, ctIn, pre.Pre1, n, r/2, r)
	if err != nil {
		return nil, tm, err
	}
	tm.AddStage(t2a)
	startPost := time.Now()
	ctTauM, err := rowSwapCipher(params, eval, ctIn)
	if err != nil {
		return nil, tm, fmt.Errorf("alg3 row swap on input failed: %w", err)
	}
	tm.PostProcess += time.Since(startPost)
	yPrime, t2b, err := parallelLT2BSGSHoistedPrecomp(params, eval, ctTauM, pre.Pre2, n, r/2, r)
	if err != nil {
		return nil, tm, err
	}
	tm.AddStage(t2b)
	startPost = time.Now()
	if err := eval.Add(y, yPrime, y); err != nil {
		return nil, tm, fmt.Errorf("alg3 add y+y' failed: %w", err)
	}
	tm.PostProcess += time.Since(startPost)
	tm.Total = time.Since(start)
	return y, tm, nil
}

type PreprocessedPolyEval struct {
	D        int
	M        int
	LeadPT   *rlwe.Plaintext
	LowerMon *PreprocessedMonomial
	OnesRMon *PreprocessedMonomial
	OnesSMon *PreprocessedMonomial
	LT       *PreprocessedParallelLT3
}

func preprocessPolyEvalPlaintexts(params bfv.Parameters, encoder *bfv.Encoder, m, d int, coeffsLower [][]uint64, leadCoeffs []uint64) (*PreprocessedPolyEval, error) {
	pre := &PreprocessedPolyEval{D: d, M: m}
	leadVec, err := sparsePackLeadingCoeffs(leadCoeffs, params.MaxSlots())
	if err != nil {
		return nil, err
	}
	pre.LeadPT, err = encodeBatchedPlaintextAtMaxLevel(params, encoder, leadVec)
	if err != nil {
		return nil, fmt.Errorf("failed to pre-encode leading x^d plaintext: %w", err)
	}
	r := params.MaxSlots() / m
	if m == 1 && d <= r {
		pre.LowerMon, err = preprocessMonomialPlaintexts(params, encoder, m, coeffsLower)
		return pre, err
	}
	if d <= r || d > r*r || d%r != 0 {
		return nil, fmt.Errorf("Algorithm 5 requires r < d <= r^2 and r|d unless m=1 uses the direct path, got d=%d, r=%d, m=%d", d, r, m)
	}
	pre.OnesRMon, err = preprocessMonomialPlaintexts(params, encoder, m, buildAllOnesCoeffs(m, r))
	if err != nil {
		return nil, err
	}
	s := d / r
	pre.OnesSMon, err = preprocessMonomialPlaintexts(params, encoder, m, buildAllOnesCoeffs(m, s))
	if err != nil {
		return nil, err
	}
	U := buildPatersonStockmeyerMatrices(coeffsLower, r)
	pre.LT, err = preprocessParallelLT3(params, encoder, U, m, s, r)
	return pre, err
}

func mulPlainRescale(eval *bfv.Evaluator, ct *rlwe.Ciphertext, plain []uint64) (*rlwe.Ciphertext, error) {
	out, err := eval.MulNew(ct, plain)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(out, out); err != nil {
		return nil, err
	}
	return out, nil
}

func HomomorphicSparseLinearTransformBSGS(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ct *rlwe.Ciphertext,
	diagExt [][]uint64,
) (*rlwe.Ciphertext, BSGSStats, error) {
	var stats BSGSStats
	n := len(diagExt)
	if n == 0 {
		return nil, stats, errors.New("no diagonals provided")
	}
	N := len(diagExt[0])
	for j := range diagExt {
		if len(diagExt[j]) != N {
			return nil, stats, fmt.Errorf("diagonal %d has inconsistent length", j)
		}
	}
	if N != params.MaxSlots() {
		return nil, stats, fmt.Errorf("diagonal extension length %d does not match MaxSlots=%d", N, params.MaxSlots())
	}

	g := int(math.Ceil(math.Sqrt(float64(n))))
	b := (n + g - 1) / g
	stats.G = g
	stats.B = b

	baby := make([]*rlwe.Ciphertext, g)
	baby[0] = ct
	for k := 1; k < g; k++ {
		rot, err := eval.RotateColumnsNew(ct, k)
		if err != nil {
			return nil, stats, fmt.Errorf("baby rotation by %d failed: %w", k, err)
		}
		baby[k] = rot
		stats.Rotations++
		stats.BabyRotations++
	}

	var acc *rlwe.Ciphertext
	for i := 0; i < b; i++ {
		giantShift := i * g
		var block *rlwe.Ciphertext

		for k := 0; k < g; k++ {
			j := giantShift + k
			if j >= n {
				break
			}
			shiftedDiag := rotateLeftUint64(diagExt[j], -giantShift)
			term, err := mulPlainRescale(eval, baby[k], shiftedDiag)
			if err != nil {
				return nil, stats, fmt.Errorf("plaintext-ciphertext multiplication for diagonal %d failed: %w", j, err)
			}
			stats.PlainCipherMults++
			if block == nil {
				block = term
			} else {
				block, err = eval.AddNew(block, term)
				if err != nil {
					return nil, stats, fmt.Errorf("block add for diagonal %d failed: %w", j, err)
				}
				stats.Additions++
			}
		}

		if block == nil {
			continue
		}

		if giantShift != 0 {
			rot, err := eval.RotateColumnsNew(block, giantShift)
			if err != nil {
				return nil, stats, fmt.Errorf("giant rotation by %d failed: %w", giantShift, err)
			}
			block = rot
			stats.Rotations++
			stats.GiantRotations++
		}

		if acc == nil {
			acc = block
		} else {
			var err error
			acc, err = eval.AddNew(acc, block)
			if err != nil {
				return nil, stats, fmt.Errorf("accumulator add for giant block %d failed: %w", i, err)
			}
			stats.Additions++
		}
	}

	if acc == nil {
		return nil, stats, errors.New("accumulator is nil")
	}
	return acc, stats, nil
}

func equalInt64Slices(a, b []int64) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func equalUint64Slices(a, b []uint64) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

type LWECiphertext struct {
	A []uint64
	B uint64
}

type ExtractionTiming struct {
	TargetSecretBuild time.Duration
	EvaluationKeyGen  time.Duration
	KeySwitch         time.Duration
	GammaComp         time.Duration
	ExternalModSwitch time.Duration
	SampleExtract     time.Duration
	LWECheck          time.Duration
}

func buildTargetBFVSecretKey(params bfv.Parameters, sSmall []int64) *rlwe.SecretKey {
	if len(sSmall) > params.N() {
		panic(fmt.Sprintf("len(sSmall)=%d > N=%d", len(sSmall), params.N()))
	}

	coeffs := make([]*big.Int, params.N())
	for i := range coeffs {
		coeffs[i] = new(big.Int)
	}
	for i, v := range sSmall {
		coeffs[i].SetInt64(v)
	}

	sk := rlwe.NewSecretKey(params)
	ringQ := params.RingQ().AtLevel(sk.LevelQ())
	ringQP := params.RingQP().AtLevel(sk.LevelQ(), sk.LevelP())

	ringQ.SetCoefficientsBigint(coeffs, sk.Value.Q)
	if sk.LevelP() > -1 {
		ringQP.ExtendBasisSmallNormAndCenter(sk.Value.Q, sk.LevelP(), sk.Value.Q, sk.Value.P)
	}
	ringQP.NTT(sk.Value, sk.Value)
	ringQP.MForm(sk.Value, sk.Value)

	return sk
}

func polyToBigintCentered(r *ring.Ring, p ring.Poly, isNTT, isMontgomery bool) []*big.Int {
	tmp := *p.CopyNew()
	if isMontgomery {
		r.IMForm(tmp, tmp)
	}
	if isNTT {
		r.INTT(tmp, tmp)
	}

	coeffs := make([]*big.Int, r.N())
	for i := range coeffs {
		coeffs[i] = new(big.Int)
	}
	r.PolyToBigintCentered(tmp, 1, coeffs)
	return coeffs
}

func modPositiveBig(x, mod *big.Int) *big.Int {
	y := new(big.Int).Mod(x, mod)
	if y.Sign() < 0 {
		y.Add(y, mod)
	}
	return y
}

func roundModSwitchBig(x, qSrc *big.Int, qDst uint64) uint64 {
	num := new(big.Int).Mul(modPositiveBig(x, qSrc), new(big.Int).SetUint64(qDst))
	num.Add(num, new(big.Int).Rsh(new(big.Int).Set(qSrc), 1))
	num.Quo(num, qSrc)
	num.Mod(num, new(big.Int).SetUint64(qDst))
	return num.Uint64()
}

func sampleExtractAt(aPoly, bPoly []uint64, idx, lweDim int, q uint64) LWECiphertext {
	N := len(aPoly)
	if len(bPoly) != N {
		panic(fmt.Sprintf("sampleExtractAt: len(aPoly)=%d != len(bPoly)=%d", N, len(bPoly)))
	}
	if idx < 0 || idx >= N {
		panic(fmt.Sprintf("sampleExtractAt: idx=%d out of range [0,%d)", idx, N))
	}
	if lweDim <= 0 || lweDim > N {
		panic(fmt.Sprintf("sampleExtractAt: invalid lweDim=%d for N=%d", lweDim, N))
	}

	a := make([]uint64, lweDim)
	for j := 0; j < lweDim; j++ {
		if j <= idx {
			a[j] = aPoly[idx-j]
		} else {
			a[j] = negateMod(aPoly[N+idx-j], q)
		}
	}
	return LWECiphertext{A: a, B: bPoly[idx]}
}

func sampleExtractSelected(aPoly, bPoly []uint64, positions []int, lweDim int, q uint64) []LWECiphertext {
	out := make([]LWECiphertext, len(positions))
	for i, pos := range positions {
		out[i] = sampleExtractAt(aPoly, bPoly, pos, lweDim, q)
	}
	return out
}

func negateMod(x, q uint64) uint64 {
	x %= q
	if x == 0 {
		return 0
	}
	return q - x
}

func mulSignedMod(a uint64, s int64, q uint64) uint64 {
	if s == 0 {
		return 0
	}
	mag := uint64(abs64(s))
	prod := (a * mag) % q
	if s > 0 {
		return prod
	}
	return negateMod(prod, q)
}

func rawDecryptLWE(ct LWECiphertext, s []int64, q uint64) uint64 {
	if len(ct.A) != len(s) {
		panic(fmt.Sprintf("rawDecryptLWE: len(a)=%d != len(s)=%d", len(ct.A), len(s)))
	}
	acc := ct.B % q
	for i, ai := range ct.A {
		prod := mulSignedMod(ai, s[i], q)
		if acc >= prod {
			acc -= prod
		} else {
			acc += q - prod
		}
	}
	return acc % q
}

func centeredDiff(have, want, q uint64) int64 {
	var d uint64
	if have >= want {
		d = have - want
	} else {
		d = have + q - want
	}
	if d <= q/2 {
		return int64(d)
	}
	return int64(d) - int64(q)
}

func negQInvModT(Q *big.Int, t uint64) uint64 {
	tBig := new(big.Int).SetUint64(t)
	qModT := new(big.Int).Mod(new(big.Int).Set(Q), tBig)
	inv := new(big.Int).ModInverse(qModT, tBig)
	if inv == nil {
		panic("Q mod t is not invertible modulo t")
	}
	inv.Neg(inv)
	inv.Mod(inv, tBig)
	return inv.Uint64()
}

func modInverseU64(x, mod uint64) uint64 {
	modBig := new(big.Int).SetUint64(mod)
	inv := new(big.Int).ModInverse(new(big.Int).SetUint64(x), modBig)
	if inv == nil {
		panic(fmt.Sprintf("%d is not invertible modulo %d", x, mod))
	}
	return inv.Uint64()
}

func randomTernary(n int, seed int64) []int64 {
	rng := rand.New(rand.NewSource(seed))
	out := make([]int64, n)
	for i := range out {
		switch rng.Intn(3) {
		case 0:
			out[i] = -1
		case 1:
			out[i] = 0
		default:
			out[i] = 1
		}
	}
	return out
}

func validateTernary(v []int64) error {
	for i, x := range v {
		if x != -1 && x != 0 && x != 1 {
			return fmt.Errorf("secret[%d]=%d is not in {-1,0,1}", i, x)
		}
	}
	return nil
}

func uintAtPositions(v []uint64, positions []int) []uint64 {
	out := make([]uint64, len(positions))
	for i, pos := range positions {
		out[i] = v[pos]
	}
	return out
}

func avgAbs(v []int64) float64 {
	if len(v) == 0 {
		return 0
	}
	var s float64
	for _, x := range v {
		if x < 0 {
			s += float64(-x)
		} else {
			s += float64(x)
		}
	}
	return s / float64(len(v))
}

func meanInt64(v []int64) float64 {
	if len(v) == 0 {
		return 0
	}
	var s float64
	for _, x := range v {
		s += float64(x)
	}
	return s / float64(len(v))
}

func stdDevInt64(v []int64) float64 {
	if len(v) == 0 {
		return 0
	}
	mu := meanInt64(v)
	var ss float64
	for _, x := range v {
		d := float64(x) - mu
		ss += d * d
	}
	return math.Sqrt(ss / float64(len(v)))
}

func abs64(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}

// Poly-evaluation timing helpers copied from the user's BFV evaluator program.
type MonomialTiming struct {
	BuildPowers time.Duration
	BuildY      time.Duration
	Total       time.Duration
}

type AlgoTimings struct {
	FirstStageDecompose time.Duration
	FirstStageEval      time.Duration
	SecondStageEval     time.Duration
	PostProcess         time.Duration
	BabyRotations       time.Duration
	GiantRotations      time.Duration
	PlaintextCipherMul  time.Duration
	Total               time.Duration
}

func (t *AlgoTimings) AddStage(o AlgoTimings) {
	t.FirstStageDecompose += o.FirstStageDecompose
	t.FirstStageEval += o.FirstStageEval
	t.SecondStageEval += o.SecondStageEval
	t.PostProcess += o.PostProcess
	t.BabyRotations += o.BabyRotations
	t.GiantRotations += o.GiantRotations
	t.PlaintextCipherMul += o.PlaintextCipherMul
	t.Total += o.Total
}

type Alg5Timing struct {
	MonomialR    MonomialTiming
	SquareXRHalf time.Duration
	ModDrop      time.Duration
	ParallelLT   AlgoTimings
	MonomialS    MonomialTiming
	PointwiseMul time.Duration
	FinalSum     time.Duration
	Total        time.Duration
}

type PolyEvalTiming struct {
	Algorithm string
	Total     time.Duration
}

type PolyEvalAlg string

const (
	PolyEvalAlg5 PolyEvalAlg = "alg5"
)

type PolyNoiseTraceEntry struct {
	Name              string
	Level             int
	CurrentLogQBits   int
	ScaleModT         uint64
	NonZeroCoeffNoise int
	MaxCoeffNoiseAbs  string
	CoeffNoisePreview []string
	TotalCoefficients int
}

type PolyNoiseTracer struct {
	Enabled bool
	Params  bfv.Parameters
	Encoder *bfv.Encoder
	Dec     *rlwe.Decryptor
	Preview int
	Full    bool
	Entries []PolyNoiseTraceEntry
}

var globalPolyNoiseTracer *PolyNoiseTracer
var globalPolyNoiseBase []uint64
var globalPolyNoiseCoeffLower [][]uint64
var globalPolyNoiseLeadCoeffs []uint64

func setPolyNoiseTraceContext(tr *PolyNoiseTracer, base []uint64, coeffsLower [][]uint64, leadCoeffs []uint64) {
	// Do not retain or copy per-run LUT data unless exact polynomial-noise tracing is enabled.
	// For large LUTs this avoids keeping another copy of multi-megabyte or gigabyte slices
	// alive until the end of the run.
	if tr == nil || !tr.Enabled {
		clearPolyNoiseTraceContext()
		return
	}

	globalPolyNoiseTracer = tr
	if base == nil {
		globalPolyNoiseBase = nil
	} else {
		globalPolyNoiseBase = append([]uint64(nil), base...)
	}
	if coeffsLower == nil {
		globalPolyNoiseCoeffLower = nil
	} else {
		globalPolyNoiseCoeffLower = make([][]uint64, len(coeffsLower))
		for i := range coeffsLower {
			globalPolyNoiseCoeffLower[i] = append([]uint64(nil), coeffsLower[i]...)
		}
	}
	if leadCoeffs == nil {
		globalPolyNoiseLeadCoeffs = nil
	} else {
		globalPolyNoiseLeadCoeffs = append([]uint64(nil), leadCoeffs...)
	}
}

func clearPolyNoiseTraceContext() {
	globalPolyNoiseTracer = nil
	globalPolyNoiseBase = nil
	globalPolyNoiseCoeffLower = nil
	globalPolyNoiseLeadCoeffs = nil
}

func makePolyNoiseTracer(enabled bool, params bfv.Parameters, encoder *bfv.Encoder, dec *rlwe.Decryptor, preview int, full bool) *PolyNoiseTracer {
	if preview <= 0 {
		preview = 8
	}
	return &PolyNoiseTracer{Enabled: enabled, Params: params, Encoder: encoder, Dec: dec, Preview: preview, Full: full}
}

func centeredDiffSlice(have, want []uint64, mod uint64) ([]int64, int, int64, float64) {
	if len(have) != len(want) {
		panic(fmt.Sprintf("centeredDiffSlice: len(have)=%d != len(want)=%d", len(have), len(want)))
	}
	diffs := make([]int64, len(have))
	exact := 0
	var maxAbs int64
	var sumAbs float64
	for i := range have {
		d := centeredDiff(have[i], want[i], mod)
		diffs[i] = d
		if d == 0 {
			exact++
		}
		ad := abs64(d)
		if ad > maxAbs {
			maxAbs = ad
		}
		sumAbs += float64(ad)
	}
	meanAbs := 0.0
	if len(diffs) > 0 {
		meanAbs = sumAbs / float64(len(diffs))
	}
	return diffs, exact, maxAbs, meanAbs
}

func (tr *PolyNoiseTracer) Probe(name string, ct *rlwe.Ciphertext, expectedSlots []uint64) error {
	if tr == nil || !tr.Enabled {
		return nil
	}
	ptGot := tr.Dec.DecryptNew(ct)
	ptRef := bfv.NewPlaintext(tr.Params, ct.Level())
	ptRef.Scale = ct.Scale
	if err := tr.Encoder.Encode(expectedSlots, ptRef); err != nil {
		return fmt.Errorf("failed to encode expected plaintext for poly-noise trace %q: %w", name, err)
	}
	ringQ := tr.Params.RingQ().AtLevel(ct.Level())
	bigQ := ringQ.Modulus()
	gotBig := polyToBigintCentered(ringQ, ptGot.Value, ptGot.IsNTT, ptGot.IsMontgomery)
	refBig := polyToBigintCentered(ringQ, ptRef.Value, ptRef.IsNTT, ptRef.IsMontgomery)

	previewN := tr.Preview
	if tr.Full || previewN > len(gotBig) {
		previewN = len(gotBig)
	}
	preview := make([]string, previewN)
	maxAbs := big.NewInt(0)
	nonZero := 0
	for i := range gotBig {
		diff := centeredModBig(new(big.Int).Sub(gotBig[i], refBig[i]), bigQ)
		if diff.Sign() != 0 {
			nonZero++
		}
		absDiff := new(big.Int).Abs(new(big.Int).Set(diff))
		if absDiff.Cmp(maxAbs) > 0 {
			maxAbs.Set(absDiff)
		}
		if i < previewN {
			preview[i] = diff.String()
		}
	}
	entry := PolyNoiseTraceEntry{
		Name:              name,
		Level:             ct.Level(),
		CurrentLogQBits:   bigQ.BitLen(),
		ScaleModT:         ct.Scale.Uint64() % tr.Params.PlaintextModulus(),
		NonZeroCoeffNoise: nonZero,
		MaxCoeffNoiseAbs:  maxAbs.String(),
		CoeffNoisePreview: preview,
		TotalCoefficients: len(gotBig),
	}
	tr.Entries = append(tr.Entries, entry)
	return nil
}

func (tr *PolyNoiseTracer) Print() {
	if tr == nil || !tr.Enabled || len(tr.Entries) == 0 {
		return
	}
	fmt.Println("---------- Exact decrypted RLWE coefficient-noise inside LUT polynomial evaluation ----------")
	for _, e := range tr.Entries {
		fmt.Printf("%s:\n", e.Name)
		fmt.Printf("  level                    : %d\n", e.Level)
		fmt.Printf("  current logQ bits        : %d\n", e.CurrentLogQBits)
		fmt.Printf("  scale mod T              : %d\n", e.ScaleModT)
		fmt.Printf("  nonzero coeff noise      : %d / %d\n", e.NonZeroCoeffNoise, e.TotalCoefficients)
		fmt.Printf("  max |coeff noise|        : %s\n", e.MaxCoeffNoiseAbs)
		fmt.Printf("  coeff noise preview      : %v\n", e.CoeffNoisePreview)
	}
	fmt.Println("--------------------------------------------------------------------------------------------")
	fmt.Println()
}

func maybeTracePolyNoise(name string, ct *rlwe.Ciphertext, expectedSlots []uint64) error {
	if globalPolyNoiseTracer == nil || !globalPolyNoiseTracer.Enabled {
		return nil
	}
	return globalPolyNoiseTracer.Probe(name, ct, expectedSlots)
}

func powVectorMod(base []uint64, exp int, mod uint64) []uint64 {
	out := make([]uint64, len(base))
	for i, x := range base {
		out[i] = powMod(x, uint64(exp), mod)
	}
	return out
}

func monomialGenReferenceSlots(base []uint64, coeffs [][]uint64, repeatFactor int, mod uint64) []uint64 {
	m := len(base)
	s := len(coeffs[0])
	out := make([]uint64, m*repeatFactor)
	for row := 0; row < repeatFactor; row++ {
		deg := row % s
		powRow := 1
		if deg != 0 {
			powRow = deg
		}
		for i := 0; i < m; i++ {
			term := coeffs[i][deg] % mod
			if deg != 0 {
				term = mulMod(term, powMod(base[i], uint64(powRow), mod), mod)
			}
			out[row*m+i] = term
		}
	}
	return out
}

func evaluatePolysPerSlot(base []uint64, coeffs [][]uint64, mod uint64) []uint64 {
	out := make([]uint64, len(base))
	for i := range base {
		out[i] = evalSinglePolyMod(base[i], coeffs[i], mod)
	}
	return out
}

func fullPolyValues(base []uint64, coeffsLower [][]uint64, leadCoeffs []uint64, degree int, mod uint64) []uint64 {
	out := evaluatePolysPerSlot(base, coeffsLower, mod)
	for i := range out {
		out[i] = (out[i] + mulMod(leadCoeffs[i], powMod(base[i], uint64(degree), mod), mod)) % mod
	}
	return out
}

func addSlotsMod(a, b []uint64, mod uint64) []uint64 {
	if len(a) != len(b) {
		panic("addSlotsMod: length mismatch")
	}
	out := make([]uint64, len(a))
	for i := range a {
		out[i] = (a[i] + b[i]) % mod
	}
	return out
}

func pointwiseMulSlots(a, b []uint64, mod uint64) []uint64 {
	if len(a) != len(b) {
		panic("pointwiseMulSlots: length mismatch")
	}
	out := make([]uint64, len(a))
	for i := range a {
		out[i] = mulMod(a[i], b[i], mod)
	}
	return out
}

func expectedAlg5LTSlots(base []uint64, coeffsLower [][]uint64, r int, mod uint64) []uint64 {
	m := len(base)
	s := len(coeffsLower[0]) / r
	out := make([]uint64, m*r)
	for row := 0; row < r; row++ {
		blk := row % s
		for i := 0; i < m; i++ {
			seg := coeffsLower[i][blk*r : (blk+1)*r]
			out[row*m+i] = evalSinglePolyMod(base[i], seg, mod)
		}
	}
	return out
}

func expectedAlg5CollapsedSlots(base []uint64, coeffsLower [][]uint64, r int, mod uint64) []uint64 {
	m := len(base)
	s := len(coeffsLower[0]) / r
	out := make([]uint64, m*r)
	for row := 0; row < r; row++ {
		blk := row % s
		for i := 0; i < m; i++ {
			seg := coeffsLower[i][blk*r : (blk+1)*r]
			blockVal := evalSinglePolyMod(base[i], seg, mod)
			out[row*m+i] = mulMod(blockVal, powMod(base[i], uint64(blk*r), mod), mod)
		}
	}
	return out
}

func buildCoeffExtVector(coeffs [][]uint64, n, r, s, slots int, modulus uint64) []uint64 {
	out := make([]uint64, slots)
	for row := 0; row < r; row++ {
		deg := row % s
		base := row * n
		for i := 0; i < n; i++ {
			out[base+i] = coeffs[i][deg] % modulus
		}
	}
	return out
}

func buildBitMasks(n, r, s, slots int) ([][]uint64, [][]uint64) {
	ell := bits.TrailingZeros(uint(s))
	cExt := make([][]uint64, ell)
	dExt := make([][]uint64, ell)

	for bit := 0; bit < ell; bit++ {
		cMask := make([]uint64, slots)
		dMask := make([]uint64, slots)
		for row := 0; row < r; row++ {
			b := uint64((row >> bit) & 1)
			base := row * n
			for i := 0; i < n; i++ {
				cMask[base+i] = b
				dMask[base+i] = 1 - b
			}
		}
		cExt[bit] = cMask
		dExt[bit] = dMask
	}
	return cExt, dExt
}

func hadamard(a, b []uint64, mod uint64) []uint64 {
	if len(a) != len(b) {
		panic("hadamard: length mismatch")
	}
	out := make([]uint64, len(a))
	for i := range a {
		out[i] = mulMod(a[i], b[i], mod)
	}
	return out
}

func zeroCiphertextFrom(eval *bfv.Evaluator, ct *rlwe.Ciphertext) (*rlwe.Ciphertext, error) {
	return eval.SubNew(ct, ct)
}

func mulCtRelinRescale(eval *bfv.Evaluator, ct0 *rlwe.Ciphertext, op1 rlwe.Operand) (*rlwe.Ciphertext, error) {
	out, err := eval.MulRelinNew(ct0, op1)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(out, out); err != nil {
		return nil, err
	}
	return out, nil
}

func mulCtLazyRelinRescale(eval *bfv.Evaluator, ct0 *rlwe.Ciphertext, op1 rlwe.Operand) (*rlwe.Ciphertext, error) {
	out, err := eval.MulNew(ct0, op1)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(out, out); err != nil {
		return nil, err
	}
	return out, nil
}

func validateMonomialInputs(params bfv.Parameters, n, s int, coeffs [][]uint64) (r int, ell int, err error) {
	if n <= 0 {
		return 0, 0, errors.New("n must be positive")
	}
	if len(coeffs) != n {
		return 0, 0, fmt.Errorf("coeffs has %d rows, want %d", len(coeffs), n)
	}
	if !isPow2(n) {
		return 0, 0, fmt.Errorf("n=%d must be a power of two", n)
	}
	if s <= 0 || !isPow2(s) {
		return 0, 0, fmt.Errorf("s=%d must be a positive power of two", s)
	}
	for i := range coeffs {
		if len(coeffs[i]) != s {
			return 0, 0, fmt.Errorf("coeffs[%d] has length %d, want %d", i, len(coeffs[i]), s)
		}
	}

	slots := params.MaxSlots()
	if slots%n != 0 {
		return 0, 0, fmt.Errorf("n=%d must divide MaxSlots=%d", n, slots)
	}
	r = slots / n
	if !isPow2(r) {
		return 0, 0, fmt.Errorf("r=%d must be a power of two", r)
	}
	if s > r {
		return 0, 0, fmt.Errorf("need s <= r, got s=%d, r=%d", s, r)
	}
	if r%s != 0 {
		return 0, 0, fmt.Errorf("need s | r, got r=%d, s=%d", r, s)
	}
	ell = bits.TrailingZeros(uint(s))
	return r, ell, nil
}

func MonomialGenExtra(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ct *rlwe.Ciphertext,
	n int,
	coeffs [][]uint64,
	wantExtra bool,
) (*rlwe.Ciphertext, *rlwe.Ciphertext, MonomialTiming, error) {
	var timing MonomialTiming
	totalStart := time.Now()

	if len(coeffs) == 0 || len(coeffs[0]) == 0 {
		return nil, nil, timing, errors.New("coeffs is empty")
	}
	s := len(coeffs[0])
	r, ell, err := validateMonomialInputs(params, n, s, coeffs)
	if err != nil {
		return nil, nil, timing, err
	}

	slots := params.MaxSlots()
	T := params.PlaintextModulus()

	if s == 1 {
		fVec := buildCoeffExtVector(coeffs, n, r, s, slots, T)
		zero, err := zeroCiphertextFrom(eval, ct)
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed to build zero ciphertext: %w", err)
		}
		out, err := eval.AddNew(zero, fVec)
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed to add constant vector: %w", err)
		}
		timing.Total = time.Since(totalStart)
		return out, nil, timing, nil
	}

	powStart := time.Now()
	xPow := make([]*rlwe.Ciphertext, ell)
	xPow[0] = ct.CopyNew()
	for i := 1; i < ell; i++ {
		xPow[i], err = mulCtRelinRescale(eval, xPow[i-1], xPow[i-1])
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed to compute x^(2^%d): %w", i, err)
		}
	}
	timing.BuildPowers = time.Since(powStart)

	var extra *rlwe.Ciphertext
	if wantExtra {
		extra = xPow[ell-1].CopyNew()
	}

	yStart := time.Now()
	fVec := buildCoeffExtVector(coeffs, n, r, s, slots, T)
	cExt, dExt := buildBitMasks(n, r, s, slots)

	firstMask := hadamard(cExt[0], fVec, T)
	firstConst := hadamard(dExt[0], fVec, T)

	tmp, err := mulPlainRescale(eval, xPow[0], firstMask)
	if err != nil {
		return nil, nil, timing, fmt.Errorf("failed first masked multiply: %w", err)
	}
	acc, err := eval.AddNew(tmp, firstConst)
	if err != nil {
		return nil, nil, timing, fmt.Errorf("failed first masked add: %w", err)
	}

	for i := 1; i < ell; i++ {
		tmp, err = mulPlainRescale(eval, xPow[i], cExt[i])
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed masked multiply at bit %d: %w", i, err)
		}
		factor, err := eval.AddNew(tmp, dExt[i])
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed masked add at bit %d: %w", i, err)
		}
		acc, err = mulCtRelinRescale(eval, acc, factor)
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed ciphertext multiply at bit %d: %w", i, err)
		}
	}

	timing.BuildY = time.Since(yStart)
	timing.Total = time.Since(totalStart)
	return acc, extra, timing, nil
}

// =================================
// ParallelLT (Algorithms 2 and 3) from file 2, BSGS + hoisting only
// =================================

// rotateWithinHalves implements rho_shift on plaintext vectors.

func rotateWithinHalves(vec []uint64, shift int) []uint64 {
	N := len(vec)
	if N%2 != 0 {
		panic("vector length must be even")
	}
	half := N / 2
	out := make([]uint64, N)

	shift %= half
	if shift < 0 {
		shift += half
	}

	for i := 0; i < half; i++ {
		out[i] = vec[(i+shift)%half]
	}
	for i := 0; i < half; i++ {
		out[half+i] = vec[half+(i+shift)%half]
	}
	return out
}

func buildMaskVector(A, B [][][]uint64, j, n, ell, r int) []uint64 {
	half := r / 2
	mask := make([]uint64, r*n)

	shortDiagonal := func(M [][]uint64, j, ell, cols int) []uint64 {
		diag := make([]uint64, cols)
		for t := 0; t < cols; t++ {
			diag[t] = M[t%ell][(t+j)%cols]
		}
		return diag
	}

	uDiag := make([][]uint64, n)
	vDiag := make([][]uint64, n)
	for i := 0; i < n; i++ {
		uDiag[i] = shortDiagonal(A[i], j, ell, half)
		vDiag[i] = shortDiagonal(B[i], j, ell, half)
	}

	for row := 0; row < half; row++ {
		for i := 0; i < n; i++ {
			mask[row*n+i] = uDiag[i][row]
		}
	}

	base := half * n
	for row := 0; row < half; row++ {
		for i := 0; i < n; i++ {
			mask[base+row*n+i] = vDiag[i][row]
		}
	}

	return mask
}

func splitUHorizontal(U [][][]uint64, ell, r int) (A, B [][][]uint64) {
	n := len(U)
	half := r / 2

	A = make([][][]uint64, n)
	B = make([][][]uint64, n)
	for i := 0; i < n; i++ {
		A[i] = make([][]uint64, ell)
		B[i] = make([][]uint64, ell)
		for row := 0; row < ell; row++ {
			A[i][row] = append([]uint64(nil), U[i][row][:half]...)
			B[i][row] = append([]uint64(nil), U[i][row][half:]...)
		}
	}
	return
}

func splitUBlocks(U [][][]uint64, r int) (A, B, C, D [][][]uint64) {
	n := len(U)
	half := r / 2

	A = make([][][]uint64, n)
	B = make([][][]uint64, n)
	C = make([][][]uint64, n)
	D = make([][][]uint64, n)

	for i := 0; i < n; i++ {
		A[i] = make([][]uint64, half)
		B[i] = make([][]uint64, half)
		C[i] = make([][]uint64, half)
		D[i] = make([][]uint64, half)

		for row := 0; row < half; row++ {
			A[i][row] = append([]uint64(nil), U[i][row][:half]...)
			B[i][row] = append([]uint64(nil), U[i][row][half:]...)
		}
		for row := 0; row < half; row++ {
			C[i][row] = append([]uint64(nil), U[i][half+row][:half]...)
			D[i][row] = append([]uint64(nil), U[i][half+row][half:]...)
		}
	}
	return
}

func allocDecompBuffer(params bfv.Parameters, levelQ, levelP int) []ringqp.Poly {
	size := params.BaseRNSDecompositionVectorSize(levelQ, levelP)
	buf := make([]ringqp.Poly, size)
	for i := range buf {
		buf[i] = ringqp.NewPoly(params.N(), levelQ, levelP)
	}
	return buf
}

func rowSwapCipher(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext) (*rlwe.Ciphertext, error) {
	out := bfv.NewCiphertext(params, 1, ct.Level())
	galEl := params.GaloisElementForRowRotation()
	if err := eval.Automorphism(ct, galEl, out); err != nil {
		return nil, err
	}
	return out, nil
}

func parallelLT2FirstStageBSGSHoisted(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ctIn *rlwe.Ciphertext,
	A, B [][][]uint64,
	n, ell, r int,
	tm *AlgoTimings,
) (*rlwe.Ciphertext, error) {

	levelQ := ctIn.Level()
	levelP := params.MaxLevelP()

	g, b, err := choosePolyLTBSGS(ell)
	if err != nil {
		return nil, err
	}

	startDec := time.Now()
	decomp := allocDecompBuffer(params, levelQ, levelP)
	eval.DecomposeNTT(levelQ, levelP, levelP+1, ctIn.Value[1], ctIn.IsNTT, decomp)
	tm.FirstStageDecompose += time.Since(startDec)

	startEval := time.Now()

	baby := make([]*rlwe.Ciphertext, g)
	baby[0] = ctIn
	for k := 1; k < g; k++ {
		rot := bfv.NewCiphertext(params, 1, levelQ)
		galEl := params.GaloisElementForColRotation(k * n)
		stRot := time.Now()
		if err := eval.AutomorphismHoisted(levelQ, ctIn, decomp, galEl, rot); err != nil {
			return nil, fmt.Errorf("alg2 bsgs baby rotation k=%d failed: %w", k, err)
		}
		tm.BabyRotations += time.Since(stRot)
		baby[k] = rot
	}

	var acc *rlwe.Ciphertext

	for i := 0; i < b; i++ {
		giantShift := i * g * n
		var block *rlwe.Ciphertext

		for k := 0; k < g; k++ {
			j := i*g + k
			if j >= ell {
				break
			}

			mask := buildMaskVector(A, B, j, n, ell, r)
			shiftedMask := rotateWithinHalves(mask, -giantShift)

			stMul := time.Now()
			term, err := eval.MulNew(baby[k], shiftedMask)
			if err != nil {
				return nil, fmt.Errorf("alg2 bsgs term multiply i=%d k=%d j=%d failed: %w", i, k, j, err)
			}
			tm.PlaintextCipherMul += time.Since(stMul)

			if block == nil {
				block = term
			} else {
				if err := eval.Add(block, term, block); err != nil {
					return nil, fmt.Errorf("alg2 bsgs block add i=%d k=%d j=%d failed: %w", i, k, j, err)
				}
			}
		}

		if block == nil {
			continue
		}

		if giantShift == 0 {
			if acc == nil {
				acc = block
			} else {
				if err := eval.Add(acc, block, acc); err != nil {
					return nil, fmt.Errorf("alg2 bsgs acc add i=%d failed: %w", i, err)
				}
			}
		} else {
			rot := bfv.NewCiphertext(params, 1, block.Level())
			galEl := params.GaloisElementForColRotation(giantShift)
			stRot := time.Now()
			if err := eval.Automorphism(block, galEl, rot); err != nil {
				return nil, fmt.Errorf("alg2 bsgs giant rotation i=%d failed: %w", i, err)
			}
			tm.GiantRotations += time.Since(stRot)
			if acc == nil {
				acc = rot
			} else {
				if err := eval.Add(acc, rot, acc); err != nil {
					return nil, fmt.Errorf("alg2 bsgs giant add i=%d failed: %w", i, err)
				}
			}
		}
	}

	tm.FirstStageEval += time.Since(startEval)
	return acc, nil
}

func parallelLT2SumColumns(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ct *rlwe.Ciphertext,
	n, ell, r int,
	tm *AlgoTimings,
) error {
	q := (r / 2) / ell
	gamma := log2Pow2(q)

	start := time.Now()
	for s := 0; s < gamma; s++ {
		rot := bfv.NewCiphertext(params, 1, ct.Level())
		shift := (1 << s) * ell * n
		galEl := params.GaloisElementForColRotation(shift)

		if err := eval.Automorphism(ct, galEl, rot); err != nil {
			return fmt.Errorf("alg2 sum-columns rotation s=%d failed: %w", s, err)
		}
		if err := eval.Add(ct, rot, ct); err != nil {
			return fmt.Errorf("alg2 sum-columns add s=%d failed: %w", s, err)
		}
	}
	tm.SecondStageEval += time.Since(start)
	return nil
}

func parallelLT2BSGSHoisted(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ctIn *rlwe.Ciphertext,
	A, B [][][]uint64,
	n, ell, r int,
) (*rlwe.Ciphertext, AlgoTimings, error) {

	var tm AlgoTimings
	start := time.Now()

	y, err := parallelLT2FirstStageBSGSHoisted(params, eval, ctIn, A, B, n, ell, r, &tm)
	if err != nil {
		return nil, tm, err
	}
	if err := parallelLT2SumColumns(params, eval, y, n, ell, r, &tm); err != nil {
		return nil, tm, err
	}

	tm.Total = time.Since(start)
	return y, tm, nil
}

func parallelLT3BSGSHoisted(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ctIn *rlwe.Ciphertext,
	U [][][]uint64,
	n, ell, r int,
) (*rlwe.Ciphertext, AlgoTimings, error) {

	var tm AlgoTimings
	start := time.Now()

	if ell < r {
		A, B := splitUHorizontal(U, ell, r)

		y, t2, err := parallelLT2BSGSHoisted(params, eval, ctIn, A, B, n, ell, r)
		if err != nil {
			return nil, tm, err
		}
		tm.AddStage(t2)

		startPost := time.Now()
		tauY, err := rowSwapCipher(params, eval, y)
		if err != nil {
			return nil, tm, fmt.Errorf("alg3 row swap failed: %w", err)
		}
		if err := eval.Add(y, tauY, y); err != nil {
			return nil, tm, fmt.Errorf("alg3 add y+tau(y) failed: %w", err)
		}
		tm.PostProcess += time.Since(startPost)

		tm.Total = time.Since(start)
		return y, tm, nil
	}

	// ell == r
	A, B, C, D := splitUBlocks(U, r)

	y, t2a, err := parallelLT2BSGSHoisted(params, eval, ctIn, A, D, n, r/2, r)
	if err != nil {
		return nil, tm, err
	}
	tm.AddStage(t2a)

	startPost := time.Now()
	ctTauM, err := rowSwapCipher(params, eval, ctIn)
	if err != nil {
		return nil, tm, fmt.Errorf("alg3 row swap on input failed: %w", err)
	}
	tm.PostProcess += time.Since(startPost)

	yPrime, t2b, err := parallelLT2BSGSHoisted(params, eval, ctTauM, B, C, n, r/2, r)
	if err != nil {
		return nil, tm, err
	}
	tm.AddStage(t2b)

	startPost = time.Now()
	if err := eval.Add(y, yPrime, y); err != nil {
		return nil, tm, fmt.Errorf("alg3 add y+y' failed: %w", err)
	}
	tm.PostProcess += time.Since(startPost)

	tm.Total = time.Since(start)
	return y, tm, nil
}

// =================================
// Algorithm 5 helpers
// =================================

func buildAllOnesCoeffs(n, s int) [][]uint64 {
	out := make([][]uint64, n)
	for i := 0; i < n; i++ {
		out[i] = make([]uint64, s)
		for j := 0; j < s; j++ {
			out[i][j] = 1
		}
	}
	return out
}

func buildPatersonStockmeyerMatrices(coeffs [][]uint64, r int) [][][]uint64 {
	n := len(coeffs)
	dPlus1 := len(coeffs[0])
	s := dPlus1 / r
	U := make([][][]uint64, n)
	for i := 0; i < n; i++ {
		U[i] = make([][]uint64, s)
		for row := 0; row < s; row++ {
			U[i][row] = make([]uint64, r)
			copy(U[i][row], coeffs[i][row*r:(row+1)*r])
		}
	}
	return U
}

func buildPatersonStockmeyerMatrixViews(coeffs [][]uint64, r int) [][][]uint64 {
	n := len(coeffs)
	if n == 0 {
		return nil
	}
	dPlus1 := len(coeffs[0])
	s := dPlus1 / r
	U := make([][][]uint64, n)
	for i := 0; i < n; i++ {
		U[i] = make([][]uint64, s)
		for row := 0; row < s; row++ {
			U[i][row] = coeffs[i][row*r : (row+1)*r]
		}
	}
	return U
}

func splitUHorizontalViews(U [][][]uint64, ell, r int) (A, B [][][]uint64) {
	n := len(U)
	half := r / 2
	A = make([][][]uint64, n)
	B = make([][][]uint64, n)
	for i := 0; i < n; i++ {
		A[i] = make([][]uint64, ell)
		B[i] = make([][]uint64, ell)
		for row := 0; row < ell; row++ {
			A[i][row] = U[i][row][:half]
			B[i][row] = U[i][row][half:]
		}
	}
	return
}

func splitUBlocksViews(U [][][]uint64, r int) (A, B, C, D [][][]uint64) {
	n := len(U)
	half := r / 2
	A = make([][][]uint64, n)
	B = make([][][]uint64, n)
	C = make([][][]uint64, n)
	D = make([][][]uint64, n)
	for i := 0; i < n; i++ {
		A[i] = make([][]uint64, half)
		B[i] = make([][]uint64, half)
		C[i] = make([][]uint64, half)
		D[i] = make([][]uint64, half)
		for row := 0; row < half; row++ {
			A[i][row] = U[i][row][:half]
			B[i][row] = U[i][row][half:]
		}
		for row := 0; row < half; row++ {
			C[i][row] = U[i][half+row][:half]
			D[i][row] = U[i][half+row][half:]
		}
	}
	return
}

func parallelLT3BSGSHoistedViews(
	params bfv.Parameters,
	eval *bfv.Evaluator,
	ctIn *rlwe.Ciphertext,
	U [][][]uint64,
	n, ell, r int,
) (*rlwe.Ciphertext, AlgoTimings, error) {
	var tm AlgoTimings
	start := time.Now()
	if ell < r {
		A, B := splitUHorizontalViews(U, ell, r)
		y, t2, err := parallelLT2BSGSHoisted(params, eval, ctIn, A, B, n, ell, r)
		if err != nil {
			return nil, tm, err
		}
		tm.AddStage(t2)
		startPost := time.Now()
		tauY, err := rowSwapCipher(params, eval, y)
		if err != nil {
			return nil, tm, fmt.Errorf("alg3 row swap failed: %w", err)
		}
		if err := eval.Add(y, tauY, y); err != nil {
			return nil, tm, fmt.Errorf("alg3 add y+tau(y) failed: %w", err)
		}
		tm.PostProcess += time.Since(startPost)
		tm.Total = time.Since(start)
		return y, tm, nil
	}
	A, B, C, D := splitUBlocksViews(U, r)
	y, t2a, err := parallelLT2BSGSHoisted(params, eval, ctIn, A, D, n, r/2, r)
	if err != nil {
		return nil, tm, err
	}
	tm.AddStage(t2a)
	startPost := time.Now()
	ctTauM, err := rowSwapCipher(params, eval, ctIn)
	if err != nil {
		return nil, tm, fmt.Errorf("alg3 row swap on input failed: %w", err)
	}
	tm.PostProcess += time.Since(startPost)
	yPrime, t2b, err := parallelLT2BSGSHoisted(params, eval, ctTauM, B, C, n, r/2, r)
	if err != nil {
		return nil, tm, err
	}
	tm.AddStage(t2b)
	startPost = time.Now()
	if err := eval.Add(y, yPrime, y); err != nil {
		return nil, tm, fmt.Errorf("alg3 add y+y' failed: %w", err)
	}
	tm.PostProcess += time.Since(startPost)
	tm.Total = time.Since(start)
	return y, tm, nil
}

func replicateSinglePolynomialShared(coeff []uint64, m int) [][]uint64 {
	out := make([][]uint64, m)
	for i := 0; i < m; i++ {
		out[i] = coeff
	}
	return out
}

func useLargeAlg5Branch(slots, m, d int) bool {
	if slots != 65536 || d != 4194304 {
		return false
	}
	switch m {
	case 8, 16, 32:
		return true
	default:
		return false
	}
}

func requiredGaloisElementsForFinalSum(params bfv.Parameters, n, s int) []uint64 {
	ell := bits.TrailingZeros(uint(s))
	set := map[uint64]struct{}{}
	for i := 0; i < ell-1; i++ {
		shift := n * (1 << i)
		set[params.GaloisElementForColRotation(shift)] = struct{}{}
	}
	if s > 1 {
		set[params.GaloisElementForColRotation(n*(1<<(ell-1)))] = struct{}{}
		set[params.GaloisElementForRowRotation()] = struct{}{}
	}
	out := make([]uint64, 0, len(set))
	for galEl := range set {
		out = append(out, galEl)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}

func neededGaloisElsAlg2(params bfv.Parameters, n, ell, r int) ([]uint64, error) {
	q := (r / 2) / ell
	gamma := log2Pow2(q)

	g, b, err := choosePolyLTBSGS(ell)
	if err != nil {
		return nil, err
	}

	seen := map[uint64]bool{}
	var galEls []uint64

	addShift := func(shift int) {
		if shift == 0 {
			return
		}
		galEl := params.GaloisElementForColRotation(shift)
		if !seen[galEl] {
			seen[galEl] = true
			galEls = append(galEls, galEl)
		}
	}

	for k := 0; k < g; k++ {
		addShift(k * n)
	}
	for i := 0; i < b; i++ {
		addShift(i * g * n)
	}
	for s := 0; s < gamma; s++ {
		addShift((1 << s) * ell * n)
	}

	return galEls, nil
}

func neededGaloisElsAlg3(params bfv.Parameters, n, ell, r int) ([]uint64, error) {
	innerEll := ell
	if ell == r {
		innerEll = r / 2
	}

	seen := map[uint64]bool{}
	var galEls []uint64
	add := func(ge uint64) {
		if ge == 1 {
			return
		}
		if !seen[ge] {
			seen[ge] = true
			galEls = append(galEls, ge)
		}
	}

	lt2, err := neededGaloisElsAlg2(params, n, innerEll, r)
	if err != nil {
		return nil, err
	}
	for _, ge := range lt2 {
		add(ge)
	}
	add(params.GaloisElementForRowRotation())
	sort.Slice(galEls, func(i, j int) bool { return galEls[i] < galEls[j] })
	return galEls, nil
}

func unionUint64Slices(a, b []uint64) []uint64 {
	set := map[uint64]struct{}{}
	for _, x := range a {
		set[x] = struct{}{}
	}
	for _, x := range b {
		set[x] = struct{}{}
	}
	out := make([]uint64, 0, len(set))
	for x := range set {
		out = append(out, x)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}

func parseCoeffList(spec string) ([]int64, error) {
	return parseVector(spec)
}

func randomCoeffVector(length int, mod uint64, seed int64) []int64 {
	rng := rand.New(rand.NewSource(seed))
	out := make([]int64, length)
	for i := range out {
		out[i] = int64(rng.Int63n(int64(mod)))
	}
	return out
}

func coeffsInt64ToMod(v []int64, mod uint64) []uint64 {
	out := make([]uint64, len(v))
	for i, x := range v {
		out[i] = toUintMod(x, mod)
	}
	return out
}

func replicateSinglePolynomial(coeff []uint64, m int) [][]uint64 {
	out := make([][]uint64, m)
	for i := 0; i < m; i++ {
		out[i] = append([]uint64(nil), coeff...)
	}
	return out
}

func repeatLeadingCoeff(lead uint64, m int) []uint64 {
	out := make([]uint64, m)
	for i := range out {
		out[i] = lead
	}
	return out
}

func alignCiphertextLevels(eval *bfv.Evaluator, a, b *rlwe.Ciphertext) {
	if a.Level() > b.Level() {
		eval.DropLevel(a, a.Level()-b.Level())
	} else if b.Level() > a.Level() {
		eval.DropLevel(b, b.Level()-a.Level())
	}
}

func rescaleCiphertextToLevel(eval *bfv.Evaluator, ct *rlwe.Ciphertext, targetLevel int) error {
	if targetLevel < 0 {
		return nil
	}
	if targetLevel > ct.Level() {
		return fmt.Errorf("target level %d exceeds current level %d", targetLevel, ct.Level())
	}
	for ct.Level() > targetLevel {
		before := ct.Level()
		if err := eval.Rescale(ct, ct); err != nil {
			return fmt.Errorf("rescale to level %d failed at level %d: %w", targetLevel, before, err)
		}
		if ct.Level() >= before {
			return fmt.Errorf("rescale to level %d made no progress: ciphertext level stayed at %d; use a non-scale-invariant evaluator for this modulus-switch step", targetLevel, before)
		}
	}
	return nil
}

func dropCiphertextCopyToLevel(eval *bfv.Evaluator, ct *rlwe.Ciphertext, targetLevel int) *rlwe.Ciphertext {
	out := ct.CopyNew()
	if targetLevel >= 0 && out.Level() > targetLevel {
		eval.DropLevel(out, out.Level()-targetLevel)
	}
	return out
}

func sparseRotateAndSum(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, baseLen, s int) (*rlwe.Ciphertext, error) {
	if s <= 1 {
		return ct, nil
	}
	if !isPow2(s) {
		return nil, fmt.Errorf("s=%d must be a power of two", s)
	}
	r := params.MaxSlots() / baseLen
	if s > r {
		return nil, fmt.Errorf("s=%d exceeds repetition factor r=%d", s, r)
	}
	ell := log2Pow2(s)
	h := ct.CopyNew()
	for i := 0; i < ell-1; i++ {
		shift := baseLen * (1 << i)
		rot, err := eval.RotateColumnsNew(h, shift)
		if err != nil {
			return nil, fmt.Errorf("RotateColumns(%d) failed: %w", shift, err)
		}
		h, err = eval.AddNew(h, rot)
		if err != nil {
			return nil, fmt.Errorf("Add after RotateColumns(%d) failed: %w", shift, err)
		}
	}
	if s == r {
		rot, err := eval.RotateRowsNew(h)
		if err != nil {
			return nil, fmt.Errorf("RotateRows failed: %w", err)
		}
		h, err = eval.AddNew(h, rot)
		if err != nil {
			return nil, fmt.Errorf("Add after RotateRows failed: %w", err)
		}
	} else {
		shift := baseLen * (1 << (ell - 1))
		rot, err := eval.RotateColumnsNew(h, shift)
		if err != nil {
			return nil, fmt.Errorf("final RotateColumns(%d) failed: %w", shift, err)
		}
		h, err = eval.AddNew(h, rot)
		if err != nil {
			return nil, fmt.Errorf("final Add after RotateColumns(%d) failed: %w", shift, err)
		}
	}
	return h, nil
}

func sparsePackLeadingCoeffs(leadCoeffs []uint64, slots int) ([]uint64, error) {
	vec, _, err := sparsePackMod(leadCoeffs, slots)
	return vec, err
}

func addLeadingPowerTerm(params bfv.Parameters, eval *bfv.Evaluator, baseCt, ctPowD *rlwe.Ciphertext, leadCoeffs []uint64) (*rlwe.Ciphertext, error) {
	leadVec, err := sparsePackLeadingCoeffs(leadCoeffs, params.MaxSlots())
	if err != nil {
		return nil, err
	}
	ctLead, err := mulPlainRescale(eval, ctPowD, leadVec)
	if err != nil {
		return nil, fmt.Errorf("leading plaintext-ciphertext multiplication failed: %w", err)
	}
	baseCopy := baseCt.CopyNew()
	alignCiphertextLevels(eval, baseCopy, ctLead)
	out, err := eval.AddNew(baseCopy, ctLead)
	if err != nil {
		return nil, fmt.Errorf("adding the leading x^d term failed: %w", err)
	}
	return out, nil
}

func polyEvalSparsePow2Alg5(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64, dropBeforeLT bool, ltDropLevel, ltPostLevel int) (*rlwe.Ciphertext, PolyEvalTiming, error) {
	var tm PolyEvalTiming
	start := time.Now()
	if len(coeffsLower) == 0 || len(coeffsLower[0]) == 0 {
		return nil, tm, errors.New("coeffsLower is empty")
	}
	d := len(coeffsLower[0])
	if !isPow2(d) {
		return nil, tm, fmt.Errorf("pow2-degree wrapper requires d=%d to be a power of two", d)
	}
	slots := params.MaxSlots()
	if slots%m != 0 {
		return nil, tm, fmt.Errorf("m=%d must divide MaxSlots=%d", m, slots)
	}
	r := slots / m
	if d <= r || d > r*r {
		return nil, tm, fmt.Errorf("Alg5 wrapper requires r < d <= r^2, got d=%d, r=%d", d, r)
	}
	if d%r != 0 {
		return nil, tm, fmt.Errorf("Alg5 wrapper requires r | d, got d=%d, r=%d", d, r)
	}
	s := d / r
	onesR := buildAllOnesCoeffs(m, r)
	onesS := buildAllOnesCoeffs(m, s)
	ctP, ctHalf, _, err := MonomialGenExtra(params, eval, ct, m, onesR, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on r failed: %w", err)
	}
	if ctHalf == nil {
		return nil, tm, errors.New("missing x^(r/2) ciphertext")
	}
	ctR, err := mulCtRelinRescale(eval, ctHalf, ctHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(r/2) to x^r failed: %w", err)
	}
	ctG, ctDHalf, _, err := MonomialGenExtra(params, eval, ctR, m, onesS, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on x^r failed: %w", err)
	}
	if ctDHalf == nil {
		return nil, tm, errors.New("missing x^(d/2) ciphertext from the second power stage")
	}
	if ltDropLevel >= 0 {
		if ctP.Level() > ltDropLevel {
			eval.DropLevel(ctP, ctP.Level()-ltDropLevel)
		}
	} else if dropBeforeLT && ctP.Level() > ctG.Level() {
		eval.DropLevel(ctP, ctP.Level()-ctG.Level())
	}
	U := buildPatersonStockmeyerMatrices(coeffsLower, r)
	ctY, _, err := parallelLT3BSGSHoisted(params, eval, ctP, U, m, s, r)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	alignCiphertextLevels(eval, ctY, ctG)
	alignCiphertextLevels(eval, ctY, ctG)
	ctCollapsed, err := mulCtRelinRescale(eval, ctY, ctG)
	if err != nil {
		return nil, tm, fmt.Errorf("pointwise multiplication y*g failed: %w", err)
	}
	ctBase, err := sparseRotateAndSum(params, eval, ctCollapsed, m, s)
	if err != nil {
		return nil, tm, err
	}
	ctPowD, err := mulCtRelinRescale(eval, ctDHalf, ctDHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
	}
	ctOut, err := addLeadingPowerTerm(params, eval, ctBase, ctPowD, leadCoeffs)
	if err != nil {
		return nil, tm, err
	}
	tm.Algorithm = "Algorithm 5 (degree d power-of-two wrapper)"
	tm.Total = time.Since(start)
	return ctOut, tm, nil
}

func polyEvalSparsePow2Alg5LargeBranch(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64, preLT *PreprocessedParallelLT3, dropBeforeLT bool, ltDropLevel, ltPostLevel int) (*rlwe.Ciphertext, PolyEvalTiming, error) {
	var tm PolyEvalTiming
	start := time.Now()
	progressf("poly eval (alg5-large): start")
	if len(coeffsLower) == 0 || len(coeffsLower[0]) == 0 {
		return nil, tm, errors.New("coeffsLower is empty")
	}
	d := len(coeffsLower[0])
	if !isPow2(d) {
		return nil, tm, fmt.Errorf("pow2-degree wrapper requires d=%d to be a power of two", d)
	}
	slots := params.MaxSlots()
	if slots%m != 0 {
		return nil, tm, fmt.Errorf("m=%d must divide MaxSlots=%d", m, slots)
	}
	r := slots / m
	if d <= r || d > r*r {
		return nil, tm, fmt.Errorf("Alg5 wrapper requires r < d <= r^2, got d=%d, r=%d", d, r)
	}
	if d%r != 0 {
		return nil, tm, fmt.Errorf("Alg5 wrapper requires r | d, got d=%d, r=%d", d, r)
	}
	s := d / r
	mod := params.PlaintextModulus()
	traceEnabled := len(globalPolyNoiseBase) == m && len(globalPolyNoiseCoeffLower) == m && len(globalPolyNoiseLeadCoeffs) == m
	base := globalPolyNoiseBase
	leadCoeffsRef := globalPolyNoiseLeadCoeffs
	var ctY, ctCollapsed, ctBase *rlwe.Ciphertext
	onesR := buildAllOnesCoeffs(m, r)
	onesS := buildAllOnesCoeffs(m, s)

	progressf("poly eval (alg5-large): building (1,x,...,x^{r-1}) and x^(r/2)")
	ctP, ctHalf, _, err := MonomialGenExtra(params, eval, ct, m, onesR, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on r failed: %w", err)
	}
	if ctHalf == nil {
		return nil, tm, errors.New("missing x^(r/2) ciphertext")
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: basis (1,x,...,x^{r-1})", ctP, monomialGenReferenceSlots(base, buildAllOnesCoeffs(m, r), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^(r/2)", ctHalf, repeatVector(powVectorMod(base, r/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	progressf("poly eval (alg5-large): computing x^r")
	ctR, err := mulCtRelinRescale(eval, ctHalf, ctHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(r/2) to x^r failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^r", ctR, repeatVector(powVectorMod(base, r, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	progressf("poly eval (alg5-large): building grouped powers of x^r and x^(d/2)")
	ctG, ctDHalf, _, err := MonomialGenExtra(params, eval, ctR, m, onesS, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on x^r failed: %w", err)
	}
	if ctDHalf == nil {
		return nil, tm, errors.New("missing x^(d/2) ciphertext from the second power stage")
	}
	if traceEnabled {
		xR := powVectorMod(base, r, mod)
		if err := maybeTracePolyNoise("poly/LUT alg5-large: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(m, s), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, d/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	if ltDropLevel >= 0 {
		if ctP.Level() > ltDropLevel {
			eval.DropLevel(ctP, ctP.Level()-ltDropLevel)
		}
	} else if dropBeforeLT && ctP.Level() > ctG.Level() {
		eval.DropLevel(ctP, ctP.Level()-ctG.Level())
	}

	if preLT != nil {
		progressf("poly eval (alg5-large): running preprocessed view-based ParallelLT")
		ctY, _, err = parallelLT3BSGSHoistedPrecomp(params, eval, ctP, preLT, m, s, r)
		if err != nil {
			return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
		}
	} else {
		progressf("poly eval (alg5-large): running view-based ParallelLT")
		U := buildPatersonStockmeyerMatrixViews(coeffsLower, r)
		ctY, _, err = parallelLT3BSGSHoistedViews(params, eval, ctP, U, m, s, r)
		if err != nil {
			return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
		}
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: ParallelLT output (before post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	if ltPostLevel >= 0 && ctY.Level() > ltPostLevel {
		if err := rescaleCiphertextToLevel(eval, ctY, ltPostLevel); err != nil {
			return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
		}
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}

	progressf("poly eval (alg5-large): multiplying ParallelLT output with grouped powers")
	alignCiphertextLevels(eval, ctY, ctG)
	ctCollapsed, err = mulCtRelinRescale(eval, ctY, ctG)
	if err != nil {
		return nil, tm, fmt.Errorf("pointwise multiplication y*g failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: collapsed blocks y*g", ctCollapsed, expectedAlg5CollapsedSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}

	progressf("poly eval (alg5-large): rotate-and-sum lower polynomial")
	ctBase, err = sparseRotateAndSum(params, eval, ctCollapsed, m, s)
	if err != nil {
		return nil, tm, err
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	progressf("poly eval (alg5-large): computing x^d")
	ctPowD, err := mulCtRelinRescale(eval, ctDHalf, ctDHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^d", ctPowD, repeatVector(powVectorMod(base, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	ctLead, err := mulPlainRescale(eval, ctPowD, sparsePackLeadingOrPanic(leadCoeffs, params.MaxSlots()))
	if err != nil {
		return nil, tm, fmt.Errorf("leading x^d plaintext-ciphertext multiplication failed: %w", err)
	}
	if traceEnabled {
		leadVals := make([]uint64, len(base))
		for i := range leadVals {
			leadVals[i] = mulMod(leadCoeffsRef[i], powMod(base[i], uint64(d), mod), mod)
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-large: leading term a_d*x^d", ctLead, repeatVector(leadVals, r)); err != nil {
			return nil, tm, err
		}
	}
	baseCopy := ctBase.CopyNew()
	alignCiphertextLevels(eval, baseCopy, ctLead)
	ctOut, err := eval.AddNew(baseCopy, ctLead)
	if err != nil {
		return nil, tm, fmt.Errorf("adding the leading x^d term failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: final F(x)", ctOut, repeatVector(fullPolyValues(base, coeffsLower, leadCoeffsRef, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	progressf("poly eval (alg5-large): final ciphertext ready at level=%d", ctOut.Level())
	tm.Algorithm = "Algorithm 5 (large-parameter branch, view-based LT)"
	tm.Total = time.Since(start)
	return ctOut, tm, nil
}

func sparsePackLeadingOrPanic(leadCoeffs []uint64, slots int) []uint64 {
	vec, err := sparsePackLeadingCoeffs(leadCoeffs, slots)
	if err != nil {
		panic(err)
	}
	return vec
}

func collectPolyEvalGaloisElements(params bfv.Parameters, m, d int) ([]uint64, error) {
	if !isPow2(d) {
		return nil, fmt.Errorf("d=%d must be a power of two", d)
	}
	r := params.MaxSlots() / m
	set := map[uint64]struct{}{}
	addAll := func(v []uint64) {
		for _, x := range v {
			set[x] = struct{}{}
		}
	}
	if m == 1 && d <= r {
		addAll(requiredGaloisElementsForFinalSum(params, m, d))
	} else {
		if d <= r || d > r*r || d%r != 0 {
			return nil, fmt.Errorf("Algorithm 5 requires r < d <= r^2 and r|d unless m=1 uses the direct path, got d=%d, r=%d, m=%d", d, r, m)
		}
		s := d / r
		addAll(requiredGaloisElementsForFinalSum(params, m, s))
		lt, err := neededGaloisElsAlg3(params, m, s, r)
		if err != nil {
			return nil, err
		}
		addAll(lt)
	}
	out := make([]uint64, 0, len(set))
	for x := range set {
		out = append(out, x)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out, nil
}

type RotationKeyUse struct {
	GaloisElement uint64
	LevelQ        int
	Count         int
	Sources       map[string]int
}

type RotationKeyPlan struct {
	uses map[uint64]*RotationKeyUse
}

type RotationKeyLevelStat struct {
	LevelQ    int
	LogQBits  int
	Count     int
	SizeBytes int64
}

type PolyRotationLevelInfo struct {
	InputLevel    int
	PowerLevel    int
	GroupedLevel  int
	LTInputLevel  int
	LTOutputLevel int
	FinalSumLevel int
	OutputLevel   int
}

func newRotationKeyPlan() *RotationKeyPlan {
	return &RotationKeyPlan{uses: map[uint64]*RotationKeyUse{}}
}

func sourceWithLevel(source string, levelQ int) string {
	return fmt.Sprintf("%s@L%d", source, levelQ)
}

func (p *RotationKeyPlan) Add(galEl uint64, levelQ int, source string) {
	if p == nil || galEl == 1 {
		return
	}
	if levelQ < 0 {
		levelQ = 0
	}
	u, ok := p.uses[galEl]
	if !ok {
		u = &RotationKeyUse{GaloisElement: galEl, LevelQ: levelQ, Sources: map[string]int{}}
		p.uses[galEl] = u
	}
	if levelQ > u.LevelQ {
		u.LevelQ = levelQ
	}
	u.Count++
	if source != "" {
		u.Sources[sourceWithLevel(source, levelQ)]++
	}
}

func (p *RotationKeyPlan) AddColRotation(params bfv.Parameters, shift int, levelQ int, source string) {
	if shift == 0 {
		return
	}
	p.Add(params.GaloisElementForColRotation(shift), levelQ, source)
}

func (p *RotationKeyPlan) AddRowRotation(params bfv.Parameters, levelQ int, source string) {
	p.Add(params.GaloisElementForRowRotation(), levelQ, source)
}

func (p *RotationKeyPlan) Has(galEl uint64) bool {
	if p == nil {
		return false
	}
	_, ok := p.uses[galEl]
	return ok
}

func (p *RotationKeyPlan) ForceLevel(levelQ int) {
	if p == nil {
		return
	}
	for _, u := range p.uses {
		u.LevelQ = levelQ
	}
}

func (p *RotationKeyPlan) GaloisElements() []uint64 {
	out := make([]uint64, 0, len(p.uses))
	for ge := range p.uses {
		out = append(out, ge)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}

func (p *RotationKeyPlan) GaloisElementsByLevel() map[int][]uint64 {
	out := map[int][]uint64{}
	for ge, u := range p.uses {
		out[u.LevelQ] = append(out[u.LevelQ], ge)
	}
	for level := range out {
		sort.Slice(out[level], func(i, j int) bool { return out[level][i] < out[level][j] })
	}
	return out
}

func sortedLevelsFromMap[T any](m map[int]T) []int {
	levels := make([]int, 0, len(m))
	for level := range m {
		levels = append(levels, level)
	}
	sort.Ints(levels)
	return levels
}

func validateRotationKeyPlan(plan *RotationKeyPlan, maxLevel int) error {
	if plan == nil {
		return errors.New("nil rotation key plan")
	}
	for ge, u := range plan.uses {
		if u.LevelQ < 0 || u.LevelQ > maxLevel {
			return fmt.Errorf("rotation key for Galois element %d has invalid LevelQ=%d; MaxLevel=%d", ge, u.LevelQ, maxLevel)
		}
	}
	return nil
}

func monomialOutputLevel(inputLevel, s int) (int, error) {
	if s <= 0 || !isPow2(s) {
		return 0, fmt.Errorf("s=%d must be a positive power of two", s)
	}
	if s == 1 {
		return inputLevel, nil
	}
	ell := log2Pow2(s)
	if ell == 1 {
		return inputLevel - 1, nil
	}
	return inputLevel - ell - 1, nil
}

func monomialExtraLevel(inputLevel, s int) (int, error) {
	if s <= 1 {
		return -1, fmt.Errorf("s=%d does not produce an extra half-power ciphertext", s)
	}
	if !isPow2(s) {
		return -1, fmt.Errorf("s=%d must be a power of two", s)
	}
	ell := log2Pow2(s)
	return inputLevel - (ell - 1), nil
}

func checkPlannedLevel(levelQ int, name string) error {
	if levelQ < 0 {
		return fmt.Errorf("planned %s level became negative: %d", name, levelQ)
	}
	return nil
}

func addSparseRotateAndSumKeyUses(params bfv.Parameters, plan *RotationKeyPlan, baseLen, s, levelQ int, source string) error {
	if s <= 1 {
		return nil
	}
	if !isPow2(s) {
		return fmt.Errorf("s=%d must be a power of two", s)
	}
	if baseLen <= 0 || params.MaxSlots()%baseLen != 0 {
		return fmt.Errorf("invalid baseLen=%d for MaxSlots=%d", baseLen, params.MaxSlots())
	}
	if err := checkPlannedLevel(levelQ, source); err != nil {
		return err
	}
	r := params.MaxSlots() / baseLen
	if s > r {
		return fmt.Errorf("s=%d exceeds repetition factor r=%d", s, r)
	}
	ell := log2Pow2(s)
	for i := 0; i < ell-1; i++ {
		shift := baseLen * (1 << i)
		plan.AddColRotation(params, shift, levelQ, source)
	}
	if s == r {
		plan.AddRowRotation(params, levelQ, source)
	} else {
		shift := baseLen * (1 << (ell - 1))
		plan.AddColRotation(params, shift, levelQ, source)
	}
	return nil
}

func addSlotToCoeffBSGSKeyUses(params bfv.Parameters, plan *RotationKeyPlan, n, inputLevel int) error {
	if n <= 1 {
		return nil
	}
	if err := checkPlannedLevel(inputLevel, "SlotToCoeff BSGS input"); err != nil {
		return err
	}
	g := int(math.Ceil(math.Sqrt(float64(n))))
	b := (n + g - 1) / g
	for k := 1; k < g; k++ {
		plan.AddColRotation(params, k, inputLevel, "SlotToCoeff baby")
	}
	giantLevel := inputLevel - 1
	if giantLevel < 0 {
		giantLevel = 0
	}
	for i := 1; i < b; i++ {
		shift := i * g
		if shift < n {
			plan.AddColRotation(params, shift, giantLevel, "SlotToCoeff giant")
		}
	}
	return nil
}

func addNeededGaloisElsAlg2KeyUsesAtLevel(params bfv.Parameters, plan *RotationKeyPlan, n, ell, r, levelQ int, source string) error {
	if err := checkPlannedLevel(levelQ, source); err != nil {
		return err
	}
	q := (r / 2) / ell
	gamma := log2Pow2(q)
	g, b, err := choosePolyLTBSGS(ell)
	if err != nil {
		return err
	}
	for k := 1; k < g; k++ {
		plan.AddColRotation(params, k*n, levelQ, source+" baby")
	}
	for i := 1; i < b; i++ {
		plan.AddColRotation(params, i*g*n, levelQ, source+" giant")
	}
	for s := 0; s < gamma; s++ {
		plan.AddColRotation(params, (1<<s)*ell*n, levelQ, source+" sum-columns")
	}
	return nil
}

func addNeededGaloisElsAlg3KeyUsesAtLevel(params bfv.Parameters, plan *RotationKeyPlan, n, ell, r, levelQ int, source string) error {
	innerEll := ell
	if ell == r {
		innerEll = r / 2
	}
	if err := addNeededGaloisElsAlg2KeyUsesAtLevel(params, plan, n, innerEll, r, levelQ, source); err != nil {
		return err
	}
	plan.AddRowRotation(params, levelQ, source+" row")
	return nil
}

func addPolyEvalRotationKeyUses(params bfv.Parameters, plan *RotationKeyPlan, m, d int, dropBeforeLT bool, ltDropLevel, ltPostLevel int, leadingTermEvaluated bool) (PolyRotationLevelInfo, error) {
	info := PolyRotationLevelInfo{InputLevel: params.MaxLevel() - 1}
	if info.InputLevel < 0 {
		return info, fmt.Errorf("MaxLevel=%d is too small for post-packing polynomial input", params.MaxLevel())
	}
	if !isPow2(d) {
		return info, fmt.Errorf("d=%d must be a power of two", d)
	}
	r := params.MaxSlots() / m
	if m == 1 && d <= r {
		lowerLevel, err := monomialOutputLevel(info.InputLevel, d)
		if err != nil {
			return info, err
		}
		info.PowerLevel = lowerLevel
		info.FinalSumLevel = lowerLevel
		info.OutputLevel = lowerLevel
		if err := addSparseRotateAndSumKeyUses(params, plan, m, d, lowerLevel, "poly direct rotate-sum"); err != nil {
			return info, err
		}
		if leadingTermEvaluated {
			var leadLevel int
			if d == 1 {
				leadLevel = info.InputLevel - 1
			} else {
				halfLevel, err := monomialExtraLevel(info.InputLevel, d)
				if err != nil {
					return info, err
				}
				leadLevel = halfLevel - 2
			}
			if leadLevel >= 0 && leadLevel < info.OutputLevel {
				info.OutputLevel = leadLevel
			}
		}
		return info, nil
	}
	if d <= r || d > r*r || d%r != 0 {
		return info, fmt.Errorf("Algorithm 5 requires r < d <= r^2 and r|d unless m=1 uses the direct path, got d=%d, r=%d, m=%d", d, r, m)
	}

	s := d / r
	ctPLevel, err := monomialOutputLevel(info.InputLevel, r)
	if err != nil {
		return info, err
	}
	ctHalfLevel, err := monomialExtraLevel(info.InputLevel, r)
	if err != nil {
		return info, err
	}
	ctRLevel := ctHalfLevel - 1
	if err := checkPlannedLevel(ctRLevel, "x^r"); err != nil {
		return info, err
	}
	ctGLevel, err := monomialOutputLevel(ctRLevel, s)
	if err != nil {
		return info, err
	}
	ctDHalfLevel, err := monomialExtraLevel(ctRLevel, s)
	if err != nil {
		return info, err
	}
	info.PowerLevel = ctPLevel
	info.GroupedLevel = ctGLevel

	ltInputLevel := ctPLevel
	if ltDropLevel >= 0 {
		if ltInputLevel > ltDropLevel {
			ltInputLevel = ltDropLevel
		}
	} else if dropBeforeLT && ltInputLevel > ctGLevel {
		ltInputLevel = ctGLevel
	}
	if err := checkPlannedLevel(ltInputLevel, "ParallelLT input"); err != nil {
		return info, err
	}
	info.LTInputLevel = ltInputLevel
	if err := addNeededGaloisElsAlg3KeyUsesAtLevel(params, plan, m, s, r, ltInputLevel, "poly ParallelLT"); err != nil {
		return info, err
	}

	ltOutputLevel := ltInputLevel
	if ltPostLevel >= 0 && ltOutputLevel > ltPostLevel {
		ltOutputLevel = ltPostLevel
	}
	info.LTOutputLevel = ltOutputLevel
	collapsedLevel := minInt(ltOutputLevel, ctGLevel) - 1
	if err := checkPlannedLevel(collapsedLevel, "post-ParallelLT collapsed ciphertext"); err != nil {
		return info, err
	}
	info.FinalSumLevel = collapsedLevel
	if err := addSparseRotateAndSumKeyUses(params, plan, m, s, collapsedLevel, "poly final rotate-sum"); err != nil {
		return info, err
	}

	info.OutputLevel = collapsedLevel
	if leadingTermEvaluated {
		ctLeadLevel := ctDHalfLevel - 2
		if err := checkPlannedLevel(ctLeadLevel, "leading term"); err != nil {
			return info, err
		}
		if ctLeadLevel < info.OutputLevel {
			info.OutputLevel = ctLeadLevel
		}
	}
	return info, nil
}

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func addLegacyFullLevelFallbacks(params bfv.Parameters, plan *RotationKeyPlan, galEls []uint64, source string) {
	fullLevel := params.MaxLevel()
	for _, ge := range galEls {
		if ge != 1 && !plan.Has(ge) {
			plan.Add(ge, fullLevel, source)
		}
	}
}

func generateGaloisKeysFromPlan(params bfv.Parameters, kgen *rlwe.KeyGenerator, sk *rlwe.SecretKey, plan *RotationKeyPlan) ([]*rlwe.GaloisKey, []RotationKeyLevelStat, int64, error) {
	if err := validateRotationKeyPlan(plan, params.MaxLevel()); err != nil {
		return nil, nil, 0, err
	}
	byLevel := plan.GaloisElementsByLevel()
	levels := sortedLevelsFromMap(byLevel)
	all := make([]*rlwe.GaloisKey, 0, len(plan.uses))
	stats := make([]RotationKeyLevelStat, 0, len(levels))
	var total int64
	for _, level := range levels {
		galEls := byLevel[level]
		levelForKey := level
		gks := kgen.GenGaloisKeysNew(galEls, sk, rlwe.EvaluationKeyParameters{LevelQ: &levelForKey})
		var size int64
		for _, gk := range gks {
			size += int64(gk.BinarySize())
		}
		logQBits := params.RingQ().AtLevel(level).Modulus().BitLen()
		stats = append(stats, RotationKeyLevelStat{LevelQ: level, LogQBits: logQBits, Count: len(gks), SizeBytes: size})
		total += size
		all = append(all, gks...)
	}
	return all, stats, total, nil
}

func sumCiphertextBinarySize(cts []*rlwe.Ciphertext) int64 {
	var total int64
	for _, ct := range cts {
		if ct != nil {
			total += int64(ct.BinarySize())
		}
	}
	return total
}

func formatBytesIEC(n int64) string {
	const unit = int64(1024)
	if n < unit {
		return fmt.Sprintf("%d B", n)
	}
	value := float64(n)
	units := []string{"KiB", "MiB", "GiB", "TiB"}
	for _, u := range units {
		value /= float64(unit)
		if value < float64(unit) {
			return fmt.Sprintf("%.2f %s", value, u)
		}
	}
	return fmt.Sprintf("%.2f PiB", value/float64(unit))
}

func printGoMemStats(label string) {
	var ms runtime.MemStats
	runtime.ReadMemStats(&ms)
	fmt.Printf("[mem] %s: HeapAlloc=%s HeapInuse=%s HeapSys=%s HeapIdle=%s HeapReleased=%s NumGC=%d PauseTotal=%v\n",
		label,
		formatBytesIEC(int64(ms.HeapAlloc)),
		formatBytesIEC(int64(ms.HeapInuse)),
		formatBytesIEC(int64(ms.HeapSys)),
		formatBytesIEC(int64(ms.HeapIdle)),
		formatBytesIEC(int64(ms.HeapReleased)),
		ms.NumGC,
		time.Duration(ms.PauseTotalNs))
}

func maybeCollectRunGarbage(runIdx int, totalRuns int, gcEvery int, freeOSMemory bool, memProgress bool) {
	if gcEvery <= 0 {
		return
	}
	runNo := runIdx + 1
	if runNo < totalRuns && runNo%gcEvery != 0 {
		return
	}
	if memProgress {
		printGoMemStats(fmt.Sprintf("after run %d before GC", runNo))
	}
	if freeOSMemory {
		// This is stronger and slower than runtime.GC(): it also asks Go to return
		// idle heap pages to the operating system. Use it only when the VM/Windows
		// memory pressure is high or when checking memory leaks.
		debug.FreeOSMemory()
	} else {
		runtime.GC()
	}
	if memProgress {
		printGoMemStats(fmt.Sprintf("after run %d after GC", runNo))
	}
}

func cloneSecretKeyQOnly(params bfv.Parameters, skIn *rlwe.SecretKey) (*rlwe.SecretKey, error) {
	if skIn == nil {
		return nil, errors.New("nil input secret key")
	}
	skOut := rlwe.NewSecretKey(params)
	if skIn.LevelQ() < skOut.LevelQ() {
		return nil, fmt.Errorf("input secret key LevelQ=%d is smaller than target LevelQ=%d", skIn.LevelQ(), skOut.LevelQ())
	}
	skOut.Value.Q.CopyLvl(skOut.LevelQ(), skIn.Value.Q)
	return skOut, nil
}

func formatLevelPForPrint(params bfv.Parameters, levelP int) string {
	if levelP < 0 {
		return "LevelP=-1 (no P)"
	}
	if params.RingP() == nil {
		return fmt.Sprintf("LevelP=%d (but params has no P)", levelP)
	}
	return fmt.Sprintf("LevelP=%d (#P=%d, logP≈%d bits)", levelP, levelP+1, params.RingP().AtLevel(levelP).Modulus().BitLen())
}

func formatPow2BaseForPrint(base int) string {
	if base <= 0 {
		return "disabled"
	}
	return fmt.Sprintf("2^%d", base)
}

func evalSinglePolyMod(x uint64, coeff []uint64, mod uint64) uint64 {
	var acc uint64
	pow := uint64(1 % mod)
	for _, a := range coeff {
		acc = (acc + (a%mod)*pow%mod) % mod
		pow = (pow * x) % mod
	}
	return acc
}

func evalSinglePolyVector(base []uint64, coeff []uint64, mod uint64) []uint64 {
	out := make([]uint64, len(base))
	for i, x := range base {
		out[i] = evalSinglePolyMod(x, coeff, mod)
	}
	return out
}

func polyEvalSparsePow2Alg5Precomp(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, pre *PreprocessedPolyEval, dropBeforeLT bool, ltDropLevel, ltPostLevel int) (*rlwe.Ciphertext, PolyEvalTiming, error) {
	var tm PolyEvalTiming
	start := time.Now()
	progressf("poly eval (alg5): start")
	if pre == nil || pre.OnesRMon == nil || pre.OnesSMon == nil || pre.LT == nil || pre.LeadPT == nil {
		return nil, tm, errors.New("missing preprocessed data for Algorithm 5")
	}
	mod := params.PlaintextModulus()
	r := params.MaxSlots() / pre.M
	s := pre.D / r
	traceEnabled := len(globalPolyNoiseBase) == pre.M && len(globalPolyNoiseCoeffLower) == pre.M && len(globalPolyNoiseLeadCoeffs) == pre.M
	base := globalPolyNoiseBase
	coeffsLower := globalPolyNoiseCoeffLower
	leadCoeffs := globalPolyNoiseLeadCoeffs
	progressf("poly eval (alg5): building (1,x,...,x^{r-1}) and x^(r/2)")
	ctP, ctHalf, _, err := MonomialGenExtraPrecomp(params, eval, ct, pre.M, pre.OnesRMon, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on r failed: %w", err)
	}
	if ctHalf == nil {
		return nil, tm, errors.New("missing x^(r/2) ciphertext")
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: basis (1,x,...,x^{r-1})", ctP, monomialGenReferenceSlots(base, buildAllOnesCoeffs(pre.M, r), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(r/2)", ctHalf, repeatVector(powVectorMod(base, r/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	progressf("poly eval (alg5): computing x^r")
	ctR, err := mulCtRelinRescale(eval, ctHalf, ctHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(r/2) to x^r failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: x^r", ctR, repeatVector(powVectorMod(base, r, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	progressf("poly eval (alg5): building grouped powers of x^r and x^(d/2)")
	ctG, ctDHalf, _, err := MonomialGenExtraPrecomp(params, eval, ctR, pre.M, pre.OnesSMon, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on x^r failed: %w", err)
	}
	if ctDHalf == nil {
		return nil, tm, errors.New("missing x^(d/2) ciphertext from the second power stage")
	}
	if traceEnabled {
		xR := powVectorMod(base, r, mod)
		if err := maybeTracePolyNoise("poly/LUT alg5: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(pre.M, s), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, pre.D/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	if ltDropLevel >= 0 {
		if ctP.Level() > ltDropLevel {
			eval.DropLevel(ctP, ctP.Level()-ltDropLevel)
		}
	} else if dropBeforeLT && ctP.Level() > ctG.Level() {
		eval.DropLevel(ctP, ctP.Level()-ctG.Level())
	}
	progressf("poly eval (alg5): running ParallelLT")
	ctY, _, err := parallelLT3BSGSHoistedPrecomp(params, eval, ctP, pre.LT, pre.M, s, r)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (before post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	if ltPostLevel >= 0 && ctY.Level() > ltPostLevel {
		if err := rescaleCiphertextToLevel(eval, ctY, ltPostLevel); err != nil {
			return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
		}
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	alignCiphertextLevels(eval, ctY, ctG)
	progressf("poly eval (alg5): multiplying ParallelLT output with grouped powers")
	ctCollapsed, err := mulCtRelinRescale(eval, ctY, ctG)
	if err != nil {
		return nil, tm, fmt.Errorf("pointwise multiplication y*g failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: collapsed blocks y*g", ctCollapsed, expectedAlg5CollapsedSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	progressf("poly eval (alg5): rotate-and-sum lower polynomial")
	ctBase, err := sparseRotateAndSum(params, eval, ctCollapsed, pre.M, s)
	if err != nil {
		return nil, tm, err
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	progressf("poly eval (alg5): computing x^d")
	ctPowD, err := mulCtRelinRescale(eval, ctDHalf, ctDHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: x^d", ctPowD, repeatVector(powVectorMod(base, pre.D, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	ctLead, err := mulOperandRescale(eval, ctPowD, pre.LeadPT)
	if err != nil {
		return nil, tm, fmt.Errorf("leading x^d plaintext-ciphertext multiplication failed: %w", err)
	}
	if traceEnabled {
		leadVals := make([]uint64, len(base))
		for i := range leadVals {
			leadVals[i] = mulMod(leadCoeffs[i], powMod(base[i], uint64(pre.D), mod), mod)
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: leading term a_d*x^d", ctLead, repeatVector(leadVals, r)); err != nil {
			return nil, tm, err
		}
	}
	baseCopy := ctBase.CopyNew()
	alignCiphertextLevels(eval, baseCopy, ctLead)
	ctOut, err := eval.AddNew(baseCopy, ctLead)
	if err != nil {
		return nil, tm, fmt.Errorf("adding the leading x^d term failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: final F(x)", ctOut, repeatVector(fullPolyValues(base, coeffsLower, leadCoeffs, pre.D, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	progressf("poly eval (alg5): final ciphertext ready at level=%d", ctOut.Level())
	tm.Algorithm = "Algorithm 5 (degree d power-of-two wrapper, preprocessed plaintexts)"
	tm.Total = time.Since(start)
	return ctOut, tm, nil
}

func alignCiphertextsByRescaleToMinLevel(eval *bfv.Evaluator, a, b *rlwe.Ciphertext) error {
	if a.Level() > b.Level() {
		return rescaleCiphertextToLevel(eval, a, b.Level())
	}
	if b.Level() > a.Level() {
		return rescaleCiphertextToLevel(eval, b, a.Level())
	}
	return nil
}

type NoiseProbeResult struct {
	Name                    string
	Level                   int
	CurrentLogQBits         int
	NextLogQBits            int
	ScaleModT               uint64
	MaxCoeffNoiseAbs        string
	RequiredBitsNoMargin    int
	RecommendedBits         int
	SmallestSafeLevel       int
	SmallestSafeLogQBits    int
	SafeDropLevelsWithGuard int
}

func centeredModBig(x, mod *big.Int) *big.Int {
	z := new(big.Int).Mod(new(big.Int).Set(x), mod)
	half := new(big.Int).Rsh(new(big.Int).Set(mod), 1)
	if z.Cmp(half) == 1 {
		z.Sub(z, mod)
	}
	return z
}

func estimateResidualBitsFromNoise(maxNoise *big.Int, plainMod uint64, safetyBits int) (noMargin, recommended int) {
	if maxNoise == nil || maxNoise.Sign() <= 0 {
		if safetyBits < 0 {
			safetyBits = 0
		}
		return 1, 1 + safetyBits
	}
	req := new(big.Int).Mul(new(big.Int).Set(maxNoise), new(big.Int).SetUint64(2*plainMod))
	noMargin = req.BitLen()
	recommended = noMargin + maxInt(0, safetyBits)
	return
}

func probeCipherNoiseAgainstSlots(params bfv.Parameters, encoder *bfv.Encoder, dec *rlwe.Decryptor, ct *rlwe.Ciphertext, expectedSlots []uint64, safetyBits int, name string) (*NoiseProbeResult, error) {
	ptGot := dec.DecryptNew(ct)
	ptRef := bfv.NewPlaintext(params, ct.Level())
	ptRef.Scale = ct.Scale
	if err := encoder.Encode(expectedSlots, ptRef); err != nil {
		return nil, fmt.Errorf("failed to encode expected plaintext for probe %q: %w", name, err)
	}
	ringQ := params.RingQ().AtLevel(ct.Level())
	bigQ := ringQ.Modulus()
	gotBig := polyToBigintCentered(ringQ, ptGot.Value, ptGot.IsNTT, ptGot.IsMontgomery)
	refBig := polyToBigintCentered(ringQ, ptRef.Value, ptRef.IsNTT, ptRef.IsMontgomery)
	maxAbs := big.NewInt(0)
	for i := range gotBig {
		diff := centeredModBig(new(big.Int).Sub(gotBig[i], refBig[i]), bigQ)
		if diff.Sign() < 0 {
			diff.Neg(diff)
		}
		if diff.Cmp(maxAbs) > 0 {
			maxAbs.Set(diff)
		}
	}
	noMargin, recommended := estimateResidualBitsFromNoise(maxAbs, params.PlaintextModulus(), safetyBits)
	currentBits := bigQ.BitLen()
	nextBits := -1
	if ct.Level() > 0 {
		nextBits = params.RingQ().AtLevel(ct.Level() - 1).Modulus().BitLen()
	}
	smallestSafeLevel := -1
	smallestSafeBits := -1
	if recommended <= currentBits {
		for lvl := 0; lvl <= ct.Level(); lvl++ {
			bits := params.RingQ().AtLevel(lvl).Modulus().BitLen()
			if bits >= recommended {
				smallestSafeLevel = lvl
				smallestSafeBits = bits
				break
			}
		}
	}
	safeDropLevels := 0
	if smallestSafeLevel >= 0 {
		safeDropLevels = ct.Level() - smallestSafeLevel
	}
	return &NoiseProbeResult{
		Name:                    name,
		Level:                   ct.Level(),
		CurrentLogQBits:         currentBits,
		NextLogQBits:            nextBits,
		ScaleModT:               ct.Scale.Uint64() % params.PlaintextModulus(),
		MaxCoeffNoiseAbs:        maxAbs.String(),
		RequiredBitsNoMargin:    noMargin,
		RecommendedBits:         recommended,
		SmallestSafeLevel:       smallestSafeLevel,
		SmallestSafeLogQBits:    smallestSafeBits,
		SafeDropLevelsWithGuard: safeDropLevels,
	}, nil
}

func printNoiseProbeResult(p *NoiseProbeResult) {
	if p == nil {
		return
	}
	fmt.Printf("%s:\n", p.Name)
	fmt.Printf("  level                    : %d\n", p.Level)
	fmt.Printf("  current logQ bits        : %d\n", p.CurrentLogQBits)
	if p.NextLogQBits >= 0 {
		fmt.Printf("  next logQ bits (1 drop)  : %d\n", p.NextLogQBits)
	} else {
		fmt.Printf("  next logQ bits (1 drop)  : n/a\n")
	}
	fmt.Printf("  scale mod T              : %d\n", p.ScaleModT)
	fmt.Printf("  max coeff noise abs      : %s\n", p.MaxCoeffNoiseAbs)
	fmt.Printf("  min residual logQ (raw)  : %d\n", p.RequiredBitsNoMargin)
	fmt.Printf("  min residual logQ (safe) : %d\n", p.RecommendedBits)
	if p.SmallestSafeLevel >= 0 {
		fmt.Printf("  smallest safe level      : %d\n", p.SmallestSafeLevel)
		fmt.Printf("  smallest safe logQ bits  : %d\n", p.SmallestSafeLogQBits)
		fmt.Printf("  safe drop levels now     : %d\n", p.SafeDropLevelsWithGuard)
	} else {
		fmt.Printf("  smallest safe level      : no level in current chain meets the target\n")
	}
}

type BenchPolyEvalBreakdown struct {
	BuildBasis           time.Duration
	SquareXRHalf         time.Duration
	BuildGrouped         time.Duration
	ParallelLT           time.Duration
	LTMatrixBuild        time.Duration
	LTDecompose          time.Duration
	LTBabyRotations      time.Duration
	LTGiantRotations     time.Duration
	LTPlaintextCipherMul time.Duration
	LTFirstStageOther    time.Duration
	LTSecondStage        time.Duration
	LTPostProcess        time.Duration
	LTPostRescale        time.Duration
	LTResidual           time.Duration
	PointwiseMul         time.Duration
	RotateAndSum         time.Duration
	ComputeXD            time.Duration
	LeadingTerm          time.Duration
	FinalAdd             time.Duration
	PowerGen             time.Duration
	OuterCombine         time.Duration
}

type BenchPolyEvalTiming struct {
	Algorithm string
	Total     time.Duration
	Breakdown BenchPolyEvalBreakdown
}

type BenchDynamicSetupTiming struct {
	FunctionTable  time.Duration
	LUTBuild       time.Duration
	LWECiphertexts time.Duration
	PolyPrecompute time.Duration
	Total          time.Duration
}

type BenchOnlineTiming struct {
	Pack          time.Duration
	Poly          BenchPolyEvalTiming
	SlotToCoeff   time.Duration
	KeySwitch     time.Duration
	Correction    time.Duration
	ModSwitch     time.Duration
	SampleExtract time.Duration
	Total         time.Duration
}

type BenchRunSummary struct {
	Run          int
	FuncSeed     int64
	LWENoiseSeed int64
	LWEASeed     int64
	MsgSeed      int64
	FuncDesc     string
	Dynamic      BenchDynamicSetupTiming
	Online       BenchOnlineTiming
	NoiseDiffs   []int64
	NoiseMean    float64
	NoiseStd     float64
	NoiseMaxAbs  int64
	PolyPlainOK  bool
	CoeffOK      bool
	DecodeOK     bool
	Correct      bool
}

func polyNoiseTraceActiveForCurrentContext(m int) bool {
	return globalPolyNoiseTracer != nil && globalPolyNoiseTracer.Enabled &&
		len(globalPolyNoiseBase) == m &&
		len(globalPolyNoiseCoeffLower) == m &&
		len(globalPolyNoiseLeadCoeffs) == m
}

func setBenchLTBreakdown(bd *BenchPolyEvalBreakdown, total, matrixBuild, postRescale time.Duration, ltTiming AlgoTimings) {
	if bd == nil {
		return
	}
	bd.ParallelLT = total
	bd.LTMatrixBuild = matrixBuild
	bd.LTDecompose = ltTiming.FirstStageDecompose
	bd.LTBabyRotations = ltTiming.BabyRotations
	bd.LTGiantRotations = ltTiming.GiantRotations
	bd.LTPlaintextCipherMul = ltTiming.PlaintextCipherMul
	firstOther := ltTiming.FirstStageEval - ltTiming.BabyRotations - ltTiming.GiantRotations - ltTiming.PlaintextCipherMul
	if firstOther < 0 {
		firstOther = 0
	}
	bd.LTFirstStageOther = firstOther
	bd.LTSecondStage = ltTiming.SecondStageEval
	bd.LTPostProcess = ltTiming.PostProcess
	bd.LTPostRescale = postRescale
	tracked := matrixBuild + ltTiming.FirstStageDecompose + ltTiming.BabyRotations + ltTiming.GiantRotations + ltTiming.PlaintextCipherMul + firstOther + ltTiming.SecondStageEval + ltTiming.PostProcess + postRescale
	if total > tracked {
		bd.LTResidual = total - tracked
	}
}

func benchAllZeroUint64(v []uint64) bool {
	for _, x := range v {
		if x != 0 {
			return false
		}
	}
	return true
}

func buildRandomFunctionTable(p uint64, seed int64) []uint64 {
	rng := rand.New(rand.NewSource(seed))
	tab := make([]uint64, p)
	for i := range tab {
		tab[i] = uint64(rng.Int63n(int64(p)))
	}
	return tab
}

func buildFunctionTableWithSeed(p uint64, funcSpec, inlineTable, filePath string, randomSeed int64) ([]uint64, string, error) {
	var vals []uint64
	var err error
	if strings.TrimSpace(filePath) != "" {
		vals, err = readUintTableFromFile(filePath)
		if err != nil {
			return nil, "", fmt.Errorf("failed to read -func-file: %w", err)
		}
	} else if strings.TrimSpace(inlineTable) != "" {
		vals, err = parseUintTableFlexible(inlineTable)
		if err != nil {
			return nil, "", fmt.Errorf("failed to parse -func-table: %w", err)
		}
	}
	if len(vals) > 0 {
		if len(vals) != int(p) {
			return nil, "", fmt.Errorf("function table length must be exactly p=%d, got %d", p, len(vals))
		}
		for i := range vals {
			vals[i] %= p
		}
		return vals, "explicit lookup table", nil
	}

	tab := make([]uint64, p)
	spec := strings.ToLower(strings.TrimSpace(funcSpec))
	desc := spec
	switch {
	case spec == "", spec == "identity":
		for i := range tab {
			tab[i] = uint64(i)
		}
		desc = "identity"
	case spec == "square":
		for i := range tab {
			x := uint64(i)
			tab[i] = (x * x) % p
		}
		desc = "square"
	case spec == "cube":
		for i := range tab {
			x := uint64(i)
			tab[i] = (x * x % p) * x % p
		}
		desc = "cube"
	case spec == "neg":
		for i := range tab {
			if i == 0 {
				tab[i] = 0
			} else {
				tab[i] = p - uint64(i)
			}
		}
		desc = "negation"
	case strings.HasPrefix(spec, "affine:"):
		a, b, err := parseAffineSpec(spec)
		if err != nil {
			return nil, "", err
		}
		for i := range tab {
			tab[i] = (a*uint64(i) + b) % p
		}
		desc = fmt.Sprintf("affine map %d*x+%d mod %d", a, b, p)
	case spec == "random":
		tab = buildRandomFunctionTable(p, randomSeed)
		desc = fmt.Sprintf("random function with seed %d", randomSeed)
	default:
		return nil, "", fmt.Errorf("unsupported -func %q: expected random|identity|square|cube|neg|affine:a,b or provide -func-table/-func-file", funcSpec)
	}
	return tab, desc, nil
}

func benchPolyEvalSparsePow2Alg5Precomp(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, pre *PreprocessedPolyEval, dropBeforeLT bool, ltDropLevel, ltPostLevel int) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
	var tm BenchPolyEvalTiming
	start := time.Now()
	if pre == nil || pre.OnesRMon == nil || pre.OnesSMon == nil || pre.LT == nil || pre.LeadPT == nil {
		return nil, tm, errors.New("missing preprocessed data for Algorithm 5")
	}
	mod := params.PlaintextModulus()
	r := params.MaxSlots() / pre.M
	s := pre.D / r
	traceEnabled := polyNoiseTraceActiveForCurrentContext(pre.M)
	base := globalPolyNoiseBase
	coeffsLower := globalPolyNoiseCoeffLower
	leadCoeffsTrace := globalPolyNoiseLeadCoeffs

	st := time.Now()
	ctP, ctHalf, _, err := MonomialGenExtraPrecomp(params, eval, ct, pre.M, pre.OnesRMon, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on r failed: %w", err)
	}
	if ctHalf == nil {
		return nil, tm, errors.New("missing x^(r/2) ciphertext")
	}
	tm.Breakdown.BuildBasis = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: basis (1,x,...,x^{r-1})", ctP, monomialGenReferenceSlots(base, buildAllOnesCoeffs(pre.M, r), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(r/2)", ctHalf, repeatVector(powVectorMod(base, r/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctR, err := mulCtRelinRescale(eval, ctHalf, ctHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(r/2) to x^r failed: %w", err)
	}
	tm.Breakdown.SquareXRHalf = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: x^r", ctR, repeatVector(powVectorMod(base, r, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctG, ctDHalf, _, err := MonomialGenExtraPrecomp(params, eval, ctR, pre.M, pre.OnesSMon, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on x^r failed: %w", err)
	}
	if ctDHalf == nil {
		return nil, tm, errors.New("missing x^(d/2) ciphertext from the second power stage")
	}
	tm.Breakdown.BuildGrouped = time.Since(st)
	if traceEnabled {
		xR := powVectorMod(base, r, mod)
		if err := maybeTracePolyNoise("poly/LUT alg5: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(pre.M, s), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, pre.D/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	if ltDropLevel >= 0 {
		if ctP.Level() > ltDropLevel {
			eval.DropLevel(ctP, ctP.Level()-ltDropLevel)
		}
	} else if dropBeforeLT && ctP.Level() > ctG.Level() {
		eval.DropLevel(ctP, ctP.Level()-ctG.Level())
	}

	ltStart := time.Now()
	ctY, ltTiming, err := parallelLT3BSGSHoistedPrecomp(params, eval, ctP, pre.LT, pre.M, s, r)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (before post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	var ltPostRescale time.Duration
	if ltPostLevel >= 0 && ctY.Level() > ltPostLevel {
		stRes := time.Now()
		if err := rescaleCiphertextToLevel(eval, ctY, ltPostLevel); err != nil {
			return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
		}
		ltPostRescale = time.Since(stRes)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	setBenchLTBreakdown(&tm.Breakdown, time.Since(ltStart), 0, ltPostRescale, ltTiming)

	st = time.Now()
	alignCiphertextLevels(eval, ctY, ctG)
	ctCollapsed, err := mulCtRelinRescale(eval, ctY, ctG)
	if err != nil {
		return nil, tm, fmt.Errorf("pointwise multiplication y*g failed: %w", err)
	}
	tm.Breakdown.PointwiseMul = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: collapsed blocks y*g", ctCollapsed, expectedAlg5CollapsedSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctBase, err := sparseRotateAndSum(params, eval, ctCollapsed, pre.M, s)
	if err != nil {
		return nil, tm, err
	}
	tm.Breakdown.RotateAndSum = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctPowD, err := mulCtRelinRescale(eval, ctDHalf, ctDHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
	}
	tm.Breakdown.ComputeXD = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: x^d", ctPowD, repeatVector(powVectorMod(base, pre.D, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctLead, err := mulOperandRescale(eval, ctPowD, pre.LeadPT)
	if err != nil {
		return nil, tm, fmt.Errorf("leading x^d plaintext-ciphertext multiplication failed: %w", err)
	}
	tm.Breakdown.LeadingTerm = time.Since(st)
	if traceEnabled {
		leadVals := make([]uint64, len(base))
		for i := range leadVals {
			leadVals[i] = mulMod(leadCoeffsTrace[i], powMod(base[i], uint64(pre.D), mod), mod)
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: leading term a_d*x^d", ctLead, repeatVector(leadVals, r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	baseCopy := ctBase.CopyNew()
	alignCiphertextLevels(eval, baseCopy, ctLead)
	ctOut, err := eval.AddNew(baseCopy, ctLead)
	if err != nil {
		return nil, tm, fmt.Errorf("adding the leading x^d term failed: %w", err)
	}
	tm.Breakdown.FinalAdd = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: final F(x)", ctOut, repeatVector(fullPolyValues(base, coeffsLower, leadCoeffsTrace, pre.D, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	tm.Algorithm = "Algorithm 5 (degree d power-of-two wrapper, preprocessed plaintexts)"
	tm.Total = time.Since(start)
	return ctOut, tm, nil
}

func benchPolyEvalSparsePow2Alg5LargeBranch(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64, preLT *PreprocessedParallelLT3, dropBeforeLT bool, ltDropLevel, ltPostLevel int) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
	var tm BenchPolyEvalTiming
	start := time.Now()
	if len(coeffsLower) == 0 || len(coeffsLower[0]) == 0 {
		return nil, tm, errors.New("coeffsLower is empty")
	}
	d := len(coeffsLower[0])
	if !isPow2(d) {
		return nil, tm, fmt.Errorf("pow2-degree wrapper requires d=%d to be a power of two", d)
	}
	slots := params.MaxSlots()
	if slots%m != 0 {
		return nil, tm, fmt.Errorf("m=%d must divide MaxSlots=%d", m, slots)
	}
	r := slots / m
	if d <= r || d > r*r {
		return nil, tm, fmt.Errorf("Alg5 wrapper requires r < d <= r^2, got d=%d, r=%d", d, r)
	}
	if d%r != 0 {
		return nil, tm, fmt.Errorf("Alg5 wrapper requires r | d, got d=%d, r=%d", d, r)
	}
	s := d / r
	mod := params.PlaintextModulus()
	traceEnabled := polyNoiseTraceActiveForCurrentContext(m)
	base := globalPolyNoiseBase
	leadCoeffsTrace := globalPolyNoiseLeadCoeffs

	onesR := buildAllOnesCoeffs(m, r)
	onesS := buildAllOnesCoeffs(m, s)
	st := time.Now()
	ctP, ctHalf, _, err := MonomialGenExtra(params, eval, ct, m, onesR, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on r failed: %w", err)
	}
	if ctHalf == nil {
		return nil, tm, errors.New("missing x^(r/2) ciphertext")
	}
	tm.Breakdown.BuildBasis = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: basis (1,x,...,x^{r-1})", ctP, monomialGenReferenceSlots(base, buildAllOnesCoeffs(m, r), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^(r/2)", ctHalf, repeatVector(powVectorMod(base, r/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctR, err := mulCtRelinRescale(eval, ctHalf, ctHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(r/2) to x^r failed: %w", err)
	}
	tm.Breakdown.SquareXRHalf = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^r", ctR, repeatVector(powVectorMod(base, r, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctG, ctDHalf, _, err := MonomialGenExtra(params, eval, ctR, m, onesS, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on x^r failed: %w", err)
	}
	if ctDHalf == nil {
		return nil, tm, errors.New("missing x^(d/2) ciphertext from the second power stage")
	}
	tm.Breakdown.BuildGrouped = time.Since(st)
	if traceEnabled {
		xR := powVectorMod(base, r, mod)
		if err := maybeTracePolyNoise("poly/LUT alg5-large: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(m, s), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, d/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	if ltDropLevel >= 0 {
		if ctP.Level() > ltDropLevel {
			eval.DropLevel(ctP, ctP.Level()-ltDropLevel)
		}
	} else if dropBeforeLT && ctP.Level() > ctG.Level() {
		eval.DropLevel(ctP, ctP.Level()-ctG.Level())
	}

	var ctY *rlwe.Ciphertext
	var ltTiming AlgoTimings
	var ltMatrixBuild, ltPostRescale time.Duration
	ltStart := time.Now()
	if preLT != nil {
		ctY, ltTiming, err = parallelLT3BSGSHoistedPrecomp(params, eval, ctP, preLT, m, s, r)
	} else {
		stMatrix := time.Now()
		U := buildPatersonStockmeyerMatrixViews(coeffsLower, r)
		ltMatrixBuild = time.Since(stMatrix)
		ctY, ltTiming, err = parallelLT3BSGSHoistedViews(params, eval, ctP, U, m, s, r)
	}
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: ParallelLT output (before post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	if ltPostLevel >= 0 && ctY.Level() > ltPostLevel {
		stRes := time.Now()
		if err := rescaleCiphertextToLevel(eval, ctY, ltPostLevel); err != nil {
			return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
		}
		ltPostRescale = time.Since(stRes)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	setBenchLTBreakdown(&tm.Breakdown, time.Since(ltStart), ltMatrixBuild, ltPostRescale, ltTiming)

	st = time.Now()
	alignCiphertextLevels(eval, ctY, ctG)
	ctCollapsed, err := mulCtRelinRescale(eval, ctY, ctG)
	if err != nil {
		return nil, tm, fmt.Errorf("pointwise multiplication y*g failed: %w", err)
	}
	tm.Breakdown.PointwiseMul = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: collapsed blocks y*g", ctCollapsed, expectedAlg5CollapsedSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctBase, err := sparseRotateAndSum(params, eval, ctCollapsed, m, s)
	if err != nil {
		return nil, tm, err
	}
	tm.Breakdown.RotateAndSum = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	if benchAllZeroUint64(leadCoeffs) {
		if traceEnabled {
			if err := maybeTracePolyNoise("poly/LUT alg5-large: final F(x)", ctBase, repeatVector(fullPolyValues(base, coeffsLower, leadCoeffsTrace, d, mod), r)); err != nil {
				return nil, tm, err
			}
		}
		tm.Algorithm = "Algorithm 5 (large-parameter branch, view-based LT)"
		tm.Total = time.Since(start)
		return ctBase, tm, nil
	}

	st = time.Now()
	ctPowD, err := mulCtRelinRescale(eval, ctDHalf, ctDHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
	}
	tm.Breakdown.ComputeXD = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^d", ctPowD, repeatVector(powVectorMod(base, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctLead, err := mulPlainRescale(eval, ctPowD, sparsePackLeadingOrPanic(leadCoeffs, params.MaxSlots()))
	if err != nil {
		return nil, tm, fmt.Errorf("leading x^d plaintext-ciphertext multiplication failed: %w", err)
	}
	tm.Breakdown.LeadingTerm = time.Since(st)
	if traceEnabled {
		leadVals := make([]uint64, len(base))
		for i := range leadVals {
			leadVals[i] = mulMod(leadCoeffsTrace[i], powMod(base[i], uint64(d), mod), mod)
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-large: leading term a_d*x^d", ctLead, repeatVector(leadVals, r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	baseCopy := ctBase.CopyNew()
	alignCiphertextLevels(eval, baseCopy, ctLead)
	ctOut, err := eval.AddNew(baseCopy, ctLead)
	if err != nil {
		return nil, tm, fmt.Errorf("adding the leading x^d term failed: %w", err)
	}
	tm.Breakdown.FinalAdd = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: final F(x)", ctOut, repeatVector(fullPolyValues(base, coeffsLower, leadCoeffsTrace, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	tm.Algorithm = "Algorithm 5 (large-parameter branch, view-based LT)"
	tm.Total = time.Since(start)
	return ctOut, tm, nil
}

func benchPolyEvalSparsePow2Alg5(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64, dropBeforeLT bool, ltDropLevel, ltPostLevel int) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
	var tm BenchPolyEvalTiming
	start := time.Now()
	if len(coeffsLower) == 0 || len(coeffsLower[0]) == 0 {
		return nil, tm, errors.New("coeffsLower is empty")
	}
	d := len(coeffsLower[0])
	if !isPow2(d) {
		return nil, tm, fmt.Errorf("pow2-degree wrapper requires d=%d to be a power of two", d)
	}
	slots := params.MaxSlots()
	if slots%m != 0 {
		return nil, tm, fmt.Errorf("m=%d must divide MaxSlots=%d", m, slots)
	}
	r := slots / m
	if d <= r || d > r*r {
		return nil, tm, fmt.Errorf("Alg5 wrapper requires r < d <= r^2, got d=%d, r=%d", d, r)
	}
	if d%r != 0 {
		return nil, tm, fmt.Errorf("Alg5 wrapper requires r | d, got d=%d, r=%d", d, r)
	}
	s := d / r
	mod := params.PlaintextModulus()
	traceEnabled := polyNoiseTraceActiveForCurrentContext(m)
	base := globalPolyNoiseBase
	leadCoeffsTrace := globalPolyNoiseLeadCoeffs

	onesR := buildAllOnesCoeffs(m, r)
	onesS := buildAllOnesCoeffs(m, s)
	st := time.Now()
	ctP, ctHalf, _, err := MonomialGenExtra(params, eval, ct, m, onesR, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on r failed: %w", err)
	}
	if ctHalf == nil {
		return nil, tm, errors.New("missing x^(r/2) ciphertext")
	}
	tm.Breakdown.BuildBasis = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: basis (1,x,...,x^{r-1})", ctP, monomialGenReferenceSlots(base, buildAllOnesCoeffs(m, r), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(r/2)", ctHalf, repeatVector(powVectorMod(base, r/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctR, err := mulCtRelinRescale(eval, ctHalf, ctHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(r/2) to x^r failed: %w", err)
	}
	tm.Breakdown.SquareXRHalf = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: x^r", ctR, repeatVector(powVectorMod(base, r, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctG, ctDHalf, _, err := MonomialGenExtra(params, eval, ctR, m, onesS, true)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGen on x^r failed: %w", err)
	}
	if ctDHalf == nil {
		return nil, tm, errors.New("missing x^(d/2) ciphertext from the second power stage")
	}
	tm.Breakdown.BuildGrouped = time.Since(st)
	if traceEnabled {
		xR := powVectorMod(base, r, mod)
		if err := maybeTracePolyNoise("poly/LUT alg5: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(m, s), r, mod)); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, d/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	if ltDropLevel >= 0 {
		if ctP.Level() > ltDropLevel {
			eval.DropLevel(ctP, ctP.Level()-ltDropLevel)
		}
	} else if dropBeforeLT && ctP.Level() > ctG.Level() {
		eval.DropLevel(ctP, ctP.Level()-ctG.Level())
	}

	stMatrix := time.Now()
	U := buildPatersonStockmeyerMatrices(coeffsLower, r)
	ltMatrixBuild := time.Since(stMatrix)

	ltStart := time.Now()
	ctY, ltTiming, err := parallelLT3BSGSHoisted(params, eval, ctP, U, m, s, r)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (before post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	var ltPostRescale time.Duration
	if ltPostLevel >= 0 && ctY.Level() > ltPostLevel {
		stRes := time.Now()
		if err := rescaleCiphertextToLevel(eval, ctY, ltPostLevel); err != nil {
			return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
		}
		ltPostRescale = time.Since(stRes)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	setBenchLTBreakdown(&tm.Breakdown, ltMatrixBuild+time.Since(ltStart), ltMatrixBuild, ltPostRescale, ltTiming)

	st = time.Now()
	alignCiphertextLevels(eval, ctY, ctG)
	ctCollapsed, err := mulCtRelinRescale(eval, ctY, ctG)
	if err != nil {
		return nil, tm, fmt.Errorf("pointwise multiplication y*g failed: %w", err)
	}
	tm.Breakdown.PointwiseMul = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: collapsed blocks y*g", ctCollapsed, expectedAlg5CollapsedSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctBase, err := sparseRotateAndSum(params, eval, ctCollapsed, m, s)
	if err != nil {
		return nil, tm, err
	}
	tm.Breakdown.RotateAndSum = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctPowD, err := mulCtRelinRescale(eval, ctDHalf, ctDHalf)
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
	}
	tm.Breakdown.ComputeXD = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: x^d", ctPowD, repeatVector(powVectorMod(base, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctLead, err := mulPlainRescale(eval, ctPowD, sparsePackLeadingOrPanic(leadCoeffs, params.MaxSlots()))
	if err != nil {
		return nil, tm, fmt.Errorf("leading x^d plaintext-ciphertext multiplication failed: %w", err)
	}
	tm.Breakdown.LeadingTerm = time.Since(st)
	if traceEnabled {
		leadVals := make([]uint64, len(base))
		for i := range leadVals {
			leadVals[i] = mulMod(leadCoeffsTrace[i], powMod(base[i], uint64(d), mod), mod)
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: leading term a_d*x^d", ctLead, repeatVector(leadVals, r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	baseCopy := ctBase.CopyNew()
	alignCiphertextLevels(eval, baseCopy, ctLead)
	ctOut, err := eval.AddNew(baseCopy, ctLead)
	if err != nil {
		return nil, tm, fmt.Errorf("adding the leading x^d term failed: %w", err)
	}
	tm.Breakdown.FinalAdd = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: final F(x)", ctOut, repeatVector(fullPolyValues(base, coeffsLower, leadCoeffsTrace, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	tm.Algorithm = "Algorithm 5 (degree d power-of-two wrapper, no precomputed plaintexts)"
	tm.Total = time.Since(start)
	return ctOut, tm, nil
}

func benchPolyEvalSingleSlotDirectPrecomp(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, pre *PreprocessedPolyEval) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
	var tm BenchPolyEvalTiming
	start := time.Now()
	if pre == nil || pre.LeadPT == nil || pre.LowerMon == nil {
		return nil, tm, errors.New("missing preprocessed data for the m=1 direct path")
	}
	mod := params.PlaintextModulus()
	r := params.MaxSlots() / pre.M
	traceEnabled := polyNoiseTraceActiveForCurrentContext(pre.M)
	base := globalPolyNoiseBase
	coeffsLower := globalPolyNoiseCoeffLower
	leadCoeffsTrace := globalPolyNoiseLeadCoeffs

	st := time.Now()
	wantExtra := pre.D > 1
	ctLowerPacked, ctHalf, _, err := MonomialGenExtraPrecomp(params, eval, ct, pre.M, pre.LowerMon, wantExtra)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGenExtraPrecomp for the m=1 direct path failed: %w", err)
	}
	tm.Breakdown.BuildBasis = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: monomial lower packed", ctLowerPacked, monomialGenReferenceSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
		if ctHalf != nil {
			if err := maybeTracePolyNoise("poly/LUT alg5-m1: x^(d/2)", ctHalf, repeatVector(powVectorMod(base, pre.D/2, mod), r)); err != nil {
				return nil, tm, err
			}
		}
	}

	st = time.Now()
	ctBase, err := sparseRotateAndSum(params, eval, ctLowerPacked, pre.M, pre.D)
	if err != nil {
		return nil, tm, err
	}
	tm.Breakdown.RotateAndSum = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	var ctPowD *rlwe.Ciphertext
	if pre.D == 1 {
		ctPowD = ct.CopyNew()
	} else {
		if ctHalf == nil {
			return nil, tm, errors.New("missing x^(d/2) ciphertext for leading term")
		}
		st = time.Now()
		ctPowD, err = mulCtRelinRescale(eval, ctHalf, ctHalf)
		if err != nil {
			return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
		}
		tm.Breakdown.ComputeXD = time.Since(st)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: x^d", ctPowD, repeatVector(powVectorMod(base, pre.D, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctLead, err := mulOperandRescale(eval, ctPowD, pre.LeadPT)
	if err != nil {
		return nil, tm, fmt.Errorf("leading x^d plaintext-ciphertext multiplication failed: %w", err)
	}
	tm.Breakdown.LeadingTerm = time.Since(st)
	if traceEnabled {
		leadVals := make([]uint64, len(base))
		for i := range leadVals {
			leadVals[i] = mulMod(leadCoeffsTrace[i], powMod(base[i], uint64(pre.D), mod), mod)
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: leading term a_d*x^d", ctLead, repeatVector(leadVals, r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	baseCopy := ctBase.CopyNew()
	alignCiphertextLevels(eval, baseCopy, ctLead)
	ctOut, err := eval.AddNew(baseCopy, ctLead)
	if err != nil {
		return nil, tm, fmt.Errorf("adding the leading x^d term failed: %w", err)
	}
	tm.Breakdown.FinalAdd = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: final F(x)", ctOut, repeatVector(fullPolyValues(base, coeffsLower, leadCoeffsTrace, pre.D, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	tm.Algorithm = "Algorithm 5 (m=1 direct path, preprocessed plaintexts)"
	tm.Total = time.Since(start)
	return ctOut, tm, nil
}

func benchPolyEvalSingleSlotDirect(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
	var tm BenchPolyEvalTiming
	start := time.Now()
	if m != 1 {
		return nil, tm, fmt.Errorf("the direct path is only valid for m=1, got m=%d", m)
	}
	if len(coeffsLower) == 0 || len(coeffsLower[0]) == 0 {
		return nil, tm, errors.New("coeffsLower is empty")
	}
	d := len(coeffsLower[0])
	mod := params.PlaintextModulus()
	r := params.MaxSlots() / m
	traceEnabled := polyNoiseTraceActiveForCurrentContext(m)
	base := globalPolyNoiseBase
	leadCoeffsTrace := globalPolyNoiseLeadCoeffs

	st := time.Now()
	wantExtra := d > 1
	ctLowerPacked, ctHalf, _, err := MonomialGenExtra(params, eval, ct, m, coeffsLower, wantExtra)
	if err != nil {
		return nil, tm, fmt.Errorf("MonomialGenExtra for the m=1 direct path failed: %w", err)
	}
	tm.Breakdown.BuildBasis = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: monomial lower packed", ctLowerPacked, monomialGenReferenceSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
		if ctHalf != nil {
			if err := maybeTracePolyNoise("poly/LUT alg5-m1: x^(d/2)", ctHalf, repeatVector(powVectorMod(base, d/2, mod), r)); err != nil {
				return nil, tm, err
			}
		}
	}

	st = time.Now()
	ctBase, err := sparseRotateAndSum(params, eval, ctLowerPacked, m, d)
	if err != nil {
		return nil, tm, err
	}
	tm.Breakdown.RotateAndSum = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	var ctPowD *rlwe.Ciphertext
	if d == 1 {
		ctPowD = ct.CopyNew()
	} else {
		if ctHalf == nil {
			return nil, tm, errors.New("missing x^(d/2) ciphertext for leading term")
		}
		st = time.Now()
		ctPowD, err = mulCtRelinRescale(eval, ctHalf, ctHalf)
		if err != nil {
			return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
		}
		tm.Breakdown.ComputeXD = time.Since(st)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: x^d", ctPowD, repeatVector(powVectorMod(base, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctLead, err := mulPlainRescale(eval, ctPowD, sparsePackLeadingOrPanic(leadCoeffs, params.MaxSlots()))
	if err != nil {
		return nil, tm, fmt.Errorf("leading x^d plaintext-ciphertext multiplication failed: %w", err)
	}
	tm.Breakdown.LeadingTerm = time.Since(st)
	if traceEnabled {
		leadVals := make([]uint64, len(base))
		for i := range leadVals {
			leadVals[i] = mulMod(leadCoeffsTrace[i], powMod(base[i], uint64(d), mod), mod)
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: leading term a_d*x^d", ctLead, repeatVector(leadVals, r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	baseCopy := ctBase.CopyNew()
	alignCiphertextLevels(eval, baseCopy, ctLead)
	ctOut, err := eval.AddNew(baseCopy, ctLead)
	if err != nil {
		return nil, tm, fmt.Errorf("adding the leading x^d term failed: %w", err)
	}
	tm.Breakdown.FinalAdd = time.Since(st)
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-m1: final F(x)", ctOut, repeatVector(fullPolyValues(base, coeffsLower, leadCoeffsTrace, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	tm.Algorithm = "Algorithm 5 (m=1 direct path, no precomputed plaintexts)"
	tm.Total = time.Since(start)
	return ctOut, tm, nil
}

func benchAvgDuration(total time.Duration, runs int) time.Duration {
	if runs <= 0 {
		return 0
	}
	return total / time.Duration(runs)
}

func main() {
	NFlag := flag.Int("N", 32, "BFV ring degree / slot count N (power of two)")
	mFlag := flag.Int("m", 4, "number of logical messages m packed sparsely into the BFV slots")
	nFlag := flag.Int("n", 8, "target LWE dimension n = len(a) = len(s); independent of the sparse input length m")
	dFlag := flag.Int("d", 65535, "target polynomial degree d; if d=65536, use the 9bit power-of-two path. If d>65536, use the d+1 power-of-two path")
	pFlag := flag.Uint64("p", 512, "message modulus p for the LWE-style encoded slot values")
	TFlag := flag.Uint64("T", 65537, "BFV plaintext modulus T; must be prime and satisfy T = 2N*k + 1")
	logQFlag := flag.String("logq", "", "comma-separated LogQ bit sizes")
	logPFlag := flag.String("logp", "", "comma-separated LogP bit sizes")
	msgFlag := flag.String("msg", "", "comma-separated plaintext messages m_i in Z_p of length m")
	randomMsgFlag := flag.Bool("random-msg", false, "use a random message vector in Z_p when -msg is not provided")
	msgSeedFlag := flag.Int64("msg-seed", 12345, "random seed used for the plaintext messages when -random-msg is set")
	noiseSigmaFlag := flag.Float64("noise-sigma", 3.2, "standard deviation of the truncated discrete Gaussian noise e_i")
	noiseSeedFlag := flag.Int64("noise-seed", 54321, "random seed used for the slot noise e_i")
	lweASeedFlag := flag.Int64("lwe-a-seed", 314159, "random seed used for the public LWE a_i vectors")
	funcSpecFlag := flag.String("func", "random", "function f: random|identity|square|cube|neg|affine:a,b|table")
	funcTableFlag := flag.String("func-table", "", "comma-separated lookup-table values for f over Z_p")
	funcFileFlag := flag.String("func-file", "", "path to a text file containing p lookup-table values for f")
	funcSeedFlag := flag.Int64("func-seed", 20260402, "base seed used when random functions are generated")
	secretFlag := flag.String("secret", "", "optional ternary LWE secret vector of length n, entries in {-1,0,1}")
	secretSeedFlag := flag.Int64("secret-seed", 67890, "random seed used for the LWE secret when -secret is not provided")
	dropBeforeLTFlag := flag.Bool("drop-before-lt", true, "for Algorithm 5: drop the level of ctP before ParallelLT so that its output matches ctG level")
	ltDropLevelFlag := flag.Int("lt-drop-level", -1, "drop level before ParallelLT; -1 keeps existing behavior")
	ltPostLevelFlag := flag.Int("lt-post-level", 2, "post-ParallelLT rescale target level; -1 disables")
	alg5LTDropLevelFlag := flag.Int("alg5-lt-drop-levels", -999, "alias for Algorithm 5 LT drop level")
	alg5LTPostLevelFlag := flag.Int("alg5-lt-post-levels", -999, "alias for Algorithm 5 LT post-rescale target level")
	ltPrecomputeTermMasksFlag := flag.Bool("lt-precompute-term-masks", false, "for the large-parameter Algorithm 5 branch, precompute LT plaintext term masks / shifted masks")
	polyLTBabyStepsFlag := flag.Int("poly-lt-baby-steps", -1, "manual baby-step count g for the polynomial-evaluation LT BSGS split; <=0 uses automatic sqrt split")
	polyLTGiantStepsFlag := flag.Int("poly-lt-giant-steps", -1, "manual giant-step count b for the polynomial-evaluation LT BSGS split; <=0 uses automatic sqrt split")
	polyPrecomputeFlag := flag.Bool("poly-precompute-pt", false, "pre-encode polynomial-evaluation plaintexts for Algorithm 5; default false to save memory")
	gammaCompFlag := flag.Bool("gamma-compensate", true, "apply the gamma^{-1} correction before external modulus switching")
	scaleCompFlag := flag.Bool("scale-compensate", true, "apply the inverse of the SlotToCoeff ciphertext scale modulo T before BFV modulus switching")
	depthSlackFlag := flag.Int("depth-slack", 0, "adjust the automatic required-depth estimate; negative values relax the pre-check")
	polyNoiseTraceFlag := flag.Bool("poly-noise-trace", false, "print exact decrypted coefficient-noise for each major step inside the LUT polynomial evaluation")
	polyNoisePreviewFlag := flag.Int("poly-noise-preview", 8, "number of coefficient-noise samples shown for each polynomial-evaluation step")
	progressFlag := flag.Bool("progress", true, "print stage-by-stage progress logs during long runs")
	progressBlocksFlag := flag.Bool("progress-blocks", true, "print finer-grained progress inside polynomial evaluation blocks")
	gcEveryFlag := flag.Int("gc-every", 0, "after clearing per-run references, explicitly run Go GC every k runs; 0 disables explicit GC and relies on Go's automatic GC")
	freeOSMemoryFlag := flag.Bool("free-os-memory", false, "when an explicit run-level GC is triggered, also ask Go to return idle heap pages to the OS; useful on memory-limited Windows/VM runs but slower")
	memProgressFlag := flag.Bool("mem-progress", false, "print Go heap statistics before and after explicit run-level GC")
	leveledRotationKeysFlag := flag.Bool("leveled-rotation-keys", true, "generate rotation/Galois keys at the highest ciphertext level where each rotation is used; false keeps the previous full-level behavior")
	finalKSLevelPFlag := flag.Int("final-ks-level-p", -1, "LevelP for the final BFV key switch: -1 uses no P with a Q-only parameter view; 0 uses one P prime; higher values use more P primes")
	finalKSPow2BaseFlag := flag.Int("final-ks-pow2-base", 8, "base-2 decomposition bit width for the final key-switch key; <=0 disables bit decomposition")
	runsFlag := flag.Int("run", 1, "number of benchmark runs; key generation is done once and the online phase is repeated")
	flag.Parse()

	globalProgress = newProgressLogger(*progressFlag)
	globalProgressBlocks = *progressBlocksFlag
	globalPolyLTBabySteps = *polyLTBabyStepsFlag
	globalPolyLTGiantSteps = *polyLTGiantStepsFlag

	if *runsFlag < 1 {
		panic("-run must be at least 1")
	}

	N := *NFlag
	m := *mFlag
	nLWE := *nFlag
	userD := *dFlag
	if userD < 0 {
		panic(fmt.Sprintf("d=%d must be non-negative", userD))
	}
	use9BitPow2Mode := userD == 65536
	var d int
	if use9BitPow2Mode {
		d = userD
	} else {
		d = userD + 1
	}
	T := *TFlag
	var err error

	if !isPow2(N) {
		panic(fmt.Sprintf("N=%d must be a power of two", N))
	}
	if !isPow2(m) {
		panic(fmt.Sprintf("m=%d must be a power of two", m))
	}
	if !isPow2(d) {
		if use9BitPow2Mode {
			panic(fmt.Sprintf("in 9bit mode need d=%d to be a power of two", d))
		}
		panic(fmt.Sprintf("need d+1 to be a power of two, got d=%d and d+1=%d", userD, d))
	}
	if m > N/2 {
		panic(fmt.Sprintf("need m <= N/2, got m=%d, N=%d", m, N))
	}
	if N%m != 0 {
		panic(fmt.Sprintf("need m | N, got m=%d, N=%d", m, N))
	}
	if nLWE <= 0 || nLWE > N {
		panic(fmt.Sprintf("need 1 <= n <= N, got n=%d, N=%d", nLWE, N))
	}
	if T%(2*uint64(N)) != 1 {
		panic(fmt.Sprintf("plaintext modulus T=%d must satisfy T ≡ 1 (mod 2N=%d)", T, 2*N))
	}
	if !new(big.Int).SetUint64(T).ProbablyPrime(32) {
		panic(fmt.Sprintf("BFV plaintext modulus T=%d must be prime", T))
	}
	if use9BitPow2Mode {
		if !isPow2(int(T - 1)) {
			panic(fmt.Sprintf("9bit mode requires T-1 to be a power of two, got T=%d", T))
		}
		if d != int(T-1) {
			panic(fmt.Sprintf("9bit mode requires d = T-1 = %d, got d=%d", int(T-1), d))
		}
	} else {
		if userD < int(T-1) {
			panic(fmt.Sprintf("input degree d=%d is too small: the LUT polynomial has degree at most T-1=%d, so need d >= T-1", userD, int(T-1)))
		}
	}

	step := (N / 2) / m
	r := N / m
	logN := log2Pow2(N)
	singleSlotDirect := m == 1 && d <= r
	if !singleSlotDirect && (d <= r || d > r*r || d%r != 0) {
		panic(fmt.Sprintf("Algorithm 5 requires r < d <= r^2 and r|d unless m=1 uses the direct path, got d=%d, r=%d, m=%d", d, r, m))
	}
	var requiredDepth int
	if singleSlotDirect {
		requiredDepth = monomialConsumedDepth(d) + 2
	} else {
		requiredDepth, err = autoDepthForWrappedPolyEval(r, d)
		if err != nil {
			panic(err)
		}
	}
	requiredDepth++
	if m == 1 {
		requiredDepth--
	}
	requiredDepth += *depthSlackFlag
	if requiredDepth < 1 {
		requiredDepth = 1
	}

	var autoLiteral bfv.ParametersLiteral
	if strings.TrimSpace(*logQFlag) == "" || strings.TrimSpace(*logPFlag) == "" {
		prof, err := chooseAutoProfileForLogNDepth(logN, requiredDepth)
		if err != nil {
			panic(err)
		}
		autoLiteral, err = prof.BuildLiteral(requiredDepth, T)
		if err != nil {
			panic(err)
		}
	}
	var logQBits, logPBits []int
	if strings.TrimSpace(*logQFlag) == "" {
		logQBits = append([]int(nil), autoLiteral.LogQ...)
	} else {
		logQBits, err = parseBitList(*logQFlag)
		if err != nil {
			panic(fmt.Errorf("invalid -logq: %w", err))
		}
	}
	if strings.TrimSpace(*logPFlag) == "" {
		logPBits = append([]int(nil), autoLiteral.LogP...)
	} else {
		logPBits, err = parseBitList(*logPFlag)
		if err != nil {
			panic(fmt.Errorf("invalid -logp: %w", err))
		}
	}
	if len(logQBits)-1 < requiredDepth {
		panic(fmt.Sprintf("insufficient LogQ chain: MaxLevel=%d but this run with Algorithm 5, N=%d, m=%d, d=%d needs at least %d levels; pass a longer -logq or leave -logq empty for automatic selection", len(logQBits)-1, N, m, d, requiredDepth))
	}
	literal, err := chooseLiteral(logN, T, logQBits, logPBits)
	if err != nil {
		panic(err)
	}
	params, err := bfv.NewParametersFromLiteral(literal)
	if err != nil {
		panic(err)
	}
	if params.MaxSlots() != N {
		panic(fmt.Sprintf("constructed parameters have MaxSlots=%d, but requested N=%d", params.MaxSlots(), N))
	}
	if params.MaxLevel() < requiredDepth {
		panic(fmt.Sprintf("insufficient BFV depth: MaxLevel=%d but this run needs at least %d", params.MaxLevel(), requiredDepth))
	}

	alg5LTDropLevel := *ltDropLevelFlag
	alg5LTPostLevel := *ltPostLevelFlag
	if *alg5LTDropLevelFlag != -999 {
		alg5LTDropLevel = *alg5LTDropLevelFlag
	}
	if *alg5LTPostLevelFlag != -999 {
		alg5LTPostLevel = *alg5LTPostLevelFlag
	}
	if err := validateLTLevel(alg5LTDropLevel, params.MaxLevel(), "alg5-lt-drop-levels"); err != nil {
		panic(err)
	}
	if err := validateLTLevel(alg5LTPostLevel, params.MaxLevel(), "alg5-lt-post-levels"); err != nil {
		panic(err)
	}
	rp := params.GetRLWEParameters()

	pMsg := *pFlag
	if pMsg == 0 {
		panic("p must be positive")
	}
	if pMsg >= T {
		panic(fmt.Sprintf("need p < T, got p=%d, T=%d", pMsg, T))
	}
	alpha := T / pMsg
	if alpha == 0 {
		panic(fmt.Sprintf("alpha=floor(T/p)=0 for T=%d, p=%d", T, pMsg))
	}
	noiseBound := int64(T / (2 * pMsg))
	if noiseBound <= 0 {
		panic(fmt.Sprintf("invalid noise bound floor(T/(2p))=%d for T=%d, p=%d", noiseBound, T, pMsg))
	}

	msgParsed, err := parseVector(*msgFlag)
	if err != nil {
		panic(err)
	}
	var msgMod []uint64
	if len(msgParsed) == 0 {
		if *randomMsgFlag {
			msgMod = makeRandomMessages(m, pMsg, *msgSeedFlag)
		} else {
			msgMod = makeDefaultMessages(m, pMsg)
		}
	} else {
		if len(msgParsed) != m {
			panic(fmt.Sprintf("len(msg)=%d does not match m=%d", len(msgParsed), m))
		}
		msgMod = make([]uint64, m)
		for i, v := range msgParsed {
			msgMod[i] = toUintMod(v, pMsg)
		}
	}
	explicitMsgVector := len(msgParsed) != 0
	secretParse, err := parseVector(*secretFlag)
	if err != nil {
		panic(err)
	}
	var lweSecret []int64
	if len(secretParse) == 0 {
		lweSecret = randomTernary(nLWE, *secretSeedFlag)
	} else {
		if len(secretParse) != nLWE {
			panic(fmt.Sprintf("len(secret)=%d does not match n=%d", len(secretParse), nLWE))
		}
		if err := validateTernary(secretParse); err != nil {
			panic(err)
		}
		lweSecret = append([]int64(nil), secretParse...)
	}
	encoder := bfv.NewEncoder(params)

	oneTimeStart := time.Now()
	skipSlotToCoeff := m == 1
	var basisTime, diagTime, slotPTTime time.Duration
	var preSlotLT *PreprocessedBSGSPlaintexts
	rotationShifts := []int{}
	if !skipSlotToCoeff {
		buildBasisStart := time.Now()
		_, matrixUmod, _, err := buildBasisMatrixU(params, encoder, N, m, T)
		if err != nil {
			panic(err)
		}
		basisTime = time.Since(buildBasisStart)
		buildDiagStart := time.Now()
		diagMod, _ := buildRightMulDiagonals(matrixUmod, T)
		diagExtMod := make([][]uint64, m)
		for j := 0; j < m; j++ {
			diagExtMod[j] = repeatVector(diagMod[j], r)
		}
		diagTime = time.Since(buildDiagStart)
		preSlotPlainStart := time.Now()
		preSlotLT, err = preprocessSlotToCoeffBSGSPlaintexts(params, encoder, diagExtMod)
		if err != nil {
			panic(err)
		}
		slotPTTime = time.Since(preSlotPlainStart)
		rotationShifts = uniqueRotationShiftsForBSGS(m)
	}
	legacyGalSet := map[uint64]struct{}{}
	for _, shift := range rotationShifts {
		if shift != 0 {
			legacyGalSet[params.GaloisElementForColRotation(shift)] = struct{}{}
		}
	}
	polyGalEls, err := collectPolyEvalGaloisElements(params, m, d)
	if err != nil {
		panic(err)
	}
	for _, ge := range polyGalEls {
		legacyGalSet[ge] = struct{}{}
	}
	inputPackGalEls := requiredGaloisElementsForFinalSum(params, m, r)
	for _, ge := range inputPackGalEls {
		legacyGalSet[ge] = struct{}{}
	}
	legacyGalEls := make([]uint64, 0, len(legacyGalSet))
	for ge := range legacyGalSet {
		legacyGalEls = append(legacyGalEls, ge)
	}
	sort.Slice(legacyGalEls, func(i, j int) bool { return legacyGalEls[i] < legacyGalEls[j] })

	rotationPlan := newRotationKeyPlan()
	packRotationLevel := params.MaxLevel() - 1
	if err := addSparseRotateAndSumKeyUses(params, rotationPlan, m, r, packRotationLevel, "pack LWE->BFV"); err != nil {
		panic(err)
	}
	leadingTermEvaluated := use9BitPow2Mode || !useLargeAlg5Branch(N, m, d)
	polyLevelInfo, err := addPolyEvalRotationKeyUses(params, rotationPlan, m, d, *dropBeforeLTFlag, alg5LTDropLevel, alg5LTPostLevel, leadingTermEvaluated)
	if err != nil {
		panic(err)
	}
	if !skipSlotToCoeff {
		if err := addSlotToCoeffBSGSKeyUses(params, rotationPlan, m, polyLevelInfo.OutputLevel); err != nil {
			panic(err)
		}
	}
	addLegacyFullLevelFallbacks(params, rotationPlan, legacyGalEls, "legacy fallback")
	if !*leveledRotationKeysFlag {
		rotationPlan.ForceLevel(params.MaxLevel())
	}
	galEls := rotationPlan.GaloisElements()
	keygenStart := time.Now()
	kgen := rlwe.NewKeyGenerator(params)
	sk := kgen.GenSecretKeyNew()
	rlk := kgen.GenRelinearizationKeyNew(sk)
	gks, rotationKeyLevelStats, rotationKeySizeBytes, err := generateGaloisKeysFromPlan(params, kgen, sk, rotationPlan)
	if err != nil {
		panic(err)
	}
	evaluationKeys := rlwe.NewMemEvaluationKeySet(rlk, gks...)
	keygenTime := time.Since(keygenStart)
	enc := bfv.NewEncryptor(params, sk)
	dec := bfv.NewDecryptor(params, sk)
	evalPack := bfv.NewEvaluator(params, evaluationKeys, false)
	evalPoly := bfv.NewEvaluator(params, evaluationKeys, false)
	evalLT := bfv.NewEvaluator(params, evaluationKeys, false)
	secretBlockPrepStart := time.Now()
	secretBlockCTs, err := preprocessEncryptedSecretBlocks(params, encoder, enc, lweSecret, m)
	if err != nil {
		panic(err)
	}
	secretBlockPrepTime := time.Since(secretBlockPrepStart)
	secretBlockSizeBytes := sumCiphertextBinarySize(secretBlockCTs)
	finalKeySwitchLevelQ := 0
	finalKeySwitchLevelP := *finalKSLevelPFlag
	if finalKeySwitchLevelP < -1 {
		panic(fmt.Sprintf("-final-ks-level-p must be -1 or non-negative, got %d", finalKeySwitchLevelP))
	}
	if finalKeySwitchLevelP >= 0 && finalKeySwitchLevelP > params.MaxLevelP() {
		panic(fmt.Sprintf("-final-ks-level-p=%d exceeds MaxLevelP=%d", finalKeySwitchLevelP, params.MaxLevelP()))
	}
	finalKSEvalParams := params
	if finalKeySwitchLevelP == -1 {
		finalKSLiteral := bfv.ParametersLiteral{
			LogN:             logN,
			Q:                rp.Q(),
			PlaintextModulus: T,
		}
		finalKSEvalParams, err = bfv.NewParametersFromLiteral(finalKSLiteral)
		if err != nil {
			panic(fmt.Errorf("failed to build Q-only parameters for final key switch: %w", err))
		}
	}
	targetSecretStart := time.Now()
	skTargetBFV := buildTargetBFVSecretKey(finalKSEvalParams, lweSecret)
	targetSecretTime := time.Since(targetSecretStart)
	skInputFinalKS := sk
	if finalKeySwitchLevelP == -1 {
		skInputFinalKS, err = cloneSecretKeyQOnly(finalKSEvalParams, sk)
		if err != nil {
			panic(fmt.Errorf("failed to clone the BFV secret key into the Q-only final-KS parameters: %w", err))
		}
	}
	finalKSParams := rlwe.EvaluationKeyParameters{
		LevelQ: &finalKeySwitchLevelQ,
		LevelP: &finalKeySwitchLevelP,
	}
	if *finalKSPow2BaseFlag > 0 {
		finalKSPow2Base := *finalKSPow2BaseFlag
		finalKSParams.BaseTwoDecomposition = &finalKSPow2Base
	}
	evalKeyStart := time.Now()
	kgenFinalKS := rlwe.NewKeyGenerator(finalKSEvalParams)
	evkKS := kgenFinalKS.GenEvaluationKeyNew(skInputFinalKS, skTargetBFV, finalKSParams)
	evalKeyTime := time.Since(evalKeyStart)
	rlkSizeBytes := int64(rlk.BinarySize())
	evalKeySizeBytes := int64(evkKS.BinarySize())
	auxKeySizeBytes := rlkSizeBytes + rotationKeySizeBytes + evalKeySizeBytes
	extractEval := bfv.NewEvaluator(finalKSEvalParams, rlwe.NewMemEvaluationKeySet(nil), true)
	decTargetKS := bfv.NewDecryptor(finalKSEvalParams, skTargetBFV)
	oneTimeTotal := time.Since(oneTimeStart)

	fmt.Println("========== BFV Parameters ==========")
	fmt.Printf("N                         : %d\n", N)
	fmt.Printf("m                         : %d\n", m)
	fmt.Printf("n (LWE dimension)         : %d\n", nLWE)
	fmt.Printf("input degree d            : %d\n", userD)
	if use9BitPow2Mode {
		fmt.Printf("degree mode               : 9bit power-of-two path (d is a power of two)\n")
	} else {
		fmt.Printf("degree mode               : d+1 power-of-two path\n")
		fmt.Printf("internal eval degree      : %d\n", d)
	}
	fmt.Printf("poly-eval algorithm       : %s\n", PolyEvalAlg5)
	fmt.Printf("poly LT baby steps        : %s\n", formatPolyLTBSGSSetting(globalPolyLTBabySteps))
	fmt.Printf("poly LT giant steps       : %s\n", formatPolyLTBSGSSetting(globalPolyLTGiantSteps))
	fmt.Printf("plaintext modulus T       : %d\n", T)
	fmt.Printf("message modulus p         : %d\n", pMsg)
	fmt.Printf("alpha=floor(T/p)          : %d\n", alpha)
	fmt.Printf("MaxLevel                  : %d\n", params.MaxLevel())
	fmt.Printf("LogQ bits                 : %v\n", literal.LogQ)
	fmt.Printf("LogP bits                 : %v\n", literal.LogP)
	fmt.Printf("Q factors                 : %v\n", rp.Q())
	fmt.Printf("P factors                 : %v\n", rp.P())
	fmt.Println("====================================")
	fmt.Println()
	fmt.Println("---------- One-time preprocessing ----------")
	fmt.Printf("SlotToCoeff basis         : %v\n", basisTime)
	fmt.Printf("SlotToCoeff diagonals     : %v\n", diagTime)
	fmt.Printf("SlotToCoeff plaintexts    : %v\n", slotPTTime)
	fmt.Printf("key generation            : %v\n", keygenTime)
	fmt.Printf("encrypted secret blocks   : %v\n", secretBlockPrepTime)
	fmt.Printf("target secret build       : %v\n", targetSecretTime)
	fmt.Printf("evaluation-key generation : %v\n", evalKeyTime)
	fmt.Printf("poly-eval Galois keys     : %d\n", len(polyGalEls))
	fmt.Printf("SlotToCoeff rotations     : %d\n", len(rotationShifts))
	fmt.Printf("packing Galois keys       : %d\n", len(inputPackGalEls))
	fmt.Printf("distinct Galois keys total: %d\n", len(galEls))
	fmt.Printf("leveled rotation keys     : %v\n", *leveledRotationKeysFlag)
	fmt.Printf("rotation level plan       : pack=%d, polyPower=%d, polyGrouped=%d, polyLT-in=%d, polyLT-out=%d, final-sum=%d, poly-out=%d\n", packRotationLevel, polyLevelInfo.PowerLevel, polyLevelInfo.GroupedLevel, polyLevelInfo.LTInputLevel, polyLevelInfo.LTOutputLevel, polyLevelInfo.FinalSumLevel, polyLevelInfo.OutputLevel)
	fmt.Printf("rotation keys total size  : %s (%d bytes)\n", formatBytesIEC(rotationKeySizeBytes), rotationKeySizeBytes)
	for _, st := range rotationKeyLevelStats {
		fmt.Printf("  - LevelQ=%d (#Q=%d, logQ≈%d bits): %d keys, %s (%d bytes)\n", st.LevelQ, st.LevelQ+1, st.LogQBits, st.Count, formatBytesIEC(st.SizeBytes), st.SizeBytes)
	}
	fmt.Printf("relinearization key size  : %s (%d bytes)\n", formatBytesIEC(rlkSizeBytes), rlkSizeBytes)
	fmt.Printf("final key-switch key level: LevelQ=%d (#Q=%d, logQ≈%d bits), %s\n", finalKeySwitchLevelQ, finalKeySwitchLevelQ+1, finalKSEvalParams.RingQ().AtLevel(finalKeySwitchLevelQ).Modulus().BitLen(), formatLevelPForPrint(finalKSEvalParams, finalKeySwitchLevelP))
	fmt.Printf("final key-switch pow2 base: %s\n", formatPow2BaseForPrint(*finalKSPow2BaseFlag))
	if finalKeySwitchLevelP == -1 {
		fmt.Printf("final key-switch params   : Q-only parameter view, PCount=%d\n", finalKSEvalParams.PCount())
	}
	fmt.Printf("final key-switch key size : %s (%d bytes)\n", formatBytesIEC(evalKeySizeBytes), evalKeySizeBytes)
	fmt.Printf("auxiliary keys total size : %s (%d bytes)\n", formatBytesIEC(auxKeySizeBytes), auxKeySizeBytes)
	fmt.Printf("encrypted secret size     : %s (%d bytes)\n", formatBytesIEC(secretBlockSizeBytes), secretBlockSizeBytes)
	fmt.Printf("run memory cleanup        : clear per-run refs, gc-every=%d, free-os-memory=%v, mem-progress=%v\n", *gcEveryFlag, *freeOSMemoryFlag, *memProgressFlag)
	fmt.Printf("one-time preprocessing    : %v\n", oneTimeTotal)
	fmt.Println("--------------------------------------------")
	fmt.Println()

	perRunRandomFunction := *runsFlag > 1 && strings.TrimSpace(*funcTableFlag) == "" && strings.TrimSpace(*funcFileFlag) == ""
	perRunFreshLWE := *runsFlag > 1
	perRunFreshMessages := perRunFreshLWE && !explicitMsgVector && *randomMsgFlag
	runResults := make([]BenchRunSummary, 0, *runsFlag)
	var sumDynamic BenchDynamicSetupTiming
	var sumOnline BenchOnlineTiming
	allNoiseDiffs := make([]int64, 0, (*runsFlag)*m)
	allCorrect := true

	for runIdx := 0; runIdx < *runsFlag; runIdx++ {
		if *progressFlag {
			progressf("run %d/%d: dynamic setup", runIdx+1, *runsFlag)
		}
		var runRes BenchRunSummary
		runRes.Run = runIdx + 1
		runFuncSeed := *funcSeedFlag + int64(runIdx)
		runNoiseSeed := *noiseSeedFlag + int64(runIdx)
		runLWEASeed := *lweASeedFlag + int64(runIdx)
		runMsgSeed := *msgSeedFlag + int64(runIdx)
		runRes.FuncSeed = runFuncSeed
		runRes.LWENoiseSeed = runNoiseSeed
		runRes.LWEASeed = runLWEASeed
		runRes.MsgSeed = runMsgSeed
		var runMsgMod []uint64
		if explicitMsgVector {
			runMsgMod = append([]uint64(nil), msgMod...)
		} else if perRunFreshMessages {
			runMsgMod = makeRandomMessages(m, pMsg, runMsgSeed)
		} else {
			runMsgMod = append([]uint64(nil), msgMod...)
		}
		lweSetupStart := time.Now()
		runSlotNoiseCentered := sampleTruncatedDiscreteGaussian(m, *noiseSigmaFlag, noiseBound, runNoiseSeed)
		runInputLWECts, runXMod, err := generateRandomLWECiphertexts(runMsgMod, lweSecret, alpha, T, runSlotNoiseCentered, runLWEASeed)
		if err != nil {
			panic(err)
		}
		runRes.Dynamic.LWECiphertexts = time.Since(lweSetupStart)
		funcStart := time.Now()
		funcSpecForRun := *funcSpecFlag
		if perRunRandomFunction {
			funcSpecForRun = "random"
		}
		funcTable, funcDesc, err := buildFunctionTableWithSeed(pMsg, funcSpecForRun, *funcTableFlag, *funcFileFlag, runFuncSeed)
		if err != nil {
			panic(err)
		}
		runRes.FuncDesc = funcDesc
		runRes.Dynamic.FunctionTable = time.Since(funcStart)
		lutStart := time.Now()
		var lutCoeffMod []uint64
		if use9BitPow2Mode {
			lutCoeffMod, err = buildLUTPolynomialCoefficientsPow2Exact(T, pMsg, funcTable)
		} else {
			lutCoeffMod, err = buildLUTPolynomialCoefficientsGeneral(T, pMsg, funcTable)
		}
		if err != nil {
			panic(err)
		}
		runRes.Dynamic.LUTBuild = time.Since(lutStart)
		var coeffMod []uint64
		if use9BitPow2Mode {
			coeffMod = lutCoeffMod
		} else {
			coeffMod = make([]uint64, userD+1)
			copy(coeffMod, lutCoeffMod)
		}
		var coeffsLower [][]uint64
		var leadCoeffs []uint64
		if use9BitPow2Mode {
			coeffsLower = replicateSinglePolynomial(coeffMod[:d], m)
			leadCoeffs = repeatLeadingCoeff(coeffMod[d], m)
		} else {
			if useLargeAlg5Branch(N, m, d) {
				coeffsLower = replicateSinglePolynomialShared(coeffMod, m)
			} else {
				coeffsLower = replicateSinglePolynomial(coeffMod, m)
			}
			leadCoeffs = repeatLeadingCoeff(0, m)
		}
		polyPreStart := time.Now()
		var prePoly *PreprocessedPolyEval
		var preLargeAlg5LT *PreprocessedParallelLT3
		if !use9BitPow2Mode && useLargeAlg5Branch(N, m, d) {
			if *ltPrecomputeTermMasksFlag {
				UViews := buildPatersonStockmeyerMatrixViews(coeffsLower, r)
				preLargeAlg5LT, err = preprocessParallelLT3Views(params, encoder, UViews, m, d/r, r)
				if err != nil {
					panic(err)
				}
			}
		} else if *polyPrecomputeFlag {
			prePoly, err = preprocessPolyEvalPlaintexts(params, encoder, m, d, coeffsLower, leadCoeffs)
			if err != nil {
				panic(err)
			}
		}
		runRes.Dynamic.PolyPrecompute = time.Since(polyPreStart)
		runRes.Dynamic.Total = runRes.Dynamic.LWECiphertexts + runRes.Dynamic.FunctionTable + runRes.Dynamic.LUTBuild + runRes.Dynamic.PolyPrecompute

		targetDecodedFirstMMod := make([]uint64, m)
		targetEncodedFirstMMod := make([]uint64, m)
		for i := 0; i < m; i++ {
			targetDecodedFirstMMod[i] = funcTable[runMsgMod[i]] % pMsg
			targetEncodedFirstMMod[i] = mulMod(alpha, targetDecodedFirstMMod[i], T)
		}
		plainEvalFirstMMod := evalSinglePolyVector(runXMod, coeffMod, T)

		polyNoiseTracer := makePolyNoiseTracer(*polyNoiseTraceFlag, params, encoder, dec, *polyNoisePreviewFlag, false)
		setPolyNoiseTraceContext(polyNoiseTracer, runXMod, coeffsLower, leadCoeffs)

		packStart := time.Now()
		ctIn, err := homomorphicPackLWECiphertexts(params, evalPack, secretBlockCTs, runInputLWECts, m)
		if err != nil {
			panic(err)
		}
		runRes.Online.Pack = time.Since(packStart)
		// These LWE-side objects are no longer needed after the packing ciphertext is built.
		runInputLWECts = nil
		runSlotNoiseCentered = nil

		var ctEval *rlwe.Ciphertext
		polyStart := time.Now()
		if singleSlotDirect {
			if prePoly != nil {
				ctEval, runRes.Online.Poly, err = benchPolyEvalSingleSlotDirectPrecomp(params, evalPoly, ctIn, prePoly)
			} else {
				ctEval, runRes.Online.Poly, err = benchPolyEvalSingleSlotDirect(params, evalPoly, ctIn, m, coeffsLower, leadCoeffs)
			}
		} else if !use9BitPow2Mode && useLargeAlg5Branch(N, m, d) {
			ctEval, runRes.Online.Poly, err = benchPolyEvalSparsePow2Alg5LargeBranch(params, evalPoly, ctIn, m, coeffsLower, leadCoeffs, preLargeAlg5LT, *dropBeforeLTFlag, alg5LTDropLevel, alg5LTPostLevel)
		} else if prePoly != nil {
			ctEval, runRes.Online.Poly, err = benchPolyEvalSparsePow2Alg5Precomp(params, evalPoly, ctIn, prePoly, *dropBeforeLTFlag, alg5LTDropLevel, alg5LTPostLevel)
		} else {
			ctEval, runRes.Online.Poly, err = benchPolyEvalSparsePow2Alg5(params, evalPoly, ctIn, m, coeffsLower, leadCoeffs, *dropBeforeLTFlag, alg5LTDropLevel, alg5LTPostLevel)
		}
		if err != nil {
			panic(err)
		}
		_ = polyStart
		// Release large LUT/plaintext-preprocessing structures as soon as polynomial
		// evaluation has consumed them. This reduces the peak heap before SlotToCoeff,
		// final key-switching, and verification allocate their own temporary buffers.
		ctIn = nil
		coeffMod = nil
		lutCoeffMod = nil
		coeffsLower = nil
		leadCoeffs = nil
		prePoly = nil
		preLargeAlg5LT = nil
		if !*polyNoiseTraceFlag {
			runXMod = nil
		}
		var ctOut *rlwe.Ciphertext
		slotToCoeffStart := time.Now()
		if skipSlotToCoeff {
			ctOut = ctEval.CopyNew()
			runRes.Online.SlotToCoeff = 0
		} else {
			ctOut, _, err = HomomorphicSparseLinearTransformBSGSPrecomp(params, evalLT, ctEval, preSlotLT)
			if err != nil {
				panic(err)
			}
			runRes.Online.SlotToCoeff = time.Since(slotToCoeffStart)
		}
		ctEval = nil
		targetSecretBFV := skTargetBFV
		_ = targetSecretBFV
		keySwitchStart := time.Now()
		ctKeySwitchIn := ctOut
		if ctKeySwitchIn.Level() > finalKeySwitchLevelQ {
			ctKeySwitchIn = ctOut.CopyNew()
			// Important: extractEval is created in scale-invariant BFV mode for the final
			// key-switch / extraction path. In that mode Rescale returns without consuming
			// a level, which causes an infinite loop in rescaleCiphertextToLevel. The
			// pre-KS modulus switch must use the ordinary leveled evaluator.
			if err := rescaleCiphertextToLevel(evalLT, ctKeySwitchIn, finalKeySwitchLevelQ); err != nil {
				panic(fmt.Errorf("final key-switch input rescale to level %d failed: %w", finalKeySwitchLevelQ, err))
			}
		}
		if ctKeySwitchIn.Level() != finalKeySwitchLevelQ {
			panic(fmt.Errorf("final key-switch input level=%d, want level=%d", ctKeySwitchIn.Level(), finalKeySwitchLevelQ))
		}
		ctKS, err := extractEval.ApplyEvaluationKeyNew(ctKeySwitchIn, evkKS)
		if err != nil {
			panic(err)
		}
		runRes.Online.KeySwitch = time.Since(keySwitchStart)
		ringQ := finalKSEvalParams.RingQ().AtLevel(ctKS.Level())
		bigQ := ringQ.Modulus()
		gamma := negQInvModT(bigQ, T)
		gammaInv := modInverseU64(gamma, T)
		keySwitchedScaleModT := ctKS.Scale.Uint64() % T
		scaleInv := uint64(1)
		if *scaleCompFlag {
			if keySwitchedScaleModT == 0 {
				panic("ciphertext scale is 0 mod T; cannot invert for extraction correction")
			}
			scaleInv = modInverseU64(keySwitchedScaleModT, T)
		}
		combinedCorrection := uint64(1)
		if *gammaCompFlag {
			combinedCorrection = (combinedCorrection * gammaInv) % T
		}
		if *scaleCompFlag {
			combinedCorrection = (combinedCorrection * scaleInv) % T
		}
		ctExtract := ctKS
		if combinedCorrection != 1 {
			corrStart := time.Now()
			ctExtract, err = extractEval.MulNew(ctKS, combinedCorrection)
			if err != nil {
				panic(err)
			}
			runRes.Online.Correction = time.Since(corrStart)
		}
		modSwitchStart := time.Now()
		c0Big := polyToBigintCentered(ringQ, ctExtract.Value[0], ctExtract.IsNTT, ctExtract.IsMontgomery)
		c1Big := polyToBigintCentered(ringQ, ctExtract.Value[1], ctExtract.IsNTT, ctExtract.IsMontgomery)
		paperA := make([]*big.Int, params.N())
		paperB := make([]*big.Int, params.N())
		for i := 0; i < params.N(); i++ {
			paperB[i] = modPositiveBig(c0Big[i], bigQ)
			paperA[i] = modPositiveBig(new(big.Int).Neg(c1Big[i]), bigQ)
		}
		aQq := make([]uint64, params.N())
		bQq := make([]uint64, params.N())
		for i := 0; i < params.N(); i++ {
			aQq[i] = roundModSwitchBig(paperA[i], bigQ, T)
			bQq[i] = roundModSwitchBig(paperB[i], bigQ, T)
		}
		runRes.Online.ModSwitch = time.Since(modSwitchStart)
		extractStart := time.Now()
		positivePositions := collectPositiveSparsePositions(m, step)
		lweCts := sampleExtractSelected(aQq, bQq, positivePositions, nLWE, T)
		runRes.Online.SampleExtract = time.Since(extractStart)
		// External modulus switching buffers can be large; release them before the
		// coefficient verification step allocates decoded slot/coefficient arrays.
		c0Big = nil
		c1Big = nil
		paperA = nil
		paperB = nil
		aQq = nil
		bQq = nil
		ctKS = nil
		ctExtract = nil
		runRes.Online.Total = runRes.Online.Pack + runRes.Online.Poly.Total + runRes.Online.SlotToCoeff + runRes.Online.KeySwitch + runRes.Online.Correction + runRes.Online.ModSwitch + runRes.Online.SampleExtract

		coeffVerifyStart := time.Now()
		ptOut := dec.DecryptNew(ctOut)
		decryptedSlotsMod := make([]uint64, N)
		if err := encoder.Decode(ptOut, decryptedSlotsMod); err != nil {
			panic(err)
		}
		_, coeffsCenteredOut, err := encodeSlotsToPolynomialCoefficients(params, encoder, decryptedSlotsMod)
		if err != nil {
			panic(err)
		}
		positiveCoeffs := extractCoefficientsAtPositions(coeffsCenteredOut, positivePositions)
		negativeCoeffs := extractCoefficientsAtPositions(coeffsCenteredOut, collectNegativeSparsePositions(m, N, step))
		expectedPositive := centeredSlice(targetEncodedFirstMMod, T)
		expectedNegative := make([]int64, 0, m-1)
		for i := 1; i < m; i++ {
			expectedNegative = append(expectedNegative, -expectedPositive[i])
		}
		_ = coeffVerifyStart
		runRes.PolyPlainOK = equalUint64Slices(plainEvalFirstMMod, targetEncodedFirstMMod)
		runRes.CoeffOK = equalInt64Slices(positiveCoeffs, expectedPositive) && equalInt64Slices(negativeCoeffs, expectedNegative)
		lwePhaseMod := make([]uint64, len(lweCts))
		lweDiffs := make([]int64, len(lweCts))
		decodedMsgsModP := make([]uint64, len(lweCts))
		decodedMatches := 0
		maxAbsDiff := int64(0)
		for i := range lweCts {
			lwePhaseMod[i] = rawDecryptLWE(lweCts[i], lweSecret, T)
			lweDiffs[i] = centeredDiff(lwePhaseMod[i], targetEncodedFirstMMod[i], T)
			if abs64(lweDiffs[i]) > maxAbsDiff {
				maxAbsDiff = abs64(lweDiffs[i])
			}
			decodedMsgsModP[i] = decodePhaseToMessageModP(lwePhaseMod[i], alpha, pMsg, T)
			if decodedMsgsModP[i] == targetDecodedFirstMMod[i] {
				decodedMatches++
			}
		}
		runRes.NoiseDiffs = lweDiffs
		runRes.NoiseMean = meanInt64(lweDiffs)
		runRes.NoiseStd = stdDevInt64(lweDiffs)
		runRes.NoiseMaxAbs = maxAbsDiff
		runRes.DecodeOK = decodedMatches == len(lweCts)
		runRes.Correct = runRes.PolyPlainOK && runRes.CoeffOK && runRes.DecodeOK
		allCorrect = allCorrect && runRes.Correct
		allNoiseDiffs = append(allNoiseDiffs, lweDiffs...)
		runRes.NoiseDiffs = nil
		runResults = append(runResults, runRes)
		sumDynamic.LWECiphertexts += runRes.Dynamic.LWECiphertexts
		sumDynamic.FunctionTable += runRes.Dynamic.FunctionTable
		sumDynamic.LUTBuild += runRes.Dynamic.LUTBuild
		sumDynamic.PolyPrecompute += runRes.Dynamic.PolyPrecompute
		sumDynamic.Total += runRes.Dynamic.Total
		sumOnline.Pack += runRes.Online.Pack
		sumOnline.Poly.Total += runRes.Online.Poly.Total
		sumOnline.Poly.Breakdown.BuildBasis += runRes.Online.Poly.Breakdown.BuildBasis
		sumOnline.Poly.Breakdown.SquareXRHalf += runRes.Online.Poly.Breakdown.SquareXRHalf
		sumOnline.Poly.Breakdown.BuildGrouped += runRes.Online.Poly.Breakdown.BuildGrouped
		sumOnline.Poly.Breakdown.ParallelLT += runRes.Online.Poly.Breakdown.ParallelLT
		sumOnline.Poly.Breakdown.LTMatrixBuild += runRes.Online.Poly.Breakdown.LTMatrixBuild
		sumOnline.Poly.Breakdown.LTDecompose += runRes.Online.Poly.Breakdown.LTDecompose
		sumOnline.Poly.Breakdown.LTBabyRotations += runRes.Online.Poly.Breakdown.LTBabyRotations
		sumOnline.Poly.Breakdown.LTGiantRotations += runRes.Online.Poly.Breakdown.LTGiantRotations
		sumOnline.Poly.Breakdown.LTPlaintextCipherMul += runRes.Online.Poly.Breakdown.LTPlaintextCipherMul
		sumOnline.Poly.Breakdown.LTFirstStageOther += runRes.Online.Poly.Breakdown.LTFirstStageOther
		sumOnline.Poly.Breakdown.LTSecondStage += runRes.Online.Poly.Breakdown.LTSecondStage
		sumOnline.Poly.Breakdown.LTPostProcess += runRes.Online.Poly.Breakdown.LTPostProcess
		sumOnline.Poly.Breakdown.LTPostRescale += runRes.Online.Poly.Breakdown.LTPostRescale
		sumOnline.Poly.Breakdown.LTResidual += runRes.Online.Poly.Breakdown.LTResidual
		sumOnline.Poly.Breakdown.PointwiseMul += runRes.Online.Poly.Breakdown.PointwiseMul
		sumOnline.Poly.Breakdown.RotateAndSum += runRes.Online.Poly.Breakdown.RotateAndSum
		sumOnline.Poly.Breakdown.ComputeXD += runRes.Online.Poly.Breakdown.ComputeXD
		sumOnline.Poly.Breakdown.LeadingTerm += runRes.Online.Poly.Breakdown.LeadingTerm
		sumOnline.Poly.Breakdown.FinalAdd += runRes.Online.Poly.Breakdown.FinalAdd
		sumOnline.Poly.Breakdown.PowerGen += runRes.Online.Poly.Breakdown.PowerGen
		sumOnline.Poly.Breakdown.OuterCombine += runRes.Online.Poly.Breakdown.OuterCombine
		sumOnline.SlotToCoeff += runRes.Online.SlotToCoeff
		sumOnline.KeySwitch += runRes.Online.KeySwitch
		sumOnline.Correction += runRes.Online.Correction
		sumOnline.ModSwitch += runRes.Online.ModSwitch
		sumOnline.SampleExtract += runRes.Online.SampleExtract
		sumOnline.Total += runRes.Online.Total
		if *polyNoiseTraceFlag {
			polyNoiseTracer.Print()
		}
		clearPolyNoiseTraceContext()

		// Release objects that are only needed for this run.
		// Keep one-time keys, evaluators, and preprocessing alive for subsequent runs.
		runMsgMod = nil
		runSlotNoiseCentered = nil
		runInputLWECts = nil
		runXMod = nil
		funcTable = nil
		lutCoeffMod = nil
		coeffMod = nil
		coeffsLower = nil
		leadCoeffs = nil
		prePoly = nil
		preLargeAlg5LT = nil
		targetDecodedFirstMMod = nil
		targetEncodedFirstMMod = nil
		plainEvalFirstMMod = nil
		if polyNoiseTracer != nil {
			polyNoiseTracer.Entries = nil
		}
		polyNoiseTracer = nil
		ctIn = nil
		ctEval = nil
		ctOut = nil
		ctKS = nil
		ctExtract = nil
		c0Big = nil
		c1Big = nil
		paperA = nil
		paperB = nil
		aQq = nil
		bQq = nil
		lweCts = nil
		ptOut = nil
		decryptedSlotsMod = nil
		coeffsCenteredOut = nil
		positiveCoeffs = nil
		negativeCoeffs = nil
		expectedPositive = nil
		expectedNegative = nil
		lwePhaseMod = nil
		lweDiffs = nil
		decodedMsgsModP = nil

		maybeCollectRunGarbage(runIdx, *runsFlag, *gcEveryFlag, *freeOSMemoryFlag, *memProgressFlag)
	}

	fmt.Println("========== Per-run Summary ==========")
	for _, rr := range runResults {
		fmt.Printf("Run %d: func-seed=%d, lwe-noise-seed=%d, lwe-a-seed=%d, correct=%v, noise mean=%.4f, noise std=%.4f, max|.|=%d, online=%v\n", rr.Run, rr.FuncSeed, rr.LWENoiseSeed, rr.LWEASeed, rr.Correct, rr.NoiseMean, rr.NoiseStd, rr.NoiseMaxAbs, rr.Online.Total)
	}
	fmt.Println("=====================================")
	fmt.Println()

	fmt.Println("========== Aggregated Summary ==========")
	fmt.Printf("runs                       : %d\n", *runsFlag)
	fmt.Printf("all runs correct           : %v\n", allCorrect)
	fmt.Printf("average dynamic setup      : %v\n", benchAvgDuration(sumDynamic.Total, *runsFlag))
	fmt.Printf("  - fresh LWE ciphertexts  : %v\n", benchAvgDuration(sumDynamic.LWECiphertexts, *runsFlag))
	fmt.Printf("  - function table         : %v\n", benchAvgDuration(sumDynamic.FunctionTable, *runsFlag))
	fmt.Printf("  - LUT build              : %v\n", benchAvgDuration(sumDynamic.LUTBuild, *runsFlag))
	fmt.Printf("  - poly plaintext prep    : %v\n", benchAvgDuration(sumDynamic.PolyPrecompute, *runsFlag))
	fmt.Printf("average online total       : %v\n", benchAvgDuration(sumOnline.Total, *runsFlag))
	fmt.Printf("  - pack LWE->BFV          : %v\n", benchAvgDuration(sumOnline.Pack, *runsFlag))
	fmt.Printf("  - poly eval total        : %v\n", benchAvgDuration(sumOnline.Poly.Total, *runsFlag))
	fmt.Printf("    · build basis/powers   : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.BuildBasis, *runsFlag))
	fmt.Printf("    · square x^(r/2)       : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.SquareXRHalf, *runsFlag))
	fmt.Printf("    · build grouped powers : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.BuildGrouped, *runsFlag))
	fmt.Printf("    · ParallelLT           : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.ParallelLT, *runsFlag))
	fmt.Printf("      · LT matrix build    : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTMatrixBuild, *runsFlag))
	fmt.Printf("      · hoisted decompose  : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTDecompose, *runsFlag))
	fmt.Printf("      · baby rotations     : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTBabyRotations, *runsFlag))
	fmt.Printf("      · giant rotations    : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTGiantRotations, *runsFlag))
	fmt.Printf("      · pt-ct multiplies   : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTPlaintextCipherMul, *runsFlag))
	fmt.Printf("      · first-stage other  : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTFirstStageOther, *runsFlag))
	fmt.Printf("      · second stage       : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTSecondStage, *runsFlag))
	fmt.Printf("      · post-process       : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTPostProcess, *runsFlag))
	fmt.Printf("      · post-LT rescale    : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTPostRescale, *runsFlag))
	fmt.Printf("      · other residual     : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTResidual, *runsFlag))
	fmt.Printf("    · pointwise multiply   : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.PointwiseMul, *runsFlag))
	fmt.Printf("    · rotate-and-sum       : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.RotateAndSum, *runsFlag))
	fmt.Printf("    · x^d / power gen      : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.ComputeXD+sumOnline.Poly.Breakdown.PowerGen, *runsFlag))
	fmt.Printf("    · outer combine        : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.OuterCombine, *runsFlag))
	fmt.Printf("    · leading term         : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LeadingTerm, *runsFlag))
	fmt.Printf("    · final add            : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.FinalAdd, *runsFlag))
	fmt.Printf("  - SlotToCoeff            : %v\n", benchAvgDuration(sumOnline.SlotToCoeff, *runsFlag))
	fmt.Printf("  - BFV-side key switch    : %v\n", benchAvgDuration(sumOnline.KeySwitch, *runsFlag))
	fmt.Printf("  - correction mul         : %v\n", benchAvgDuration(sumOnline.Correction, *runsFlag))
	fmt.Printf("  - external mod switch    : %v\n", benchAvgDuration(sumOnline.ModSwitch, *runsFlag))
	fmt.Printf("  - sample extraction      : %v\n", benchAvgDuration(sumOnline.SampleExtract, *runsFlag))
	fmt.Printf("noise mean (all samples)   : %.4f\n", meanInt64(allNoiseDiffs))
	fmt.Printf("noise std dev (all samples): %.4f\n", stdDevInt64(allNoiseDiffs))
	maxAll := int64(0)
	for _, v := range allNoiseDiffs {
		if abs64(v) > maxAll {
			maxAll = abs64(v)
		}
	}
	fmt.Printf("max |noise| (all samples)  : %d\n", maxAll)
	fmt.Printf("total wall time            : %v\n", time.Since(globalProgress.Start))
	fmt.Println("========================================")
	_ = decTargetKS
}
