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

// Research prototype for BFV-based functional bootstrapping of LWE ciphertexts.
//
// The implementation follows the sparse-packing polynomial-evaluation strategy
// used in the accompanying paper "Functional Bootstrapping for a Single LWE
// Ciphertext with O~(1) Polynomial Multiplications". At a high level, the
// online path is:
//
//   1. homomorphically decrypt and sparsely pack LWE phases into a BFV/RLWE
//      ciphertext;
//   2. evaluate the LUT polynomial with the sparse Algorithm-5 path using
//      EvalPower, hoisted BSGS BatchLT, grouped powers, and RotateAndSum;
//   3. optionally convert the BFV/RLWE output back to LWE by sparse StC,
//      base-modulus key switching, sample extraction, and Qprime-to-T switching.
//
// The program is intended for reproducible research experiments. It is not
// production cryptographic software.

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

type LWEToRLWEStats struct {
	Blocks       int
	InnerPeriod  int
	CMults       int
	Rotations    int
	RowRotations int
	Additions    int
	Encryptions  int
	BSKBytes     int64
	Mode         string
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
var globalDeferPointwiseRescale bool

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
	// Algorithm 5 should consume log(d)+2 levels in the wrapped power-of-two
	// setting used here. With r and s=d/r, this is
	//   log(r) + (log(s)+1) + 1 = log(d)+2.
	// The default fast LT policy evaluates BatchLT directly at the grouped-powers
	// level, matching the original implementation. The optional extra-level LT
	// policy can still evaluate at ct2.Level()+1 and rescale back, but the output
	// level entering the line-5 product is planned by the same depth formula.
	consumed := log2Pow2(r) + monomialConsumedDepth(s) + 1
	return consumed, nil
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

func addSignedMod(x uint64, e int64, mod uint64) uint64 {
	x %= mod
	if e >= 0 {
		return (x + uint64(e)%mod) % mod
	}
	mag := uint64(-e) % mod
	if x >= mag {
		return x - mag
	}
	return x + mod - mag
}

func isLWEToRLWEInputMode(inputMode string) bool {
	mode := strings.ToLower(strings.TrimSpace(inputMode))
	switch mode {
	case "lwe", "lwe-phase", "lwe-pack", "lwe-to-rlwe", "lwe-rlwe", "step1", "lwe-step1", "lwe-homdec":
		return true
	default:
		return false
	}
}

type LWEToRLWEPackingPlan struct {
	Blocks      int
	InnerPeriod int
	Desc        string
}

func planLWEToRLWEStep1(N, m, n int) (LWEToRLWEPackingPlan, error) {
	if m <= 0 || N%m != 0 {
		return LWEToRLWEPackingPlan{}, fmt.Errorf("invalid sparse packing: N=%d, m=%d", N, m)
	}
	if n <= 0 {
		return LWEToRLWEPackingPlan{}, fmt.Errorf("LWE dimension must be positive, got n=%d", n)
	}
	if !isPow2(n) {
		return LWEToRLWEPackingPlan{}, fmt.Errorf("the Step-1 row-sum implementation assumes -lwe-n is a power of two, got %d", n)
	}
	r := N / m
	if !isPow2(r) {
		return LWEToRLWEPackingPlan{}, fmt.Errorf("r=N/m must be a power of two, got r=%d", r)
	}
	if r >= n {
		if r%n != 0 {
			return LWEToRLWEPackingPlan{}, fmt.Errorf("paper Step 1 in the r>=n branch requires n|r, got r=%d n=%d", r, n)
		}
		return LWEToRLWEPackingPlan{
			Blocks:      1,
			InnerPeriod: n,
			Desc:        fmt.Sprintf("r=%d >= n=%d: one encrypted repeated secret block, row-sum period n", r, n),
		}, nil
	}
	if n%r != 0 {
		return LWEToRLWEPackingPlan{}, fmt.Errorf("paper Step 1 in the n>r branch requires r|n, got n=%d r=%d", n, r)
	}
	return LWEToRLWEPackingPlan{
		Blocks:      n / r,
		InnerPeriod: r,
		Desc:        fmt.Sprintf("n=%d > r=%d: split LWE secret into %d encrypted blocks, row-sum period r", n, r, n/r),
	}, nil
}

func buildRLWEPhaseInputs(inputMode string, rawInput []int64, messageSpec, errorSpec string, m int, t, p uint64, inputSeed, errorSeed int64, errorSigma float64, errorBoundFlag int64) (x []uint64, messages []uint64, errors []int64, desc string, err error) {
	if m <= 0 {
		return nil, nil, nil, "", fmt.Errorf("m must be positive")
	}
	mode := strings.ToLower(strings.TrimSpace(inputMode))
	if mode == "" {
		mode = "phase"
	}

	parseMessages := func() ([]uint64, error) {
		parsed, err := parseVector(messageSpec)
		if err != nil {
			return nil, fmt.Errorf("invalid -message: %w", err)
		}
		if len(parsed) == 0 {
			return makeRandomMessages(m, p, inputSeed), nil
		}
		if len(parsed) != m {
			return nil, fmt.Errorf("len(message)=%d != m=%d", len(parsed), m)
		}
		out := make([]uint64, m)
		for i, v := range parsed {
			out[i] = toUintMod(v, p)
		}
		return out, nil
	}

	parseErrors := func(defaultBound int64) ([]int64, int64, error) {
		bound := errorBoundFlag
		if bound < 0 {
			bound = defaultBound
		}
		if bound <= 0 {
			return nil, 0, fmt.Errorf("input phase error bound must be positive, got %d", bound)
		}
		parsed, err := parseVector(errorSpec)
		if err != nil {
			return nil, 0, fmt.Errorf("invalid -phase-error: %w", err)
		}
		if len(parsed) != 0 {
			if len(parsed) != m {
				return nil, 0, fmt.Errorf("len(phase-error)=%d != m=%d", len(parsed), m)
			}
			out := make([]int64, m)
			for i, v := range parsed {
				if abs64(v) >= bound {
					return nil, 0, fmt.Errorf("phase-error[%d]=%d violates |e| < %d", i, v, bound)
				}
				out[i] = v
			}
			return out, bound, nil
		}
		return sampleTruncatedDiscreteGaussian(m, errorSigma, bound, errorSeed), bound, nil
	}

	switch mode {
	case "raw", "direct", "plain", "plaintext":
		if len(rawInput) == 0 {
			x = makeRandomMessages(m, t, inputSeed)
		} else {
			if len(rawInput) != m {
				return nil, nil, nil, "", fmt.Errorf("len(x)=%d != m=%d", len(rawInput), m)
			}
			x = make([]uint64, m)
			for i, v := range rawInput {
				x[i] = toUintMod(v, t)
			}
		}
		return x, nil, nil, fmt.Sprintf("raw/direct: encrypt supplied values x in Z_%d", t), nil

	case "phase-raw", "raw-phase":
		if len(rawInput) == 0 {
			return nil, nil, nil, "", fmt.Errorf("-input-mode=%s requires explicit -x phase values", mode)
		}
		if len(rawInput) != m {
			return nil, nil, nil, "", fmt.Errorf("len(x)=%d != m=%d", len(rawInput), m)
		}
		x = make([]uint64, m)
		for i, v := range rawInput {
			x[i] = toUintMod(v, t)
		}
		return x, nil, nil, fmt.Sprintf("phase-raw: encrypt explicit phase values x in Z_%d", t), nil

	case "phase", "delta", "delta-phase", "lwe-phase", "bfv-phase":
		if p == 0 || t < p {
			return nil, nil, nil, "", fmt.Errorf("phase input requires 0 < p <= T, got p=%d T=%d", p, t)
		}
		delta := t / p
		if delta == 0 {
			return nil, nil, nil, "", fmt.Errorf("Delta=floor(T/p)=0 for T=%d p=%d", t, p)
		}
		if len(rawInput) != 0 {
			return nil, nil, nil, "", fmt.Errorf("-input-mode=phase uses -message and -phase-error; use -input-mode=phase-raw if -x already contains phase values")
		}
		msgs, err := parseMessages()
		if err != nil {
			return nil, nil, nil, "", err
		}
		defaultBound := int64(delta / 2)
		if defaultBound <= 0 {
			defaultBound = 1
		}
		errs, bound, err := parseErrors(defaultBound)
		if err != nil {
			return nil, nil, nil, "", err
		}
		x = make([]uint64, m)
		for i := 0; i < m; i++ {
			x[i] = toUintMod(int64(delta)*int64(msgs[i])+errs[i], t)
		}
		desc = fmt.Sprintf("phase: encrypt x=Delta*m+e in Z_%d, p=%d, Delta=floor(T/p)=%d, |e|<%d", t, p, delta, bound)
		return x, msgs, errs, desc, nil
	default:
		return nil, nil, nil, "", fmt.Errorf("unknown -input-mode=%q; expected phase, phase-raw, or raw", inputMode)
	}
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

func buildStep1SecretAndMaskSlots(lweCts []LWECiphertext, secretMod []uint64, block int, plan LWEToRLWEPackingPlan, m, r int, mod uint64) (skSlots, maskSlots []uint64, err error) {
	if len(lweCts) != m {
		return nil, nil, fmt.Errorf("len(lweCts)=%d != m=%d", len(lweCts), m)
	}
	if len(secretMod) == 0 {
		return nil, nil, errors.New("empty LWE secret")
	}
	N := m * r
	skSlots = make([]uint64, N)
	maskSlots = make([]uint64, N)
	n := len(secretMod)
	for col := 0; col < r; col++ {
		var coord int
		if plan.Blocks == 1 && r >= n {
			coord = col % n
		} else {
			coord = block*r + col
		}
		if coord < 0 || coord >= n {
			return nil, nil, fmt.Errorf("internal Step1 coordinate out of range: coord=%d, n=%d", coord, n)
		}
		sVal := secretMod[coord] % mod
		for row := 0; row < m; row++ {
			if coord >= len(lweCts[row].A) {
				return nil, nil, fmt.Errorf("LWE ciphertext %d has dimension %d, but Step1 requested coordinate %d", row, len(lweCts[row].A), coord)
			}
			pos := col*m + row
			skSlots[pos] = sVal
			maskSlots[pos] = negateMod(lweCts[row].A[coord]%mod, mod)
		}
	}
	return skSlots, maskSlots, nil
}

func expectedForAddPlainSlots(ct *rlwe.Ciphertext, plain []uint64) []uint64 {
	av, ok := polyExpected(ct)
	if !ok || plain == nil || globalMulTracer == nil {
		return nil
	}
	if len(av) != len(plain) {
		return nil
	}
	out := make([]uint64, len(av))
	mod := globalMulTracer.Mod
	for i := range av {
		out[i] = (av[i] + plain[i]) % mod
	}
	return out
}

func mulPlainNoRescaleNamed(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand, expectedPlain []uint64, traceName string) (*rlwe.Ciphertext, error) {
	st := time.Now()
	out, err := eval.MulNew(ct, op)
	dur := time.Since(st)
	if err != nil {
		return nil, err
	}
	logMulTrace(mulTraceName("mulPlainNoRescale", traceName), "ct-pt-Step1", ct, nil, out, false, dur, expectedForCtPlainMul(ct, expectedPlain))
	return out, nil
}

func addCiphertextsStep1(eval *bfv.Evaluator, a, b *rlwe.Ciphertext, name string) (*rlwe.Ciphertext, error) {
	st := time.Now()
	out, err := eval.AddNew(a, b)
	dur := time.Since(st)
	if err != nil {
		return nil, err
	}
	logOpTrace(name, "add", a, b, out, false, dur, expectedForAdd(a, b))
	return out, nil
}

func sparseRotateAndSumStep1(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, baseLen, s int, stats *LWEToRLWEStats) (*rlwe.Ciphertext, error) {
	if s <= 1 {
		return ct, nil
	}
	if !isPow2(s) {
		return nil, fmt.Errorf("Step1 row-sum period s=%d must be a power of two", s)
	}
	r := params.MaxSlots() / baseLen
	if s > r {
		return nil, fmt.Errorf("Step1 row-sum period s=%d exceeds repetition factor r=%d", s, r)
	}
	ell := log2Pow2(s)
	h := ct.CopyNew()
	polyCopyExpected(ct, h)
	for i := 0; i < ell-1; i++ {
		shift := baseLen * (1 << i)
		stRot := time.Now()
		rot, err := eval.RotateColumnsNew(h, shift)
		durRot := time.Since(stRot)
		if err != nil {
			return nil, fmt.Errorf("Step1 RotateColumns(%d) failed: %w", shift, err)
		}
		if stats != nil {
			stats.Rotations++
		}
		logOpTrace(fmt.Sprintf("LWE->RLWE Step1 row-sum: ColumnRotation step=%d shift=%d", i, shift), "rot-col", h, nil, rot, false, durRot, expectedForRotateColumns(h, shift))
		stAdd := time.Now()
		sum, err := eval.AddNew(h, rot)
		durAdd := time.Since(stAdd)
		if err != nil {
			return nil, fmt.Errorf("Step1 Add after RotateColumns(%d) failed: %w", shift, err)
		}
		if stats != nil {
			stats.Additions++
		}
		logOpTrace(fmt.Sprintf("LWE->RLWE Step1 row-sum: Add rotated value step=%d shift=%d", i, shift), "add", h, rot, sum, false, durAdd, expectedForAdd(h, rot))
		h = sum
	}
	if s == r {
		stRot := time.Now()
		rot, err := eval.RotateRowsNew(h)
		durRot := time.Since(stRot)
		if err != nil {
			return nil, fmt.Errorf("Step1 RotateRows failed: %w", err)
		}
		if stats != nil {
			stats.RowRotations++
		}
		logOpTrace("LWE->RLWE Step1 row-sum: RowRotation final half-sum", "rot-row", h, nil, rot, false, durRot, expectedForRowSwap(h))
		stAdd := time.Now()
		sum, err := eval.AddNew(h, rot)
		durAdd := time.Since(stAdd)
		if err != nil {
			return nil, fmt.Errorf("Step1 Add after RotateRows failed: %w", err)
		}
		if stats != nil {
			stats.Additions++
		}
		logOpTrace("LWE->RLWE Step1 row-sum: Add RowRotation final half-sum", "add", h, rot, sum, false, durAdd, expectedForAdd(h, rot))
		h = sum
	} else {
		shift := baseLen * (1 << (ell - 1))
		stRot := time.Now()
		rot, err := eval.RotateColumnsNew(h, shift)
		durRot := time.Since(stRot)
		if err != nil {
			return nil, fmt.Errorf("Step1 final RotateColumns(%d) failed: %w", shift, err)
		}
		if stats != nil {
			stats.Rotations++
		}
		logOpTrace(fmt.Sprintf("LWE->RLWE Step1 row-sum: final ColumnRotation shift=%d", shift), "rot-col", h, nil, rot, false, durRot, expectedForRotateColumns(h, shift))
		stAdd := time.Now()
		sum, err := eval.AddNew(h, rot)
		durAdd := time.Since(stAdd)
		if err != nil {
			return nil, fmt.Errorf("Step1 final Add after RotateColumns(%d) failed: %w", shift, err)
		}
		if stats != nil {
			stats.Additions++
		}
		logOpTrace(fmt.Sprintf("LWE->RLWE Step1 row-sum: final Add after ColumnRotation shift=%d", shift), "add", h, rot, sum, false, durAdd, expectedForAdd(h, rot))
		h = sum
	}
	return h, nil
}

func homomorphicDecryptLWEToSparseRLWE(params bfv.Parameters, encoder *bfv.Encoder, enc *rlwe.Encryptor, eval *bfv.Evaluator, lweCts []LWECiphertext, secretMod []uint64, plan LWEToRLWEPackingPlan, m int) (*rlwe.Ciphertext, LWEToRLWEStats, error) {
	stats := LWEToRLWEStats{Blocks: plan.Blocks, InnerPeriod: plan.InnerPeriod, Mode: plan.Desc}
	if len(lweCts) != m {
		return nil, stats, fmt.Errorf("len(lweCts)=%d != m=%d", len(lweCts), m)
	}
	if len(secretMod) == 0 {
		return nil, stats, errors.New("empty LWE secret")
	}
	N := params.MaxSlots()
	if N%m != 0 {
		return nil, stats, fmt.Errorf("m=%d must divide MaxSlots=%d", m, N)
	}
	r := N / m
	if plan.Blocks <= 0 || plan.InnerPeriod <= 0 {
		return nil, stats, fmt.Errorf("invalid LWE->RLWE Step1 plan: %+v", plan)
	}
	var acc *rlwe.Ciphertext
	for block := 0; block < plan.Blocks; block++ {
		skSlots, maskSlots, err := buildStep1SecretAndMaskSlots(lweCts, secretMod, block, plan, m, r, params.PlaintextModulus())
		if err != nil {
			return nil, stats, err
		}
		ptSk, err := encodeBatchedPlaintextAtMaxLevel(params, encoder, skSlots)
		if err != nil {
			return nil, stats, fmt.Errorf("encode LWE->RLWE encrypted secret block %d: %w", block, err)
		}
		ctSk, err := enc.EncryptNew(ptSk)
		if err != nil {
			return nil, stats, fmt.Errorf("encrypt LWE->RLWE secret block %d: %w", block, err)
		}
		stats.Encryptions++
		stats.BSKBytes += int64(ctSk.BinarySize())
		polyRegisterExpected(ctSk, skSlots)
		ptMask, err := encodeBatchedPlaintextAtLevel(params, encoder, maskSlots, ctSk.Level(), ctSk.MetaData)
		if err != nil {
			return nil, stats, fmt.Errorf("encode LWE->RLWE -a mask block %d: %w", block, err)
		}
		term, err := mulPlainNoRescaleNamed(eval, ctSk, ptMask, maskSlots, fmt.Sprintf("LWE->RLWE Step1: encrypted secret block %d times plaintext -a mask", block))
		if err != nil {
			return nil, stats, fmt.Errorf("LWE->RLWE CMult for secret block %d failed: %w", block, err)
		}
		stats.CMults++
		if acc == nil {
			acc = term
		} else {
			var err error
			acc, err = addCiphertextsStep1(eval, acc, term, fmt.Sprintf("LWE->RLWE Step1: add secret-block contribution %d", block))
			if err != nil {
				return nil, stats, err
			}
			stats.Additions++
		}
	}
	if acc == nil {
		return nil, stats, errors.New("LWE->RLWE accumulator is empty")
	}
	ctInner, err := sparseRotateAndSumStep1(params, eval, acc, m, plan.InnerPeriod, &stats)
	if err != nil {
		return nil, stats, err
	}
	bSlots := make([]uint64, N)
	for col := 0; col < r; col++ {
		for row := 0; row < m; row++ {
			bSlots[col*m+row] = lweCts[row].B % params.PlaintextModulus()
		}
	}
	ptB, err := encodeBatchedPlaintextAtLevel(params, encoder, bSlots, ctInner.Level(), ctInner.MetaData)
	if err != nil {
		return nil, stats, fmt.Errorf("encode LWE->RLWE replicated b vector: %w", err)
	}
	stAdd := time.Now()
	ctOut, err := eval.AddNew(ctInner, ptB)
	durAdd := time.Since(stAdd)
	if err != nil {
		return nil, stats, fmt.Errorf("LWE->RLWE add replicated b failed: %w", err)
	}
	stats.Additions++
	ctOut.IsBatched = true
	logOpTrace("LWE->RLWE Step1: add replicated b vector", "add", ctInner, nil, ctOut, false, durAdd, expectedForAddPlainSlots(ctInner, bSlots))
	return ctOut, stats, nil
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
		term, err := mulPlainRescaleNamed(eval, ctS, mask, fmt.Sprintf("PackLWE: secret block %d times plaintext LWE mask", ell))
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

func strictDecodePhaseToMessageModP(phase, alpha, p, t, bound uint64) (uint64, bool) {
	if alpha == 0 || p == 0 || t == 0 || bound == 0 {
		return 0, false
	}
	phase %= t
	mu := decodePhaseToMessageModP(phase, alpha, p, t)
	center := mulMod(alpha%t, mu%p, t)
	d := centeredDiff(phase, center, t)
	if d < 0 {
		d = -d
	}
	return mu, uint64(d) < bound
}

// buildStrictFunctionalLUTPolynomialCoefficients implements the Section-5 LUT
// construction over the whole field Z_t. For each valid noisy phase
//
//	y = Delta*m + e,  |e| < floor(t/(2p)),
//
// it assigns
//
//	LUT(inputScale*y) = outputScale*Delta*f(m)  (mod t),
//
// and assigns 0 outside the union of the valid intervals. The returned
// coefficients represent the unique polynomial of degree at most t-1 over Z_t.
func buildStrictFunctionalLUTPolynomialCoefficients(t, p uint64, funcTable []uint64, inputScale, outputScale uint64) ([]uint64, error) {
	if len(funcTable) != int(p) {
		return nil, fmt.Errorf("function table length must be p=%d, got %d", p, len(funcTable))
	}
	if p == 0 || t < p {
		return nil, fmt.Errorf("need 0 < p <= t, got p=%d t=%d", p, t)
	}
	alpha := t / p
	if alpha == 0 {
		return nil, fmt.Errorf("Delta=floor(t/p)=0 for t=%d, p=%d", t, p)
	}
	bound := t / (2 * p)
	if bound == 0 {
		return nil, fmt.Errorf("empty valid phase interval: floor(t/(2p))=0 for t=%d p=%d", t, p)
	}
	inputScale %= t
	outputScale %= t
	if inputScale == 0 || tailGCDUint64(inputScale, t) != 1 {
		return nil, fmt.Errorf("input scale %d is not a unit modulo t=%d", inputScale, t)
	}
	invInputScale, err := tailInvModUint64(inputScale, t)
	if err != nil {
		return nil, err
	}
	order := int(t - 1)
	root, err := findPrimitiveRootPrime(t)
	if err != nil {
		return nil, err
	}
	lutValueAtScaledInput := func(z uint64) uint64 {
		y := mulMod(z%t, invInputScale, t)
		mu, ok := strictDecodePhaseToMessageModP(y, alpha, p, t, bound)
		if !ok {
			return 0
		}
		return mulMod(outputScale, mulMod(alpha%t, funcTable[mu%p]%p, t), t)
	}
	seq := make([]uint64, order)
	x := uint64(1)
	for j := 0; j < order; j++ {
		seq[j] = lutValueAtScaledInput(x)
		x = mulMod(x, root, t)
	}
	dft, err := nttForwardMixedPow2Odd(seq, root, t)
	if err != nil {
		return nil, err
	}
	coeff := make([]uint64, order+1)
	y0 := lutValueAtScaledInput(0)
	coeff[0] = y0
	for i := 1; i < order; i++ {
		coeff[i] = negateMod(dft[order-i], t)
	}
	coeff[order] = negateMod((y0+dft[0])%t, t)
	return coeff, nil
}

func padPolynomialCoefficientsToDegree(coeff []uint64, degree int) []uint64 {
	need := degree + 1
	if need <= 0 {
		return coeff
	}
	if len(coeff) >= need {
		return coeff[:need]
	}
	out := make([]uint64, need)
	copy(out, coeff)
	return out
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
	G          int
	B          int
	ShiftedPT  []*rlwe.Plaintext
	ShiftedVec [][]uint64 // optional cleartext masks used only by -mul-trace-noise
}

func encodeBatchedPlaintextAtLevel(params bfv.Parameters, encoder *bfv.Encoder, values []uint64, level int, md *rlwe.MetaData) (*rlwe.Plaintext, error) {
	if level < 0 || level > params.MaxLevel() {
		return nil, fmt.Errorf("invalid plaintext level %d for MaxLevel=%d", level, params.MaxLevel())
	}
	pt := bfv.NewPlaintext(params, level)
	if md != nil {
		pt.MetaData = md.CopyNew()
	}
	pt.IsBatched = true
	if err := encoder.Encode(values, pt); err != nil {
		return nil, err
	}
	return pt, nil
}

func encodeBatchedPlaintextAtMaxLevel(params bfv.Parameters, encoder *bfv.Encoder, values []uint64) (*rlwe.Plaintext, error) {
	return encodeBatchedPlaintextAtLevel(params, encoder, values, params.MaxLevel(), nil)
}

func cloneTraceSlotsIfNeeded(values []uint64) []uint64 {
	if !mulTraceNoiseActive() || values == nil {
		return nil
	}
	return append([]uint64(nil), values...)
}

func mulOperandNoRescale(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand) (*rlwe.Ciphertext, error) {
	return mulOperandNoRescaleNamed(eval, ct, op, "")
}

func mulOperandNoRescaleNamed(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand, traceName string) (*rlwe.Ciphertext, error) {
	return mulOperandNoRescaleNamedWithPlain(eval, ct, op, nil, traceName)
}

func mulOperandNoRescaleNamedWithPlain(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand, plain []uint64, traceName string) (*rlwe.Ciphertext, error) {
	st := time.Now()
	out, err := eval.MulNew(ct, op)
	if err != nil {
		return nil, err
	}
	logMulTrace(mulTraceName("mulOperandNoRescale", traceName), "ct-op", ct, nil, out, false, time.Since(st), expectedForCtPlainMul(ct, plain))
	return out, nil
}

func mulOperandRescale(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand) (*rlwe.Ciphertext, error) {
	return mulOperandRescaleNamed(eval, ct, op, "")
}

func mulOperandRescaleNamed(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand, traceName string) (*rlwe.Ciphertext, error) {
	return mulOperandRescaleNamedWithPlain(eval, ct, op, nil, traceName)
}

func mulOperandRescaleNamedWithPlain(eval *bfv.Evaluator, ct *rlwe.Ciphertext, op rlwe.Operand, plain []uint64, traceName string) (*rlwe.Ciphertext, error) {
	st := time.Now()
	out, err := eval.MulNew(ct, op)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(out, out); err != nil {
		return nil, err
	}
	logMulTrace(mulTraceName("mulOperandRescale", traceName), "ct-op", ct, nil, out, true, time.Since(st), expectedForCtPlainMul(ct, plain))
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
	var shiftedVec [][]uint64
	if mulTraceNoiseActive() {
		shiftedVec = make([][]uint64, n)
	}
	for j := 0; j < n; j++ {
		giantShift := (j / g) * g
		shifted := rotateLeftUint64(diagExt[j], -giantShift)
		pt, err := encodeBatchedPlaintextAtMaxLevel(params, encoder, shifted)
		if err != nil {
			return nil, fmt.Errorf("failed to pre-encode SlotToCoeff diagonal %d: %w", j, err)
		}
		shiftedPT[j] = pt
		if shiftedVec != nil {
			shiftedVec[j] = append([]uint64(nil), shifted...)
		}
	}
	return &PreprocessedBSGSPlaintexts{G: g, B: b, ShiftedPT: shiftedPT, ShiftedVec: shiftedVec}, nil
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
		polyRegisterExpectedRotateColumns(rot, ct, k)
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
			var shiftedPlain []uint64
			if j < len(pre.ShiftedVec) {
				shiftedPlain = pre.ShiftedVec[j]
			}
			term, err := mulOperandRescaleNamedWithPlain(eval, baby[k], pre.ShiftedPT[j], shiftedPlain, fmt.Sprintf("SlotToCoeff BSGS(precomp): term j=%d from giant i=%d, baby k=%d", j, i, k))
			if err != nil {
				return nil, stats, fmt.Errorf("plaintext-ciphertext multiplication for diagonal %d failed: %w", j, err)
			}
			stats.PlainCipherMults++
			if block == nil {
				block = term
			} else {
				oldBlockExpected := polyExpectedClone(block)
				block, err = eval.AddNew(block, term)
				if err != nil {
					return nil, stats, fmt.Errorf("block add for diagonal %d failed: %w", j, err)
				}
				polyRegisterExpectedAddSaved(block, oldBlockExpected, term)
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
			polyRegisterExpectedRotateColumns(rot, block, giantShift)
			block = rot
			stats.Rotations++
			stats.GiantRotations++
		}
		if acc == nil {
			acc = block
		} else {
			oldAccExpected := polyExpectedClone(acc)
			var err error
			acc, err = eval.AddNew(acc, block)
			if err != nil {
				return nil, stats, fmt.Errorf("accumulator add for giant block %d failed: %w", i, err)
			}
			polyRegisterExpectedAddSaved(acc, oldAccExpected, block)
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
	FirstMaskVec  []uint64 // optional cleartext mask used only by -mul-trace-noise
	FirstConstVec []uint64
	CMaskPT       []*rlwe.Plaintext
	CMaskVec      [][]uint64 // optional cleartext masks used only by -mul-trace-noise
	DConstVec     [][]uint64
}

func preprocessMonomialPlaintextsAtInputLevel(params bfv.Parameters, encoder *bfv.Encoder, n int, coeffs [][]uint64, inputLevel int) (*PreprocessedMonomial, error) {
	if len(coeffs) == 0 || len(coeffs[0]) == 0 {
		return nil, errors.New("coeffs is empty")
	}
	if inputLevel < 0 || inputLevel > params.MaxLevel() {
		return nil, fmt.Errorf("invalid monomial precompute input level L%d for MaxLevel=%d", inputLevel, params.MaxLevel())
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
	pre.FirstMaskPT, err = encodeBatchedPlaintextAtLevel(params, encoder, firstMask, inputLevel, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to pre-encode first monomial mask at L%d: %w", inputLevel, err)
	}
	pre.FirstMaskVec = cloneTraceSlotsIfNeeded(firstMask)
	pre.FirstConstVec = hadamard(dExt[0], fVec, T)
	pre.CMaskPT = make([]*rlwe.Plaintext, ell)
	if mulTraceNoiseActive() {
		pre.CMaskVec = make([][]uint64, ell)
	}
	pre.DConstVec = make([][]uint64, ell)
	for i := 1; i < ell; i++ {
		maskLevel := inputLevel - i
		if maskLevel < 0 {
			return nil, fmt.Errorf("monomial precompute would need C_%d at negative level L%d; input level L%d is too small", i, maskLevel, inputLevel)
		}
		pre.CMaskPT[i], err = encodeBatchedPlaintextAtLevel(params, encoder, cExt[i], maskLevel, nil)
		if err != nil {
			return nil, fmt.Errorf("failed to pre-encode monomial mask bit %d at L%d: %w", i, maskLevel, err)
		}
		if pre.CMaskVec != nil {
			pre.CMaskVec[i] = append([]uint64(nil), cExt[i]...)
		}
		pre.DConstVec[i] = append([]uint64(nil), dExt[i]...)
	}
	return pre, nil
}

func preprocessMonomialPlaintexts(params bfv.Parameters, encoder *bfv.Encoder, n int, coeffs [][]uint64) (*PreprocessedMonomial, error) {
	return preprocessMonomialPlaintextsAtInputLevel(params, encoder, n, coeffs, params.MaxLevel())
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
		polyRegisterExpected(out, pre.ConstVec)
		timing.Total = time.Since(totalStart)
		progressf("run complete in %v", timing.Total)
		return out, nil, timing, nil
	}
	powStart := time.Now()
	xPow := make([]*rlwe.Ciphertext, pre.Ell)
	xPow[0] = ct.CopyNew()
	polyCopyExpected(ct, xPow[0])
	for i := 1; i < pre.Ell; i++ {
		xPow[i], err = mulCtRelinRescaleNamed(eval, xPow[i-1], xPow[i-1], fmt.Sprintf("MonomialGen(s=%d): power chain xPow[%d] = xPow[%d]^2", s, i, i-1))
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed to compute x^(2^%d): %w", i, err)
		}
	}
	timing.BuildPowers = time.Since(powStart)
	var extra *rlwe.Ciphertext
	if wantExtra {
		extra = xPow[pre.Ell-1].CopyNew()
		polyCopyExpected(xPow[pre.Ell-1], extra)
	}
	yStart := time.Now()
	tmp, err := mulOperandRescaleNamedWithPlain(eval, xPow[0], pre.FirstMaskPT, pre.FirstMaskVec, fmt.Sprintf("MonomialGen(s=%d): first masked factor tmp = xPow[0] * C_0", s))
	if err != nil {
		return nil, nil, timing, fmt.Errorf("failed first masked multiply: %w", err)
	}
	acc, err := eval.AddNew(tmp, pre.FirstConstVec)
	if err != nil {
		return nil, nil, timing, fmt.Errorf("failed first masked add: %w", err)
	}
	polyRegisterExpectedAddPlain(acc, tmp, pre.FirstConstVec)
	for i := 1; i < pre.Ell; i++ {
		var cMaskPlain []uint64
		if i < len(pre.CMaskVec) {
			cMaskPlain = pre.CMaskVec[i]
		}
		tmp, err = mulOperandRescaleNamedWithPlain(eval, xPow[i], pre.CMaskPT[i], cMaskPlain, fmt.Sprintf("MonomialGen(s=%d): bit %d masked factor tmp = xPow[%d] * C_%d", s, i, i, i))
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed masked multiply at bit %d: %w", i, err)
		}
		factor, err := eval.AddNew(tmp, pre.DConstVec[i])
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed masked add at bit %d: %w", i, err)
		}
		polyRegisterExpectedAddPlain(factor, tmp, pre.DConstVec[i])
		acc, err = mulCtRelinRescaleNamed(eval, acc, factor, fmt.Sprintf("MonomialGen(s=%d): bit %d combine acc = acc * factor", s, i))
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed ciphertext multiply at bit %d: %w", i, err)
		}
	}
	timing.BuildY = time.Since(yStart)
	timing.Total = time.Since(totalStart)
	return acc, extra, timing, nil
}

type PreprocessedParallelLT2 struct {
	Ell            int
	R              int
	G              int
	B              int
	ShiftedMaskPT  []*rlwe.Plaintext
	ShiftedMaskVec [][]uint64 // optional cleartext masks used only by -mul-trace-noise
}

func preprocessParallelLT2AtLevel(params bfv.Parameters, encoder *bfv.Encoder, A, B [][][]uint64, n, ell, r int, level int) (*PreprocessedParallelLT2, error) {
	if level < 0 || level > params.MaxLevel() {
		return nil, fmt.Errorf("invalid ParallelLT plaintext level L%d for MaxLevel=%d", level, params.MaxLevel())
	}
	g, b, err := choosePolyLTBSGS(ell)
	if err != nil {
		return nil, err
	}
	pre := &PreprocessedParallelLT2{Ell: ell, R: r, G: g, B: b, ShiftedMaskPT: make([]*rlwe.Plaintext, ell)}
	if mulTraceNoiseActive() {
		pre.ShiftedMaskVec = make([][]uint64, ell)
	}
	var shiftedMaskBuf []uint64
	for j := 0; j < ell; j++ {
		giantShift := (j / g) * g * n
		shiftedMask := buildShiftedMaskVectorInPlace(shiftedMaskBuf, A, B, j, n, ell, r, giantShift)
		shiftedMaskBuf = shiftedMask
		pt, err := encodeBatchedPlaintextAtLevel(params, encoder, shiftedMask, level, nil)
		if err != nil {
			return nil, fmt.Errorf("failed to pre-encode ParallelLT mask %d at L%d: %w", j, level, err)
		}
		pre.ShiftedMaskPT[j] = pt
		if pre.ShiftedMaskVec != nil {
			pre.ShiftedMaskVec[j] = append([]uint64(nil), shiftedMask...)
		}
	}
	return pre, nil
}

func preprocessParallelLT2(params bfv.Parameters, encoder *bfv.Encoder, A, B [][][]uint64, n, ell, r int) (*PreprocessedParallelLT2, error) {
	return preprocessParallelLT2AtLevel(params, encoder, A, B, n, ell, r, params.MaxLevel())
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
		polyRegisterExpectedRotateColumns(rot, ctIn, k*n)
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
			if pre.ShiftedMaskPT[j] == nil {
				return nil, fmt.Errorf("alg2 bsgs precomputed plaintext j=%d is nil", j)
			}
			if plaintextLevel(pre.ShiftedMaskPT[j]) != levelQ {
				return nil, fmt.Errorf("alg2 bsgs precomputed plaintext j=%d is at L%d but BatchLT ciphertext is at L%d; regenerate -poly-precompute-pt with the resolved LT level", j, plaintextLevel(pre.ShiftedMaskPT[j]), levelQ)
			}
			stMul := time.Now()
			term, err := eval.MulNew(baby[k], pre.ShiftedMaskPT[j])
			if err != nil {
				return nil, fmt.Errorf("alg2 bsgs term multiply i=%d k=%d j=%d failed: %w", i, k, j, err)
			}
			durMul := time.Since(stMul)
			tm.PlaintextCipherMul += durMul
			if mulTraceActive() {
				var shiftedPlain []uint64
				if j < len(pre.ShiftedMaskVec) {
					shiftedPlain = pre.ShiftedMaskVec[j]
				}
				logMulTrace(fmt.Sprintf("ParallelLT/BSGS(precomp): term = baby[%d] * shiftedMask[j=%d], giant block i=%d", k, j, i), "ct-pt-LT", baby[k], nil, term, false, durMul, expectedForCtPlainMul(baby[k], shiftedPlain))
			}
			if block == nil {
				block = term
			} else {
				oldBlockExpected := polyExpectedClone(block)
				if err := eval.Add(block, term, block); err != nil {
					return nil, fmt.Errorf("alg2 bsgs block add i=%d k=%d j=%d failed: %w", i, k, j, err)
				}
				polyRegisterExpectedAddSaved(block, oldBlockExpected, term)
			}
		}
		if block == nil {
			continue
		}
		if giantShift == 0 {
			if acc == nil {
				acc = block
			} else {
				oldAccExpected := polyExpectedClone(acc)
				if err := eval.Add(acc, block, acc); err != nil {
					return nil, fmt.Errorf("alg2 bsgs acc add i=%d failed: %w", i, err)
				}
				polyRegisterExpectedAddSaved(acc, oldAccExpected, block)
			}
		} else {
			rot := bfv.NewCiphertext(params, 1, block.Level())
			galEl := params.GaloisElementForColRotation(giantShift)
			stRot := time.Now()
			if err := eval.Automorphism(block, galEl, rot); err != nil {
				return nil, fmt.Errorf("alg2 bsgs giant rotation i=%d failed: %w", i, err)
			}
			tm.GiantRotations += time.Since(stRot)
			polyRegisterExpectedRotateColumns(rot, block, giantShift)
			if acc == nil {
				acc = rot
			} else {
				oldAccExpected := polyExpectedClone(acc)
				if err := eval.Add(acc, rot, acc); err != nil {
					return nil, fmt.Errorf("alg2 bsgs giant add i=%d failed: %w", i, err)
				}
				polyRegisterExpectedAddSaved(acc, oldAccExpected, rot)
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

func preprocessParallelLT3ViewsAtLevel(params bfv.Parameters, encoder *bfv.Encoder, U [][][]uint64, n, ell, r int, level int) (*PreprocessedParallelLT3, error) {
	pre := &PreprocessedParallelLT3{}
	if ell < r {
		A, B := splitUHorizontalViews(U, ell, r)
		p1, err := preprocessParallelLT2AtLevel(params, encoder, A, B, n, ell, r, level)
		if err != nil {
			return nil, err
		}
		pre.Short = true
		pre.Pre1 = p1
		return pre, nil
	}
	A, B, C, D := splitUBlocksViews(U, r)
	p1, err := preprocessParallelLT2AtLevel(params, encoder, A, D, n, r/2, r, level)
	if err != nil {
		return nil, err
	}
	p2, err := preprocessParallelLT2AtLevel(params, encoder, B, C, n, r/2, r, level)
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
		oldYExpected := polyExpectedClone(y)
		tauY, err := rowSwapCipher(params, eval, y)
		if err != nil {
			return nil, tm, fmt.Errorf("alg3 row swap failed: %w", err)
		}
		if err := eval.Add(y, tauY, y); err != nil {
			return nil, tm, fmt.Errorf("alg3 add y+tau(y) failed: %w", err)
		}
		polyRegisterExpectedAddSaved(y, oldYExpected, tauY)
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
	oldYExpected := polyExpectedClone(y)
	if err := eval.Add(y, yPrime, y); err != nil {
		return nil, tm, fmt.Errorf("alg3 add y+y' failed: %w", err)
	}
	polyRegisterExpectedAddSaved(y, oldYExpected, yPrime)
	tm.PostProcess += time.Since(startPost)
	tm.Total = time.Since(start)
	return y, tm, nil
}

type PreprocessedPolyEval struct {
	D           int
	M           int
	Mode        string
	InputLevel  int
	CT1Level    int
	CT2Level    int
	LTLevel     int
	LTPostLevel int
	LeadLevel   int
	LeadPT      *rlwe.Plaintext
	LeadVec     []uint64 // optional cleartext leading vector used only by -mul-trace-noise
	LowerMon    *PreprocessedMonomial
	OnesRMon    *PreprocessedMonomial
	OnesSMon    *PreprocessedMonomial
	LT          *PreprocessedParallelLT3
}

func monomialOutputLevelForPrecompute(inputLevel, s int) (int, error) {
	if inputLevel < 0 {
		return 0, fmt.Errorf("negative monomial input level L%d", inputLevel)
	}
	if s <= 0 || !isPow2(s) {
		return 0, fmt.Errorf("s=%d must be a positive power of two", s)
	}
	ell := log2Pow2(s)
	if ell == 0 {
		return inputLevel, nil
	}
	if ell == 1 {
		if inputLevel-1 < 0 {
			return 0, fmt.Errorf("monomial s=%d at L%d would end below L0", s, inputLevel)
		}
		return inputLevel - 1, nil
	}
	out := inputLevel - ell - 1
	if out < 0 {
		return 0, fmt.Errorf("monomial s=%d at L%d would end below L0", s, inputLevel)
	}
	return out, nil
}

func monomialExtraLevelForPrecompute(inputLevel, s int) (int, error) {
	if inputLevel < 0 {
		return 0, fmt.Errorf("negative monomial input level L%d", inputLevel)
	}
	if s <= 1 {
		return inputLevel, nil
	}
	if !isPow2(s) {
		return 0, fmt.Errorf("s=%d must be a positive power of two", s)
	}
	ell := log2Pow2(s)
	extra := inputLevel - (ell - 1)
	if extra < 0 {
		return 0, fmt.Errorf("monomial extra x^(s/2) for s=%d at L%d would be below L0", s, inputLevel)
	}
	return extra, nil
}

func estimateAlg5PrecomputeLevels(params bfv.Parameters, m, d, inputLevel int, dropBeforeLT bool, ltLevel, ltPostLevel int, deferLTPostRescale bool) (ct1Level, ct2Level, ltInputLevel, resolvedLTPostLevel, leadLevel int, err error) {
	if m <= 0 || params.MaxSlots()%m != 0 {
		return 0, 0, 0, 0, 0, fmt.Errorf("m=%d must divide MaxSlots=%d", m, params.MaxSlots())
	}
	r := params.MaxSlots() / m
	if d <= r || d > r*r || d%r != 0 {
		return 0, 0, 0, 0, 0, fmt.Errorf("Algorithm 5 requires r < d <= r^2 and r|d, got d=%d, r=%d, m=%d", d, r, m)
	}
	s := d / r
	ct1Level, err = monomialOutputLevelForPrecompute(inputLevel, r)
	if err != nil {
		return 0, 0, 0, 0, 0, fmt.Errorf("estimating ct1/ctP level failed: %w", err)
	}
	ctHalfLevel, err := monomialExtraLevelForPrecompute(inputLevel, r)
	if err != nil {
		return 0, 0, 0, 0, 0, fmt.Errorf("estimating x^(r/2) level failed: %w", err)
	}
	ctRLevel := ctHalfLevel - 1
	if ctRLevel < 0 {
		return 0, 0, 0, 0, 0, fmt.Errorf("x^r square would go below L0 from x^(r/2) at L%d", ctHalfLevel)
	}
	ct2Level, err = monomialOutputLevelForPrecompute(ctRLevel, s)
	if err != nil {
		return 0, 0, 0, 0, 0, fmt.Errorf("estimating ct2/grouped-powers level failed: %w", err)
	}
	ltInputLevel, resolvedLTPostLevel, err = resolveParallelLTLevelPolicy(ct1Level, ct2Level, dropBeforeLT, ltLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return 0, 0, 0, 0, 0, err
	}
	ctDHalfLevel, err := monomialExtraLevelForPrecompute(ctRLevel, s)
	if err != nil {
		return 0, 0, 0, 0, 0, fmt.Errorf("estimating x^(d/2) level failed: %w", err)
	}
	leadLevel = ctDHalfLevel - 1
	if leadLevel < 0 {
		return 0, 0, 0, 0, 0, fmt.Errorf("x^d square would go below L0 from x^(d/2) at L%d", ctDHalfLevel)
	}
	return ct1Level, ct2Level, ltInputLevel, resolvedLTPostLevel, leadLevel, nil
}

func preprocessPolyEvalPlaintexts(params bfv.Parameters, encoder *bfv.Encoder, m, d int, coeffsLower [][]uint64, leadCoeffs []uint64) (*PreprocessedPolyEval, error) {
	return preprocessPolyEvalPlaintextsAligned(params, encoder, m, d, coeffsLower, leadCoeffs, params.MaxLevel(), true, -1, 2, false, false)
}

func preprocessPolyEvalPlaintextsAligned(params bfv.Parameters, encoder *bfv.Encoder, m, d int, coeffsLower [][]uint64, leadCoeffs []uint64, inputLevel int, dropBeforeLT bool, ltLevel, ltPostLevel int, deferLTPostRescale bool, ltOnly bool) (*PreprocessedPolyEval, error) {
	pre := &PreprocessedPolyEval{D: d, M: m, InputLevel: inputLevel, CT1Level: -1, CT2Level: -1, LTLevel: -1, LTPostLevel: -1, LeadLevel: -1}
	if ltOnly {
		pre.Mode = "LT-only large-branch precompute"
	} else {
		pre.Mode = "full Algorithm-5 precompute"
	}
	if inputLevel < 0 || inputLevel > params.MaxLevel() {
		return nil, fmt.Errorf("invalid polynomial input level L%d for MaxLevel=%d", inputLevel, params.MaxLevel())
	}
	if m <= 0 || params.MaxSlots()%m != 0 {
		return nil, fmt.Errorf("m=%d must divide MaxSlots=%d", m, params.MaxSlots())
	}
	r := params.MaxSlots() / m
	var err error
	if m == 1 && d <= r {
		if ltOnly {
			return nil, fmt.Errorf("LT-only precompute is not applicable to the m=1 direct path")
		}
		pre.LeadLevel = inputLevel
		if d > 1 {
			ctHalfLevel, err := monomialExtraLevelForPrecompute(inputLevel, d)
			if err != nil {
				return nil, err
			}
			pre.LeadLevel = ctHalfLevel - 1
			if pre.LeadLevel < 0 {
				return nil, fmt.Errorf("leading term plaintext level would be negative")
			}
		}
		leadVec, err := sparsePackLeadingCoeffs(leadCoeffs, params.MaxSlots())
		if err != nil {
			return nil, err
		}
		pre.LeadPT, err = encodeBatchedPlaintextAtLevel(params, encoder, leadVec, pre.LeadLevel, nil)
		if err != nil {
			return nil, fmt.Errorf("failed to pre-encode leading x^d plaintext at L%d: %w", pre.LeadLevel, err)
		}
		pre.LeadVec = cloneTraceSlotsIfNeeded(leadVec)
		pre.LowerMon, err = preprocessMonomialPlaintextsAtInputLevel(params, encoder, m, coeffsLower, inputLevel)
		return pre, err
	}
	if d <= r || d > r*r || d%r != 0 {
		return nil, fmt.Errorf("Algorithm 5 requires r < d <= r^2 and r|d unless m=1 uses the direct path, got d=%d, r=%d, m=%d", d, r, m)
	}
	s := d / r
	ct1Level, ct2Level, ltInputLevel, resolvedLTPostLevel, leadLevel, err := estimateAlg5PrecomputeLevels(params, m, d, inputLevel, dropBeforeLT, ltLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return nil, err
	}
	pre.CT1Level = ct1Level
	pre.CT2Level = ct2Level
	pre.LTLevel = ltInputLevel
	pre.LTPostLevel = resolvedLTPostLevel
	pre.LeadLevel = leadLevel
	if !ltOnly {
		leadVec, err := sparsePackLeadingCoeffs(leadCoeffs, params.MaxSlots())
		if err != nil {
			return nil, err
		}
		pre.LeadPT, err = encodeBatchedPlaintextAtLevel(params, encoder, leadVec, leadLevel, nil)
		if err != nil {
			return nil, fmt.Errorf("failed to pre-encode leading x^d plaintext at L%d: %w", leadLevel, err)
		}
		pre.LeadVec = cloneTraceSlotsIfNeeded(leadVec)
		pre.OnesRMon, err = preprocessMonomialPlaintextsAtInputLevel(params, encoder, m, buildAllOnesCoeffs(m, r), inputLevel)
		if err != nil {
			return nil, err
		}
		ctHalfLevel, err := monomialExtraLevelForPrecompute(inputLevel, r)
		if err != nil {
			return nil, err
		}
		ctRLevel := ctHalfLevel - 1
		pre.OnesSMon, err = preprocessMonomialPlaintextsAtInputLevel(params, encoder, m, buildAllOnesCoeffs(m, s), ctRLevel)
		if err != nil {
			return nil, err
		}
	}
	U := buildPatersonStockmeyerMatrixViews(coeffsLower, r)
	pre.LT, err = preprocessParallelLT3ViewsAtLevel(params, encoder, U, m, s, r, ltInputLevel)
	return pre, err
}

func mulPlainRescale(eval *bfv.Evaluator, ct *rlwe.Ciphertext, plain []uint64) (*rlwe.Ciphertext, error) {
	return mulPlainRescaleNamed(eval, ct, plain, "")
}

func mulPlainRescaleNamed(eval *bfv.Evaluator, ct *rlwe.Ciphertext, plain []uint64, traceName string) (*rlwe.Ciphertext, error) {
	st := time.Now()
	out, err := eval.MulNew(ct, plain)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(out, out); err != nil {
		return nil, err
	}
	logMulTrace(mulTraceName("mulPlainRescale", traceName), "ct-pt", ct, nil, out, true, time.Since(st), expectedForCtPlainMul(ct, plain))
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
		polyRegisterExpectedRotateColumns(rot, ct, k)
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

			// For SlotToCoeff we intentionally do NOT rescale each diagonal term.
			// The whole StC linear transform is accumulated at the input level.
			// The caller then performs either one direct post-StC Rescale/ModSwitch
			// to Q'=Q[0], or a two-step buffer rescale Lk -> Lbuffer -> Q'.
			stMul := time.Now()
			term, err := eval.MulNew(baby[k], shiftedDiag)
			durMul := time.Since(stMul)
			if err != nil {
				return nil, stats, fmt.Errorf("plaintext-ciphertext multiplication for diagonal %d failed: %w", j, err)
			}
			logMulTrace(fmt.Sprintf("SlotToCoeff BSGS(stream,no-rescale): term j=%d from giant i=%d, baby k=%d", j, i, k), "ct-pt-StC", baby[k], nil, term, false, durMul, expectedForCtPlainMul(baby[k], shiftedDiag))
			stats.PlainCipherMults++
			if block == nil {
				block = term
			} else {
				oldBlockExpected := polyExpectedClone(block)
				block, err = eval.AddNew(block, term)
				if err != nil {
					return nil, stats, fmt.Errorf("block add for diagonal %d failed: %w", j, err)
				}
				polyRegisterExpectedAddSaved(block, oldBlockExpected, term)
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
			polyRegisterExpectedRotateColumns(rot, block, giantShift)
			block = rot
			stats.Rotations++
			stats.GiantRotations++
		}

		if acc == nil {
			acc = block
		} else {
			oldAccExpected := polyExpectedClone(acc)
			var err error
			acc, err = eval.AddNew(acc, block)
			if err != nil {
				return nil, stats, fmt.Errorf("accumulator add for giant block %d failed: %w", i, err)
			}
			polyRegisterExpectedAddSaved(acc, oldAccExpected, block)
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
	Name               string
	Level              int
	CurrentLogQBits    int
	ScaleModT          uint64
	NonZeroCoeffNoise  int
	MaxCoeffNoiseAbs   string
	MaxCoeffNoiseBits  int
	ApproxErrorAbs     string
	RequiredBitsRaw    int
	NoiseBudgetBits    int
	CoeffNoisePreview  []string
	TotalCoefficients  int
	DecodedSlotBad     int
	DecodedSlotTotal   int
	DecodedSlotMaxAbs  int64
	DecodedSlotPreview []string
}

type PolyNoiseTracer struct {
	Enabled   bool
	Params    bfv.Parameters
	Encoder   *bfv.Encoder
	Dec       *rlwe.Decryptor
	Preview   int
	Full      bool
	Entries   []PolyNoiseTraceEntry
	ProbeTime time.Duration
}

var globalPolyNoiseTracer *PolyNoiseTracer
var globalPolyNoiseBase []uint64
var globalPolyNoiseCoeffLower [][]uint64
var globalPolyNoiseLeadCoeffs []uint64
var globalCt2NoiseProbe bool

func setPolyNoiseTraceContext(tr *PolyNoiseTracer, base []uint64, coeffsLower [][]uint64, leadCoeffs []uint64) {
	// Do not retain or copy per-run LUT data unless exact polynomial-noise tracing
	// or the targeted c2/ct2 probe is enabled.  For large LUTs this avoids keeping
	// another copy of multi-megabyte or gigabyte slices alive until the end of the run.
	if tr == nil || (!tr.Enabled && !globalCt2NoiseProbe) {
		clearPolyNoiseTraceContext()
		return
	}

	if tr.Enabled {
		globalPolyNoiseTracer = tr
	} else {
		globalPolyNoiseTracer = nil
	}
	if base == nil {
		globalPolyNoiseBase = nil
	} else {
		globalPolyNoiseBase = append([]uint64(nil), base...)
	}
	if !tr.Enabled {
		globalPolyNoiseCoeffLower = nil
		globalPolyNoiseLeadCoeffs = nil
		return
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
	reqBits, _ := estimateResidualBitsFromNoise(maxAbs, tr.Params.PlaintextModulus(), 0)
	maxResidualBits := 0
	if maxAbs.Sign() > 0 {
		maxResidualBits = maxAbs.BitLen() - 1
	}
	approxErr := new(big.Int).Set(maxAbs)
	if tr.Params.PlaintextModulus() > 0 {
		approxErr.Quo(approxErr, new(big.Int).SetUint64(tr.Params.PlaintextModulus()))
	}

	// In addition to the coefficient-domain residual ptGot-Encode(expected),
	// also decode the ciphertext and compare the decoded slots modulo T.  The
	// coefficient residual is the BGV/BFV decryptability noise (and can be very
	// large after dense plaintext multiplications), while the decoded-slot
	// residual is only a correctness diagnostic modulo T.  Printing both avoids
	// confusing large but still decryptable coefficient noise with a wrong
	// plaintext reference.
	decoded := make([]uint64, tr.Params.MaxSlots())
	decodedBad := -1
	decodedTotal := len(expectedSlots)
	decodedMaxAbs := int64(0)
	decodedPreview := []string{}
	if err := tr.Encoder.Decode(ptGot, decoded); err == nil && len(expectedSlots) <= len(decoded) {
		decodedBad = 0
		previewSlots := tr.Preview
		if tr.Full || previewSlots > len(expectedSlots) {
			previewSlots = len(expectedSlots)
		}
		decodedPreview = make([]string, previewSlots)
		for i := range expectedSlots {
			d := centeredDiff(decoded[i], expectedSlots[i], tr.Params.PlaintextModulus())
			if d != 0 {
				decodedBad++
			}
			ad := abs64(d)
			if ad > decodedMaxAbs {
				decodedMaxAbs = ad
			}
			if i < previewSlots {
				decodedPreview[i] = fmt.Sprintf("%d", d)
			}
		}
	}

	entry := PolyNoiseTraceEntry{
		Name:               name,
		Level:              ct.Level(),
		CurrentLogQBits:    bigQ.BitLen(),
		ScaleModT:          scaleModUint64(ct.Scale, tr.Params.PlaintextModulus()),
		NonZeroCoeffNoise:  nonZero,
		MaxCoeffNoiseAbs:   maxAbs.String(),
		MaxCoeffNoiseBits:  maxResidualBits,
		ApproxErrorAbs:     approxErr.String(),
		RequiredBitsRaw:    reqBits,
		NoiseBudgetBits:    bigQ.BitLen() - reqBits,
		CoeffNoisePreview:  preview,
		TotalCoefficients:  len(gotBig),
		DecodedSlotBad:     decodedBad,
		DecodedSlotTotal:   decodedTotal,
		DecodedSlotMaxAbs:  decodedMaxAbs,
		DecodedSlotPreview: decodedPreview,
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
		fmt.Printf("  nonzero coeff residual   : %d / %d\n", e.NonZeroCoeffNoise, e.TotalCoefficients)
		fmt.Printf("  max |coeff residual|     : %s  (≈2^%d)\n", e.MaxCoeffNoiseAbs, e.MaxCoeffNoiseBits)
		fmt.Printf("  approx |error|=res/T     : %s\n", e.ApproxErrorAbs)
		fmt.Printf("  required logQ raw        : %d\n", e.RequiredBitsRaw)
		fmt.Printf("  coefficient noise budget : %d bits\n", e.NoiseBudgetBits)
		fmt.Printf("  coeff residual preview   : %v\n", e.CoeffNoisePreview)
		if e.DecodedSlotBad >= 0 {
			fmt.Printf("  decoded-slot mismatches  : %d / %d\n", e.DecodedSlotBad, e.DecodedSlotTotal)
			fmt.Printf("  decoded-slot max |diff|  : %d\n", e.DecodedSlotMaxAbs)
			fmt.Printf("  decoded-slot diff preview: %v\n", e.DecodedSlotPreview)
		} else {
			fmt.Printf("  decoded-slot residual    : n/a\n")
		}
	}
	fmt.Println("--------------------------------------------------------------------------------------------")
	fmt.Println()
}

func printImmediateCt2NoiseProbe(e PolyNoiseTraceEntry) {
	fmt.Println()
	fmt.Println("---------- Immediate ct2/grouped-powers noise checkpoint ----------")
	fmt.Printf("%s:\n", e.Name)
	fmt.Printf("  level                    : %d\n", e.Level)
	fmt.Printf("  current logQ bits        : %d\n", e.CurrentLogQBits)
	fmt.Printf("  scale mod T              : %d\n", e.ScaleModT)
	fmt.Printf("  max |coeff residual|     : %s  (≈2^%d)\n", e.MaxCoeffNoiseAbs, e.MaxCoeffNoiseBits)
	fmt.Printf("  required logQ raw        : %d\n", e.RequiredBitsRaw)
	fmt.Printf("  coefficient noise budget : %d bits\n", e.NoiseBudgetBits)
	fmt.Printf("  coeff residual preview   : %v\n", e.CoeffNoisePreview)
	if e.DecodedSlotBad >= 0 {
		fmt.Printf("  decoded-slot mismatches  : %d / %d\n", e.DecodedSlotBad, e.DecodedSlotTotal)
		fmt.Printf("  decoded-slot max |diff|  : %d\n", e.DecodedSlotMaxAbs)
		fmt.Printf("  decoded-slot diff preview: %v\n", e.DecodedSlotPreview)
	}
	fmt.Println("-------------------------------------------------------------------")
	fmt.Println()
}

func maybeTracePolyNoise(name string, ct *rlwe.Ciphertext, expectedSlots []uint64) error {
	polyRegisterExpected(ct, expectedSlots)
	if globalPolyNoiseTracer == nil || !globalPolyNoiseTracer.Enabled {
		return nil
	}
	start := time.Now()
	err := globalPolyNoiseTracer.Probe(name, ct, expectedSlots)
	globalPolyNoiseTracer.ProbeTime += time.Since(start)
	return err
}

func maybeTraceAndPrintImmediatePolyNoise(name string, ct *rlwe.Ciphertext, expectedSlots []uint64, title string) error {
	polyRegisterExpected(ct, expectedSlots)
	if title == "" {
		title = name
	}

	// Also insert a checkpoint row only when the expensive operation-noise probes
	// are explicitly enabled. Plain -mul-trace is kept lightweight and does not
	// decrypt/decode c2/ct2.
	if mulTraceNoiseActive() {
		logOpTrace(title, "checkpoint", ct, nil, ct, false, 0, expectedSlots)
	}

	if globalPolyNoiseTracer != nil && globalPolyNoiseTracer.Enabled {
		before := len(globalPolyNoiseTracer.Entries)
		start := time.Now()
		if err := globalPolyNoiseTracer.Probe(name, ct, expectedSlots); err != nil {
			globalPolyNoiseTracer.ProbeTime += time.Since(start)
			return err
		}
		globalPolyNoiseTracer.ProbeTime += time.Since(start)
		if len(globalPolyNoiseTracer.Entries) > before {
			e := globalPolyNoiseTracer.Entries[len(globalPolyNoiseTracer.Entries)-1]
			mismatch := "n/a"
			if e.DecodedSlotBad >= 0 {
				mismatch = fmt.Sprintf("%d/%d", e.DecodedSlotBad, e.DecodedSlotTotal)
			}
			fmt.Printf("[immediate noise probe] %s: level=L%d/%db, scale mod T=%d, noiseBudget=%d bits, max|noise|=%s, requiredLogQ=%d, decodedMismatches=%s\n",
				title,
				e.Level,
				e.CurrentLogQBits,
				e.ScaleModT,
				e.NoiseBudgetBits,
				e.MaxCoeffNoiseAbs,
				e.RequiredBitsRaw,
				mismatch)
		}
		return nil
	}

	// Lightweight standalone probe: enabled by -ct2-noise-probe even when the full
	// polynomial noise trace is disabled. It reuses the same decrypt/encode residual
	// convention as the exact poly-noise trace.
	if globalCt2NoiseProbe && globalMulTracer != nil {
		probeStart := time.Now()
		probe, err := probeCipherNoiseAgainstSlots(globalMulTracer.Params, globalMulTracer.Encoder, globalMulTracer.Dec, ct, expectedSlots, 0, name)
		globalMulTracer.ProbeTime += time.Since(probeStart)
		if err != nil {
			return err
		}
		if probe != nil {
			fmt.Printf("[immediate noise probe] %s: level=L%d/%db, scale mod T=%d, noiseBudget=%d bits, max|noise|=%s, requiredLogQ=%d\n",
				title,
				ct.Level(),
				probe.CurrentLogQBits,
				probe.ScaleModT,
				probe.CurrentLogQBits-probe.RequiredBitsNoMargin,
				probe.MaxCoeffNoiseAbs,
				probe.RequiredBitsNoMargin)
		}
	}
	return nil
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
	return mulCtRelinRescaleNamed(eval, ct0, op1, "")
}

func mulCtRelinRescaleNamed(eval *bfv.Evaluator, ct0 *rlwe.Ciphertext, op1 rlwe.Operand, traceName string) (*rlwe.Ciphertext, error) {
	st := time.Now()
	out, err := eval.MulRelinNew(ct0, op1)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(out, out); err != nil {
		return nil, err
	}
	var ct1 *rlwe.Ciphertext
	if v, ok := op1.(*rlwe.Ciphertext); ok {
		ct1 = v
	}
	logMulTrace(mulTraceName("mulCtRelinRescale", traceName), "ct-ct", ct0, ct1, out, true, time.Since(st), expectedForCtCtMul(out, ct0, ct1))
	return out, nil
}
func mulCtRelinNoRescaleNamed(eval *bfv.Evaluator, ct0 *rlwe.Ciphertext, op1 rlwe.Operand, traceName string) (*rlwe.Ciphertext, error) {
	st := time.Now()
	out, err := eval.MulRelinNew(ct0, op1)
	if err != nil {
		return nil, err
	}
	var ct1 *rlwe.Ciphertext
	if v, ok := op1.(*rlwe.Ciphertext); ok {
		ct1 = v
	}
	logMulTrace(mulTraceName("mulCtRelinNoRescale", traceName), "ct-ct", ct0, ct1, out, false, time.Since(st), expectedForCtCtMul(out, ct0, ct1))
	return out, nil
}

func shouldDeferAlg5PointwiseRescale(m int, ctY, ctG *rlwe.Ciphertext) bool {
	return globalDeferPointwiseRescale && ctY != nil && ctG != nil && ctY.Level() == ctG.Level() && ctY.Level() > 0
}

func alg5PointwiseMultiplyMaybeDeferred(eval *bfv.Evaluator, ctY, ctG *rlwe.Ciphertext, m, s int) (*rlwe.Ciphertext, int, error) {
	name := fmt.Sprintf("Algorithm 5 line 5: ctCollapsed = ct3 * ct2 = block-values * grouped-powers; s=%d", s)
	if shouldDeferAlg5PointwiseRescale(m, ctY, ctG) {
		out, err := mulCtRelinNoRescaleNamed(eval, ctY, ctG, name+"; deferred rescale after RotateAndSum")
		if err != nil {
			return nil, -1, err
		}
		return out, out.Level() - 1, nil
	}
	out, err := mulCtRelinRescaleNamed(eval, ctY, ctG, name)
	return out, -1, err
}

func rescaleAfterAlg5RotateAndSumIfNeeded(eval *bfv.Evaluator, ctBase *rlwe.Ciphertext, targetLevel int) (time.Duration, error) {
	if targetLevel < 0 {
		return 0, nil
	}
	return rescaleCiphertextToLevelWithTrace(eval, ctBase, targetLevel, "Algorithm 5 deferred rescale after RotateAndSum")
}

func mulCtLazyRelinRescale(eval *bfv.Evaluator, ct0 *rlwe.Ciphertext, op1 rlwe.Operand) (*rlwe.Ciphertext, error) {
	return mulCtLazyRelinRescaleNamed(eval, ct0, op1, "")
}

func mulCtLazyRelinRescaleNamed(eval *bfv.Evaluator, ct0 *rlwe.Ciphertext, op1 rlwe.Operand, traceName string) (*rlwe.Ciphertext, error) {
	st := time.Now()
	out, err := eval.MulNew(ct0, op1)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(out, out); err != nil {
		return nil, err
	}
	var ct1 *rlwe.Ciphertext
	if v, ok := op1.(*rlwe.Ciphertext); ok {
		ct1 = v
	}
	logMulTrace(mulTraceName("mulCtLazyRelinRescale", traceName), "ct-ct-lazy", ct0, ct1, out, true, time.Since(st), expectedForCtCtMul(out, ct0, ct1))
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
		polyRegisterExpected(out, fVec)
		timing.Total = time.Since(totalStart)
		return out, nil, timing, nil
	}

	powStart := time.Now()
	xPow := make([]*rlwe.Ciphertext, ell)
	xPow[0] = ct.CopyNew()
	polyCopyExpected(ct, xPow[0])
	for i := 1; i < ell; i++ {
		xPow[i], err = mulCtRelinRescaleNamed(eval, xPow[i-1], xPow[i-1], fmt.Sprintf("MonomialGen(s=%d): power chain xPow[%d] = xPow[%d]^2", s, i, i-1))
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed to compute x^(2^%d): %w", i, err)
		}
	}
	timing.BuildPowers = time.Since(powStart)

	var extra *rlwe.Ciphertext
	if wantExtra {
		extra = xPow[ell-1].CopyNew()
		polyCopyExpected(xPow[ell-1], extra)
	}

	yStart := time.Now()
	fVec := buildCoeffExtVector(coeffs, n, r, s, slots, T)
	cExt, dExt := buildBitMasks(n, r, s, slots)

	firstMask := hadamard(cExt[0], fVec, T)
	firstConst := hadamard(dExt[0], fVec, T)

	tmp, err := mulPlainRescaleNamed(eval, xPow[0], firstMask, fmt.Sprintf("MonomialGen(s=%d): first masked factor tmp = xPow[0] * C_0", s))
	if err != nil {
		return nil, nil, timing, fmt.Errorf("failed first masked multiply: %w", err)
	}
	acc, err := eval.AddNew(tmp, firstConst)
	if err != nil {
		return nil, nil, timing, fmt.Errorf("failed first masked add: %w", err)
	}
	polyRegisterExpectedAddPlain(acc, tmp, firstConst)

	for i := 1; i < ell; i++ {
		tmp, err = mulPlainRescaleNamed(eval, xPow[i], cExt[i], fmt.Sprintf("MonomialGen(s=%d): bit %d masked factor tmp = xPow[%d] * C_%d", s, i, i, i))
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed masked multiply at bit %d: %w", i, err)
		}
		factor, err := eval.AddNew(tmp, dExt[i])
		if err != nil {
			return nil, nil, timing, fmt.Errorf("failed masked add at bit %d: %w", i, err)
		}
		polyRegisterExpectedAddPlain(factor, tmp, dExt[i])
		acc, err = mulCtRelinRescaleNamed(eval, acc, factor, fmt.Sprintf("MonomialGen(s=%d): bit %d combine acc = acc * factor", s, i))
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

// buildShiftedMaskVectorInPlace is the allocation-light version of
// rotateWithinHalves(buildMaskVector(A, B, j, n, ell, r), -giantShift).
// The original two-step implementation allocated the full mask, two diagonal
// work arrays, and the rotated mask for every LT term. In the streaming LT path
// this happens O(ell) times, so for N=65536 and ell=1024 it creates several GiB
// of transient garbage. This routine writes the final shifted mask directly
// into a reusable buffer.
func buildShiftedMaskVectorInPlace(out []uint64, A, B [][][]uint64, j, n, ell, r int, giantShift int) []uint64 {
	total := r * n
	if cap(out) < total {
		out = make([]uint64, total)
	} else {
		out = out[:total]
	}

	halfCols := r / 2
	halfLen := halfCols * n

	// giantShift is always a multiple of n in Algorithm 2/3. Therefore the
	// rotation within each half is a row rotation, and we can avoid per-slot
	// division/modulo in the hot loop.
	shiftRows := 0
	if n > 0 {
		shiftRows = (-(giantShift / n)) % halfCols
		if shiftRows < 0 {
			shiftRows += halfCols
		}
	}

	for dstRow := 0; dstRow < halfCols; dstRow++ {
		srcRow := dstRow + shiftRows
		if srcRow >= halfCols {
			srcRow -= halfCols
		}
		rowMod := srcRow % ell
		col := srcRow + j
		if col >= halfCols {
			col -= halfCols
		}
		rowBase := dstRow * n
		for idx := 0; idx < n; idx++ {
			out[rowBase+idx] = A[idx][rowMod][col]
		}
	}

	base := halfLen
	for dstRow := 0; dstRow < halfCols; dstRow++ {
		srcRow := dstRow + shiftRows
		if srcRow >= halfCols {
			srcRow -= halfCols
		}
		rowMod := srcRow % ell
		col := srcRow + j
		if col >= halfCols {
			col -= halfCols
		}
		rowBase := base + dstRow*n
		for idx := 0; idx < n; idx++ {
			out[rowBase+idx] = B[idx][rowMod][col]
		}
	}

	return out
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
	polyRegisterExpectedRowSwap(out, ct)
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
		polyRegisterExpectedRotateColumns(rot, ctIn, k*n)
		baby[k] = rot
	}

	var acc *rlwe.Ciphertext
	var shiftedMaskBuf []uint64

	for i := 0; i < b; i++ {
		giantShift := i * g * n
		var block *rlwe.Ciphertext

		for k := 0; k < g; k++ {
			j := i*g + k
			if j >= ell {
				break
			}

			shiftedMask := buildShiftedMaskVectorInPlace(shiftedMaskBuf, A, B, j, n, ell, r, giantShift)
			shiftedMaskBuf = shiftedMask

			stMul := time.Now()
			term, err := eval.MulNew(baby[k], shiftedMask)
			if err != nil {
				return nil, fmt.Errorf("alg2 bsgs term multiply i=%d k=%d j=%d failed: %w", i, k, j, err)
			}
			durMul := time.Since(stMul)
			tm.PlaintextCipherMul += durMul
			if mulTraceActive() {
				logMulTrace(fmt.Sprintf("ParallelLT/BSGS(stream): term = baby[%d] * shiftedMask[j=%d], giant block i=%d", k, j, i), "ct-pt-LT", baby[k], nil, term, false, durMul, expectedForCtPlainMul(baby[k], shiftedMask))
			}

			if block == nil {
				block = term
			} else {
				oldBlockExpected := polyExpectedClone(block)
				if err := eval.Add(block, term, block); err != nil {
					return nil, fmt.Errorf("alg2 bsgs block add i=%d k=%d j=%d failed: %w", i, k, j, err)
				}
				polyRegisterExpectedAddSaved(block, oldBlockExpected, term)
			}
		}

		if block == nil {
			continue
		}

		if giantShift == 0 {
			if acc == nil {
				acc = block
			} else {
				oldAccExpected := polyExpectedClone(acc)
				if err := eval.Add(acc, block, acc); err != nil {
					return nil, fmt.Errorf("alg2 bsgs acc add i=%d failed: %w", i, err)
				}
				polyRegisterExpectedAddSaved(acc, oldAccExpected, block)
			}
		} else {
			rot := bfv.NewCiphertext(params, 1, block.Level())
			galEl := params.GaloisElementForColRotation(giantShift)
			stRot := time.Now()
			if err := eval.Automorphism(block, galEl, rot); err != nil {
				return nil, fmt.Errorf("alg2 bsgs giant rotation i=%d failed: %w", i, err)
			}
			tm.GiantRotations += time.Since(stRot)
			polyRegisterExpectedRotateColumns(rot, block, giantShift)
			if acc == nil {
				acc = rot
			} else {
				oldAccExpected := polyExpectedClone(acc)
				if err := eval.Add(acc, rot, acc); err != nil {
					return nil, fmt.Errorf("alg2 bsgs giant add i=%d failed: %w", i, err)
				}
				polyRegisterExpectedAddSaved(acc, oldAccExpected, rot)
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
		polyRegisterExpectedRotateColumns(rot, ct, shift)
		oldCtExpected := polyExpectedClone(ct)
		if err := eval.Add(ct, rot, ct); err != nil {
			return fmt.Errorf("alg2 sum-columns add s=%d failed: %w", s, err)
		}
		polyRegisterExpectedAddSaved(ct, oldCtExpected, rot)
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
		oldYExpected := polyExpectedClone(y)
		tauY, err := rowSwapCipher(params, eval, y)
		if err != nil {
			return nil, tm, fmt.Errorf("alg3 row swap failed: %w", err)
		}
		if err := eval.Add(y, tauY, y); err != nil {
			return nil, tm, fmt.Errorf("alg3 add y+tau(y) failed: %w", err)
		}
		polyRegisterExpectedAddSaved(y, oldYExpected, tauY)
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
	oldYExpected := polyExpectedClone(y)
	if err := eval.Add(y, yPrime, y); err != nil {
		return nil, tm, fmt.Errorf("alg3 add y+y' failed: %w", err)
	}
	polyRegisterExpectedAddSaved(y, oldYExpected, yPrime)
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
		oldYExpected := polyExpectedClone(y)
		tauY, err := rowSwapCipher(params, eval, y)
		if err != nil {
			return nil, tm, fmt.Errorf("alg3 row swap failed: %w", err)
		}
		if err := eval.Add(y, tauY, y); err != nil {
			return nil, tm, fmt.Errorf("alg3 add y+tau(y) failed: %w", err)
		}
		polyRegisterExpectedAddSaved(y, oldYExpected, tauY)
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
	oldYExpected := polyExpectedClone(y)
	if err := eval.Add(y, yPrime, y); err != nil {
		return nil, tm, fmt.Errorf("alg3 add y+y' failed: %w", err)
	}
	polyRegisterExpectedAddSaved(y, oldYExpected, yPrime)
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

func rescaleCiphertextToLevelWithTrace(eval *bfv.Evaluator, ct *rlwe.Ciphertext, targetLevel int, label string) (time.Duration, error) {
	if ct == nil {
		return 0, errors.New("cannot rescale a nil ciphertext")
	}
	if targetLevel < 0 {
		return 0, nil
	}
	if targetLevel > ct.Level() {
		return 0, fmt.Errorf("target level %d exceeds current level %d", targetLevel, ct.Level())
	}
	var total time.Duration
	for ct.Level() > targetLevel {
		before := ct.CopyNew()
		beforeLevel := before.Level()
		expectedOut, _ := polyExpected(ct)
		if expectedOut != nil {
			expectedOut = append([]uint64(nil), expectedOut...)
		}
		st := time.Now()
		if err := eval.Rescale(ct, ct); err != nil {
			return total, fmt.Errorf("final rescale to level %d failed at level %d: %w", targetLevel, beforeLevel, err)
		}
		dur := time.Since(st)
		total += dur
		if ct.Level() >= beforeLevel {
			return total, fmt.Errorf("final rescale to level %d made no progress: ciphertext level stayed at %d", targetLevel, beforeLevel)
		}
		logOpTrace(fmt.Sprintf("%s: final Rescale/ModSwitch L%d -> L%d", label, beforeLevel, ct.Level()), "final-rescale", before, nil, ct, true, dur, expectedOut)
	}
	return total, nil
}

const ltLevelExtraCT2Level = -2
const ltPostAutoCT2Level = -2

func resolveParallelLTLevelPolicy(ctPLevel, ct2Level int, dropBeforeLT bool, ltLevel, ltPostLevel int, deferLTPostRescale bool) (inputLevel, postLevel int, err error) {
	if ctPLevel < 0 {
		return 0, 0, fmt.Errorf("invalid ParallelLT ct1/ctP level %d", ctPLevel)
	}
	if ct2Level < 0 {
		return 0, 0, fmt.Errorf("invalid ParallelLT ct2/grouped-powers level %d", ct2Level)
	}
	if ltLevel < ltLevelExtraCT2Level {
		return 0, 0, fmt.Errorf("invalid ParallelLT level %d; use -2 for extra-level auto, -1 for fast auto, or a nonnegative manual level", ltLevel)
	}
	if ltPostLevel < ltPostAutoCT2Level {
		return 0, 0, fmt.Errorf("invalid post-ParallelLT level %d; use -2 for auto ct2 level, -1 to disable, or a nonnegative level", ltPostLevel)
	}

	inputLevel = ctPLevel
	if ltLevel >= 0 {
		inputLevel = ltLevel
	} else if dropBeforeLT && ltLevel == ltLevelExtraCT2Level {
		// Optional safer policy: run BatchLT one level above the grouped-powers
		// ciphertext and rescale afterwards. This is slower because every LT
		// plaintext-ciphertext multiplication carries one extra Q-prime.
		inputLevel = ct2Level + 1
		if inputLevel > ctPLevel {
			inputLevel = ctPLevel
		}
	} else if dropBeforeLT && ctPLevel > ct2Level {
		// Fast default policy: match the original implementation and run BatchLT
		// directly at the grouped-powers ciphertext level.
		inputLevel = ct2Level
	}
	if inputLevel < 0 {
		return 0, 0, fmt.Errorf("ParallelLT input level became negative: L%d", inputLevel)
	}
	if inputLevel > ctPLevel {
		return 0, 0, fmt.Errorf("requested ParallelLT level L%d exceeds ct1/ctP level L%d", inputLevel, ctPLevel)
	}

	postLevel = -1
	switch {
	case ltPostLevel == ltPostAutoCT2Level:
		postLevel = ct2Level
	case ltPostLevel == -1:
		postLevel = -1
	case ltPostLevel >= 0:
		postLevel = ltPostLevel
	}
	if deferLTPostRescale {
		// Experimental policy: do not normalize the BatchLT output here.
		// The following ct3*ct2 ciphertext-ciphertext multiplication will perform
		// the single rescale, so ct3 and ct2 should usually be evaluated at the
		// same level (the fast default -lt-level=-1 does exactly this).
		postLevel = -1
	}
	if postLevel >= 0 && postLevel > inputLevel {
		return 0, 0, fmt.Errorf("post-ParallelLT target L%d exceeds BatchLT output/input level L%d", postLevel, inputLevel)
	}
	return inputLevel, postLevel, nil
}

func applyParallelLTLevelPolicy(eval *bfv.Evaluator, ctP, ct2 *rlwe.Ciphertext, dropBeforeLT bool, ltLevel, ltPostLevel int, deferLTPostRescale bool) (inputLevel, postLevel int, err error) {
	if ctP == nil || ct2 == nil {
		return 0, 0, errors.New("nil ciphertext passed to ParallelLT level policy")
	}
	inputLevel, postLevel, err = resolveParallelLTLevelPolicy(ctP.Level(), ct2.Level(), dropBeforeLT, ltLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return 0, 0, err
	}
	if ctP.Level() > inputLevel {
		eval.DropLevel(ctP, ctP.Level()-inputLevel)
	}
	return inputLevel, postLevel, nil
}

func rescaleParallelLTOutputToPolicy(eval *bfv.Evaluator, ctY *rlwe.Ciphertext, targetLevel int, label string) (time.Duration, error) {
	if ctY == nil {
		return 0, errors.New("nil BatchLT output ciphertext")
	}
	if targetLevel < 0 {
		return 0, nil
	}
	if targetLevel > ctY.Level() {
		return 0, fmt.Errorf("post-ParallelLT target L%d exceeds BatchLT output level L%d", targetLevel, ctY.Level())
	}
	if ctY.Level() == targetLevel {
		return 0, nil
	}
	return rescaleCiphertextToLevelWithTrace(eval, ctY, targetLevel, label)
}

func formatParallelLTLevelPolicy(dropBeforeLT bool, ltLevel, ltPostLevel int, deferLTPostRescale bool) string {
	input := "auto ct2.Level()"
	if ltLevel == ltLevelExtraCT2Level {
		input = "auto ct2.Level()+1"
	} else if ltLevel >= 0 {
		input = fmt.Sprintf("manual L%d", ltLevel)
	} else if !dropBeforeLT {
		input = "no pre-drop; use ct1/ctP current level"
	}
	post := "auto ct2.Level()"
	switch {
	case ltPostLevel == -1:
		post = "disabled"
	case ltPostLevel >= 0:
		post = fmt.Sprintf("manual L%d", ltPostLevel)
	}
	if deferLTPostRescale {
		post = post + "; deferred until ct3*ct2"
	}
	return fmt.Sprintf("BatchLT input %s; post-BatchLT rescale %s", input, post)
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
	polyCopyExpected(ct, h)
	for i := 0; i < ell-1; i++ {
		shift := baseLen * (1 << i)
		stRot := time.Now()
		rot, err := eval.RotateColumnsNew(h, shift)
		durRot := time.Since(stRot)
		if err != nil {
			return nil, fmt.Errorf("RotateColumns(%d) failed: %w", shift, err)
		}
		logOpTrace(fmt.Sprintf("RotateAndSum: Algorithm 5 line 7 ColumnRotation step=%d shift=%d", i, shift), "rot-col", h, nil, rot, false, durRot, expectedForRotateColumns(h, shift))
		stAdd := time.Now()
		sum, err := eval.AddNew(h, rot)
		durAdd := time.Since(stAdd)
		if err != nil {
			return nil, fmt.Errorf("Add after RotateColumns(%d) failed: %w", shift, err)
		}
		logOpTrace(fmt.Sprintf("RotateAndSum: Algorithm 5 line 7 Add rotated value step=%d shift=%d", i, shift), "add", h, rot, sum, false, durAdd, expectedForAdd(h, rot))
		h = sum
	}
	if s == r {
		stRot := time.Now()
		rot, err := eval.RotateRowsNew(h)
		durRot := time.Since(stRot)
		if err != nil {
			return nil, fmt.Errorf("RotateRows failed: %w", err)
		}
		logOpTrace("RotateAndSum: Algorithm 5 line 10 RowRotation final half-sum", "rot-row", h, nil, rot, false, durRot, expectedForRowSwap(h))
		stAdd := time.Now()
		sum, err := eval.AddNew(h, rot)
		durAdd := time.Since(stAdd)
		if err != nil {
			return nil, fmt.Errorf("Add after RotateRows failed: %w", err)
		}
		logOpTrace("RotateAndSum: Algorithm 5 line 10 Add RowRotation final half-sum", "add", h, rot, sum, false, durAdd, expectedForAdd(h, rot))
		h = sum
	} else {
		shift := baseLen * (1 << (ell - 1))
		stRot := time.Now()
		rot, err := eval.RotateColumnsNew(h, shift)
		durRot := time.Since(stRot)
		if err != nil {
			return nil, fmt.Errorf("final RotateColumns(%d) failed: %w", shift, err)
		}
		logOpTrace(fmt.Sprintf("RotateAndSum: Algorithm 5 line 12 final ColumnRotation shift=%d", shift), "rot-col", h, nil, rot, false, durRot, expectedForRotateColumns(h, shift))
		stAdd := time.Now()
		sum, err := eval.AddNew(h, rot)
		durAdd := time.Since(stAdd)
		if err != nil {
			return nil, fmt.Errorf("final Add after RotateColumns(%d) failed: %w", shift, err)
		}
		logOpTrace(fmt.Sprintf("RotateAndSum: Algorithm 5 line 12 final Add after ColumnRotation shift=%d", shift), "add", h, rot, sum, false, durAdd, expectedForAdd(h, rot))
		h = sum
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
	ctLead, err := mulPlainRescaleNamed(eval, ctPowD, leadVec, "Leading term: ctLead = x^d * sparse leading-coefficient vector a_d")
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

func polyEvalSparsePow2Alg5(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64, dropBeforeLT bool, ltDropLevel, ltPostLevel int, deferLTPostRescale bool) (*rlwe.Ciphertext, PolyEvalTiming, error) {
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
	ctR, err := mulCtRelinRescaleNamed(eval, ctHalf, ctHalf, fmt.Sprintf("Algorithm 5 line 2: ctR = (x^(r/2))^2 = x^r; r=%d", r))
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
	if (polyNoiseTraceActiveForCurrentContext(m) || globalCt2NoiseProbe || mulTraceNoiseActive()) && len(globalPolyNoiseBase) > 0 {
		mod := params.PlaintextModulus()
		base := globalPolyNoiseBase
		xR := powVectorMod(base, r, mod)
		if err := maybeTraceAndPrintImmediatePolyNoise("poly/LUT alg5: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(m, s), r, mod), "Algorithm 5 line 3 output c2/ct2 grouped powers"); err != nil {
			return nil, tm, err
		}
	}
	_, resolvedLTPostLevel, err := applyParallelLTLevelPolicy(eval, ctP, ctG, dropBeforeLT, ltDropLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT level policy failed: %w", err)
	}
	U := buildPatersonStockmeyerMatrices(coeffsLower, r)
	ctY, _, err := parallelLT3BSGSHoisted(params, eval, ctP, U, m, s, r)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	if _, err := rescaleParallelLTOutputToPolicy(eval, ctY, resolvedLTPostLevel, "Post-ParallelLT normalization to ct2/grouped-powers level"); err != nil {
		return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
	}
	alignCiphertextLevels(eval, ctY, ctG)
	logInputPairCheckpoint("Algorithm 5 line 5 inputs before Mult: c3/ct3=BatchLT output, c2/ct2=grouped powers", "c3", ctY, "c2", ctG)
	ctCollapsed, deferredPointwiseRescaleLevel, err := alg5PointwiseMultiplyMaybeDeferred(eval, ctY, ctG, m, s)
	if err != nil {
		return nil, tm, fmt.Errorf("pointwise multiplication y*g failed: %w", err)
	}
	ctBase, err := sparseRotateAndSum(params, eval, ctCollapsed, m, s)
	if err != nil {
		return nil, tm, err
	}
	if _, err := rescaleAfterAlg5RotateAndSumIfNeeded(eval, ctBase, deferredPointwiseRescaleLevel); err != nil {
		return nil, tm, fmt.Errorf("deferred rescale after RotateAndSum failed: %w", err)
	}
	ctPowD, err := mulCtRelinRescaleNamed(eval, ctDHalf, ctDHalf, fmt.Sprintf("Leading term: ctPowD = (x^(d/2))^2 = x^d; d=%d", d))
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

func polyEvalSparsePow2Alg5LargeBranch(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64, preLT *PreprocessedParallelLT3, dropBeforeLT bool, ltDropLevel, ltPostLevel int, deferLTPostRescale bool) (*rlwe.Ciphertext, PolyEvalTiming, error) {
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
	ctR, err := mulCtRelinRescaleNamed(eval, ctHalf, ctHalf, fmt.Sprintf("Algorithm 5 line 2: ctR = (x^(r/2))^2 = x^r; r=%d", r))
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
	if (traceEnabled || globalCt2NoiseProbe || mulTraceNoiseActive()) && len(base) > 0 {
		xR := powVectorMod(base, r, mod)
		if err := maybeTraceAndPrintImmediatePolyNoise("poly/LUT alg5-large: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(m, s), r, mod), "Algorithm 5 line 3 output c2/ct2 grouped powers"); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, d/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	_, resolvedLTPostLevel, err := applyParallelLTLevelPolicy(eval, ctP, ctG, dropBeforeLT, ltDropLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT level policy failed: %w", err)
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
	if _, err := rescaleParallelLTOutputToPolicy(eval, ctY, resolvedLTPostLevel, "Post-ParallelLT normalization to ct2/grouped-powers level"); err != nil {
		return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}

	progressf("poly eval (alg5-large): multiplying ParallelLT output with grouped powers")
	alignCiphertextLevels(eval, ctY, ctG)
	logInputPairCheckpoint("Algorithm 5 line 5 inputs before Mult: c3/ct3=BatchLT output, c2/ct2=grouped powers", "c3", ctY, "c2", ctG)
	deferredPointwiseRescaleLevel := -1
	ctCollapsed, deferredPointwiseRescaleLevel, err = alg5PointwiseMultiplyMaybeDeferred(eval, ctY, ctG, m, s)
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
	if _, err := rescaleAfterAlg5RotateAndSumIfNeeded(eval, ctBase, deferredPointwiseRescaleLevel); err != nil {
		return nil, tm, fmt.Errorf("deferred rescale after RotateAndSum failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	progressf("poly eval (alg5-large): computing x^d")
	ctPowD, err := mulCtRelinRescaleNamed(eval, ctDHalf, ctDHalf, fmt.Sprintf("Leading term: ctPowD = (x^(d/2))^2 = x^d; d=%d", d))
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^d", ctPowD, repeatVector(powVectorMod(base, d, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	ctLead, err := mulPlainRescaleNamed(eval, ctPowD, sparsePackLeadingOrPanic(leadCoeffs, params.MaxSlots()), "Leading term: ctLead = ctPowD * sparse leading-coefficient vector a_d")
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
	// The current StC implementation accumulates the whole BSGS linear transform
	// at the input level and only rescales after StC. Therefore both baby and
	// giant rotations need keys at inputLevel.
	for i := 1; i < b; i++ {
		shift := i * g
		if shift < n {
			plan.AddColRotation(params, shift, inputLevel, "SlotToCoeff giant")
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

func addPolyEvalRotationKeyUses(params bfv.Parameters, plan *RotationKeyPlan, polyInputLevel, m, d int, dropBeforeLT bool, ltDropLevel, ltPostLevel int, deferLTPostRescale bool, leadingTermEvaluated bool) (PolyRotationLevelInfo, error) {
	info := PolyRotationLevelInfo{InputLevel: polyInputLevel}
	if info.InputLevel < 0 || info.InputLevel > params.MaxLevel() {
		return info, fmt.Errorf("invalid polynomial input level L%d for MaxLevel=%d", info.InputLevel, params.MaxLevel())
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

	ltInputLevel, ltOutputLevel, err := resolveParallelLTLevelPolicy(ctPLevel, ctGLevel, dropBeforeLT, ltDropLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return info, err
	}
	if err := checkPlannedLevel(ltInputLevel, "ParallelLT input"); err != nil {
		return info, err
	}
	info.LTInputLevel = ltInputLevel
	if err := addNeededGaloisElsAlg3KeyUsesAtLevel(params, plan, m, s, r, ltInputLevel, "poly ParallelLT"); err != nil {
		return info, err
	}
	if ltOutputLevel < 0 {
		ltOutputLevel = ltInputLevel
	}
	info.LTOutputLevel = ltOutputLevel
	collapseInputLevel := minInt(ltOutputLevel, ctGLevel)
	collapsedLevel := collapseInputLevel - 1
	if err := checkPlannedLevel(collapsedLevel, "post-ParallelLT collapsed ciphertext"); err != nil {
		return info, err
	}
	finalSumLevel := collapsedLevel
	if globalDeferPointwiseRescale {
		finalSumLevel = collapseInputLevel
	}
	info.FinalSumLevel = finalSumLevel
	if err := addSparseRotateAndSumKeyUses(params, plan, m, s, finalSumLevel, "poly final rotate-sum"); err != nil {
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

func plaintextLevel(pt *rlwe.Plaintext) int {
	if pt == nil {
		return -1
	}
	return len(pt.Value.Coeffs) - 1
}

func plaintextPayloadBytes(pt *rlwe.Plaintext) int64 {
	if pt == nil {
		return 0
	}
	var total int64
	for _, coeffs := range pt.Value.Coeffs {
		total += int64(len(coeffs)) * 8
	}
	return total
}

type PlaintextMemoryStat struct {
	Category string
	Level    int
	Count    int
	Bytes    int64
}

func addPlaintextMemoryStat(stats map[string]*PlaintextMemoryStat, category string, pt *rlwe.Plaintext) {
	if pt == nil {
		return
	}
	level := plaintextLevel(pt)
	key := fmt.Sprintf("%s|%d", category, level)
	st := stats[key]
	if st == nil {
		st = &PlaintextMemoryStat{Category: category, Level: level}
		stats[key] = st
	}
	st.Count++
	st.Bytes += plaintextPayloadBytes(pt)
}

func collectMonomialPlaintextMemoryStats(stats map[string]*PlaintextMemoryStat, category string, pre *PreprocessedMonomial) {
	if pre == nil {
		return
	}
	addPlaintextMemoryStat(stats, category, pre.FirstMaskPT)
	for _, pt := range pre.CMaskPT {
		addPlaintextMemoryStat(stats, category, pt)
	}
}

func collectParallelLT2PlaintextMemoryStats(stats map[string]*PlaintextMemoryStat, category string, pre *PreprocessedParallelLT2) {
	if pre == nil {
		return
	}
	for _, pt := range pre.ShiftedMaskPT {
		addPlaintextMemoryStat(stats, category, pt)
	}
}

func collectParallelLT3PlaintextMemoryStats(stats map[string]*PlaintextMemoryStat, category string, pre *PreprocessedParallelLT3) {
	if pre == nil {
		return
	}
	collectParallelLT2PlaintextMemoryStats(stats, category, pre.Pre1)
	collectParallelLT2PlaintextMemoryStats(stats, category, pre.Pre2)
}

func collectPolyPrecomputePlaintextMemoryStats(pre *PreprocessedPolyEval) []PlaintextMemoryStat {
	if pre == nil {
		return nil
	}
	stats := make(map[string]*PlaintextMemoryStat)
	addPlaintextMemoryStat(stats, "leading coefficient", pre.LeadPT)
	collectMonomialPlaintextMemoryStats(stats, "monomial lower", pre.LowerMon)
	collectMonomialPlaintextMemoryStats(stats, "monomial basis/r", pre.OnesRMon)
	collectMonomialPlaintextMemoryStats(stats, "monomial grouped/s", pre.OnesSMon)
	collectParallelLT3PlaintextMemoryStats(stats, "ParallelLT masks", pre.LT)
	out := make([]PlaintextMemoryStat, 0, len(stats))
	for _, st := range stats {
		out = append(out, *st)
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].Category != out[j].Category {
			return out[i].Category < out[j].Category
		}
		return out[i].Level < out[j].Level
	})
	return out
}

func printPolyPrecomputePlaintextMemorySummary(params bfv.Parameters, pre *PreprocessedPolyEval) {
	if pre == nil {
		return
	}
	stats := collectPolyPrecomputePlaintextMemoryStats(pre)
	var totalBytes int64
	var totalCount int
	for _, st := range stats {
		totalBytes += st.Bytes
		totalCount += st.Count
	}
	fmt.Printf("precomputed plaintext mode : %s\n", pre.Mode)
	fmt.Printf("precompute level plan      : input L%d", pre.InputLevel)
	if pre.CT1Level >= 0 || pre.CT2Level >= 0 || pre.LTLevel >= 0 {
		fmt.Printf(", ct1/ctP L%d, ct2 L%d, BatchLT L%d", pre.CT1Level, pre.CT2Level, pre.LTLevel)
		if pre.LTPostLevel >= 0 {
			fmt.Printf(" -> post-LT L%d", pre.LTPostLevel)
		} else {
			fmt.Printf(" -> post-LT disabled")
		}
	}
	if pre.LeadPT != nil {
		fmt.Printf(", lead L%d", pre.LeadLevel)
	}
	fmt.Println()
	fmt.Printf("precomputed plaintext mem  : %s coefficient payload over %d plaintext(s)\n", formatBytesIEC(totalBytes), totalCount)
	if len(stats) == 0 {
		return
	}
	rows := make([][]string, 0, len(stats))
	for _, st := range stats {
		logQ := "-"
		if st.Level >= 0 && st.Level <= params.MaxLevel() {
			logQ = fmt.Sprintf("%d", qBitsOfLevel(params, st.Level))
		}
		rows = append(rows, []string{
			st.Category,
			fmt.Sprintf("L%d", st.Level),
			logQ,
			fmt.Sprintf("%d", st.Count),
			formatBytesIEC(st.Bytes),
		})
	}
	printAlignedPipeTable(
		[]string{"plaintext group", "LevelQ", "logQ", "count", "payload memory"},
		rows,
		[]bool{false, true, true, true, true},
	)
}

func printEvaluationKeyLevelSummary(params bfv.Parameters, relinLevel int, relinSizeBytes int64, rotationStats []RotationKeyLevelStat, totalEvalKeyBytes int64, levelAware bool) {
	policy := "level-aware"
	if !levelAware {
		policy = "full-chain"
	}
	fmt.Printf("evaluation key policy      : %s Q-level generation\n", policy)
	rows := make([][]string, 0, 1+len(rotationStats)+1)
	if relinLevel >= 0 {
		rows = append(rows, []string{
			"Relinearization",
			fmt.Sprintf("L%d", relinLevel),
			fmt.Sprintf("%d", qBitsOfLevel(params, relinLevel)),
			"1",
			formatBytesIEC(relinSizeBytes),
		})
	}
	for _, st := range rotationStats {
		rows = append(rows, []string{
			"Galois/rotation",
			fmt.Sprintf("L%d", st.LevelQ),
			fmt.Sprintf("%d", st.LogQBits),
			fmt.Sprintf("%d", st.Count),
			formatBytesIEC(st.SizeBytes),
		})
	}
	rows = append(rows, []string{"Total eval keys", "-", "-", "-", formatBytesIEC(totalEvalKeyBytes)})
	printAlignedPipeTable(
		[]string{"key type", "LevelQ", "logQ", "count", "size"},
		rows,
		[]bool{false, true, true, true, true},
	)
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

func polyEvalSparsePow2Alg5Precomp(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, pre *PreprocessedPolyEval, dropBeforeLT bool, ltDropLevel, ltPostLevel int, deferLTPostRescale bool) (*rlwe.Ciphertext, PolyEvalTiming, error) {
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
	ctR, err := mulCtRelinRescaleNamed(eval, ctHalf, ctHalf, fmt.Sprintf("Algorithm 5 line 2: ctR = (x^(r/2))^2 = x^r; r=%d", r))
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
	if (traceEnabled || globalCt2NoiseProbe || mulTraceNoiseActive()) && len(base) > 0 {
		xR := powVectorMod(base, r, mod)
		if err := maybeTraceAndPrintImmediatePolyNoise("poly/LUT alg5: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(pre.M, s), r, mod), "Algorithm 5 line 3 output c2/ct2 grouped powers"); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, pre.D/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	_, resolvedLTPostLevel, err := applyParallelLTLevelPolicy(eval, ctP, ctG, dropBeforeLT, ltDropLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT level policy failed: %w", err)
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
	if _, err := rescaleParallelLTOutputToPolicy(eval, ctY, resolvedLTPostLevel, "Post-ParallelLT normalization to ct2/grouped-powers level"); err != nil {
		return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	alignCiphertextLevels(eval, ctY, ctG)
	logInputPairCheckpoint("Algorithm 5 line 5 inputs before Mult: c3/ct3=BatchLT output, c2/ct2=grouped powers", "c3", ctY, "c2", ctG)
	progressf("poly eval (alg5): multiplying ParallelLT output with grouped powers")
	ctCollapsed, deferredPointwiseRescaleLevel, err := alg5PointwiseMultiplyMaybeDeferred(eval, ctY, ctG, pre.M, s)
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
	if _, err := rescaleAfterAlg5RotateAndSumIfNeeded(eval, ctBase, deferredPointwiseRescaleLevel); err != nil {
		return nil, tm, fmt.Errorf("deferred rescale after RotateAndSum failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	progressf("poly eval (alg5): computing x^d")
	ctPowD, err := mulCtRelinRescaleNamed(eval, ctDHalf, ctDHalf, fmt.Sprintf("Leading term: ctPowD = (x^(d/2))^2 = x^d; d=%d", pre.D))
	if err != nil {
		return nil, tm, fmt.Errorf("squaring x^(d/2) to x^d failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: x^d", ctPowD, repeatVector(powVectorMod(base, pre.D, mod), r)); err != nil {
			return nil, tm, err
		}
	}
	ctLead, err := mulOperandRescaleNamedWithPlain(eval, ctPowD, pre.LeadPT, pre.LeadVec, "Leading term: ctLead = ctPowD * precomputed leading-coefficient plaintext a_d")
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
	NoiseBudgetBits         int
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
		ScaleModT:               scaleModUint64(ct.Scale, params.PlaintextModulus()),
		MaxCoeffNoiseAbs:        maxAbs.String(),
		RequiredBitsNoMargin:    noMargin,
		RecommendedBits:         recommended,
		NoiseBudgetBits:         currentBits - noMargin,
		SmallestSafeLevel:       smallestSafeLevel,
		SmallestSafeLogQBits:    smallestSafeBits,
		SafeDropLevelsWithGuard: safeDropLevels,
	}, nil
}

func probeCipherNoiseAgainstCoeffs(params bfv.Parameters, encoder *bfv.Encoder, dec *rlwe.Decryptor, ct *rlwe.Ciphertext, expectedCoeffs []uint64, safetyBits int, name string) (*NoiseProbeResult, error) {
	ptGot := dec.DecryptNew(ct)
	ptRef := bfv.NewPlaintext(params, ct.Level())
	ptRef.Scale = ct.Scale
	ptRef.IsBatched = false
	coeffs := make([]uint64, params.N())
	for i := range coeffs {
		if i < len(expectedCoeffs) {
			coeffs[i] = expectedCoeffs[i] % params.PlaintextModulus()
		}
	}
	if err := encoder.Encode(coeffs, ptRef); err != nil {
		return nil, fmt.Errorf("failed to encode expected coefficient plaintext for probe %q: %w", name, err)
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
		ScaleModT:               scaleModUint64(ct.Scale, params.PlaintextModulus()),
		MaxCoeffNoiseAbs:        maxAbs.String(),
		RequiredBitsNoMargin:    noMargin,
		RecommendedBits:         recommended,
		NoiseBudgetBits:         currentBits - noMargin,
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
	fmt.Printf("  coefficient noise budget : %d bits\n", p.NoiseBudgetBits)
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
	FinalRescale         time.Duration
	PowerGen             time.Duration
	OuterCombine         time.Duration
}

type BenchPolyEvalTiming struct {
	Algorithm string
	Total     time.Duration
	Breakdown BenchPolyEvalBreakdown
}

type BenchDynamicSetupTiming struct {
	FunctionTable      time.Duration
	LUTBuild           time.Duration
	LWECiphertexts     time.Duration
	PolyPrecompute     time.Duration
	M1GammaCalibration time.Duration
	Total              time.Duration
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
	Run           int
	FuncSeed      int64
	LWENoiseSeed  int64
	LWEASeed      int64
	MsgSeed       int64
	FuncDesc      string
	Dynamic       BenchDynamicSetupTiming
	Online        BenchOnlineTiming
	Wall          time.Duration
	NoiseDiffs    []int64
	NoiseMean     float64
	NoiseStd      float64
	NoiseMaxAbs   int64
	QBeforeDiffs  []int64
	QAfterDiffs   []int64
	QKSDiffs      []int64
	QExtractDiffs []int64
	PolyPlainOK   bool
	CoeffOK       bool
	DecodeOK      bool
	Correct       bool
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

func benchPolyEvalSparsePow2Alg5Precomp(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, pre *PreprocessedPolyEval, dropBeforeLT bool, ltDropLevel, ltPostLevel int, deferLTPostRescale bool) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
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
	ctR, err := mulCtRelinRescaleNamed(eval, ctHalf, ctHalf, fmt.Sprintf("Algorithm 5 line 2: ctR = (x^(r/2))^2 = x^r; r=%d", r))
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
	if (traceEnabled || globalCt2NoiseProbe || mulTraceNoiseActive()) && len(base) > 0 {
		xR := powVectorMod(base, r, mod)
		if err := maybeTraceAndPrintImmediatePolyNoise("poly/LUT alg5: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(pre.M, s), r, mod), "Algorithm 5 line 3 output c2/ct2 grouped powers"); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, pre.D/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	_, resolvedLTPostLevel, err := applyParallelLTLevelPolicy(eval, ctP, ctG, dropBeforeLT, ltDropLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT level policy failed: %w", err)
	}

	ltStart := time.Now()
	ctY, ltTiming, err := parallelLT3BSGSHoistedPrecomp(params, eval, ctP, pre.LT, pre.M, s, r)
	ltCoreDuration := time.Since(ltStart)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (before post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	var ltPostRescale time.Duration
	ltPostRescale, err = rescaleParallelLTOutputToPolicy(eval, ctY, resolvedLTPostLevel, "Post-ParallelLT normalization to ct2/grouped-powers level")
	if err != nil {
		return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	setBenchLTBreakdown(&tm.Breakdown, ltCoreDuration+ltPostRescale, 0, ltPostRescale, ltTiming)

	st = time.Now()
	alignCiphertextLevels(eval, ctY, ctG)
	logInputPairCheckpoint("Algorithm 5 line 5 inputs before Mult: c3/ct3=BatchLT output, c2/ct2=grouped powers", "c3", ctY, "c2", ctG)
	ctCollapsed, deferredPointwiseRescaleLevel, err := alg5PointwiseMultiplyMaybeDeferred(eval, ctY, ctG, pre.M, s)
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
	if dur, err := rescaleAfterAlg5RotateAndSumIfNeeded(eval, ctBase, deferredPointwiseRescaleLevel); err != nil {
		return nil, tm, fmt.Errorf("deferred rescale after RotateAndSum failed: %w", err)
	} else {
		tm.Breakdown.FinalRescale += dur
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctPowD, err := mulCtRelinRescaleNamed(eval, ctDHalf, ctDHalf, fmt.Sprintf("Leading term: ctPowD = (x^(d/2))^2 = x^d; d=%d", pre.D))
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
	ctLead, err := mulOperandRescaleNamedWithPlain(eval, ctPowD, pre.LeadPT, pre.LeadVec, "Leading term: ctLead = ctPowD * precomputed leading-coefficient plaintext a_d")
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

func benchPolyEvalSparsePow2Alg5LargeBranch(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64, preLT *PreprocessedParallelLT3, dropBeforeLT bool, ltDropLevel, ltPostLevel int, deferLTPostRescale bool) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
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
	ctR, err := mulCtRelinRescaleNamed(eval, ctHalf, ctHalf, fmt.Sprintf("Algorithm 5 line 2: ctR = (x^(r/2))^2 = x^r; r=%d", r))
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
	if (traceEnabled || globalCt2NoiseProbe || mulTraceNoiseActive()) && len(base) > 0 {
		xR := powVectorMod(base, r, mod)
		if err := maybeTraceAndPrintImmediatePolyNoise("poly/LUT alg5-large: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(m, s), r, mod), "Algorithm 5 line 3 output c2/ct2 grouped powers"); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5-large: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, d/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	_, resolvedLTPostLevel, err := applyParallelLTLevelPolicy(eval, ctP, ctG, dropBeforeLT, ltDropLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT level policy failed: %w", err)
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
	ltCoreDuration := time.Since(ltStart)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: ParallelLT output (before post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	ltPostRescale, err = rescaleParallelLTOutputToPolicy(eval, ctY, resolvedLTPostLevel, "Post-ParallelLT normalization to ct2/grouped-powers level")
	if err != nil {
		return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5-large: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	setBenchLTBreakdown(&tm.Breakdown, ltCoreDuration+ltPostRescale, ltMatrixBuild, ltPostRescale, ltTiming)

	st = time.Now()
	alignCiphertextLevels(eval, ctY, ctG)
	logInputPairCheckpoint("Algorithm 5 line 5 inputs before Mult: c3/ct3=BatchLT output, c2/ct2=grouped powers", "c3", ctY, "c2", ctG)
	ctCollapsed, deferredPointwiseRescaleLevel, err := alg5PointwiseMultiplyMaybeDeferred(eval, ctY, ctG, m, s)
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
	if dur, err := rescaleAfterAlg5RotateAndSumIfNeeded(eval, ctBase, deferredPointwiseRescaleLevel); err != nil {
		return nil, tm, fmt.Errorf("deferred rescale after RotateAndSum failed: %w", err)
	} else {
		tm.Breakdown.FinalRescale += dur
	}
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
	ctPowD, err := mulCtRelinRescaleNamed(eval, ctDHalf, ctDHalf, fmt.Sprintf("Leading term: ctPowD = (x^(d/2))^2 = x^d; d=%d", d))
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
	ctLead, err := mulPlainRescaleNamed(eval, ctPowD, sparsePackLeadingOrPanic(leadCoeffs, params.MaxSlots()), "Leading term: ctLead = ctPowD * sparse leading-coefficient vector a_d")
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

func benchPolyEvalSparsePow2Alg5(params bfv.Parameters, eval *bfv.Evaluator, ct *rlwe.Ciphertext, m int, coeffsLower [][]uint64, leadCoeffs []uint64, dropBeforeLT bool, ltDropLevel, ltPostLevel int, deferLTPostRescale bool) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
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
	ctR, err := mulCtRelinRescaleNamed(eval, ctHalf, ctHalf, fmt.Sprintf("Algorithm 5 line 2: ctR = (x^(r/2))^2 = x^r; r=%d", r))
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
	if (traceEnabled || globalCt2NoiseProbe || mulTraceNoiseActive()) && len(base) > 0 {
		xR := powVectorMod(base, r, mod)
		if err := maybeTraceAndPrintImmediatePolyNoise("poly/LUT alg5: grouped powers of x^r", ctG, monomialGenReferenceSlots(xR, buildAllOnesCoeffs(m, s), r, mod), "Algorithm 5 line 3 output c2/ct2 grouped powers"); err != nil {
			return nil, tm, err
		}
		if err := maybeTracePolyNoise("poly/LUT alg5: x^(d/2)", ctDHalf, repeatVector(powVectorMod(base, d/2, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	_, resolvedLTPostLevel, err := applyParallelLTLevelPolicy(eval, ctP, ctG, dropBeforeLT, ltDropLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT level policy failed: %w", err)
	}

	stMatrix := time.Now()
	U := buildPatersonStockmeyerMatrices(coeffsLower, r)
	ltMatrixBuild := time.Since(stMatrix)

	ltStart := time.Now()
	ctY, ltTiming, err := parallelLT3BSGSHoisted(params, eval, ctP, U, m, s, r)
	ltCoreDuration := time.Since(ltStart)
	if err != nil {
		return nil, tm, fmt.Errorf("ParallelLT failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (before post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	var ltPostRescale time.Duration
	ltPostRescale, err = rescaleParallelLTOutputToPolicy(eval, ctY, resolvedLTPostLevel, "Post-ParallelLT normalization to ct2/grouped-powers level")
	if err != nil {
		return nil, tm, fmt.Errorf("post-ParallelLT rescale failed: %w", err)
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: ParallelLT output (after post-rescale)", ctY, expectedAlg5LTSlots(base, coeffsLower, r, mod)); err != nil {
			return nil, tm, err
		}
	}
	setBenchLTBreakdown(&tm.Breakdown, ltMatrixBuild+ltCoreDuration+ltPostRescale, ltMatrixBuild, ltPostRescale, ltTiming)

	st = time.Now()
	alignCiphertextLevels(eval, ctY, ctG)
	logInputPairCheckpoint("Algorithm 5 line 5 inputs before Mult: c3/ct3=BatchLT output, c2/ct2=grouped powers", "c3", ctY, "c2", ctG)
	ctCollapsed, deferredPointwiseRescaleLevel, err := alg5PointwiseMultiplyMaybeDeferred(eval, ctY, ctG, m, s)
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
	if dur, err := rescaleAfterAlg5RotateAndSumIfNeeded(eval, ctBase, deferredPointwiseRescaleLevel); err != nil {
		return nil, tm, fmt.Errorf("deferred rescale after RotateAndSum failed: %w", err)
	} else {
		tm.Breakdown.FinalRescale += dur
	}
	if traceEnabled {
		if err := maybeTracePolyNoise("poly/LUT alg5: lower polynomial after rotate-sum", ctBase, repeatVector(evaluatePolysPerSlot(base, coeffsLower, mod), r)); err != nil {
			return nil, tm, err
		}
	}

	st = time.Now()
	ctPowD, err := mulCtRelinRescaleNamed(eval, ctDHalf, ctDHalf, fmt.Sprintf("Leading term: ctPowD = (x^(d/2))^2 = x^d; d=%d", d))
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
	ctLead, err := mulPlainRescaleNamed(eval, ctPowD, sparsePackLeadingOrPanic(leadCoeffs, params.MaxSlots()), "Leading term: ctLead = ctPowD * sparse leading-coefficient vector a_d")
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
		ctPowD, err = mulCtRelinRescaleNamed(eval, ctHalf, ctHalf, fmt.Sprintf("m=1 direct path: ctPowD = (x^(d/2))^2 = x^d; d=%d", pre.D))
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
	ctLead, err := mulOperandRescaleNamedWithPlain(eval, ctPowD, pre.LeadPT, pre.LeadVec, "Leading term: ctLead = ctPowD * precomputed leading-coefficient plaintext a_d")
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
		ctPowD, err = mulCtRelinRescaleNamed(eval, ctHalf, ctHalf, fmt.Sprintf("m=1 direct path: ctPowD = (x^(d/2))^2 = x^d; d=%d", d))
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
	ctLead, err := mulPlainRescaleNamed(eval, ctPowD, sparsePackLeadingOrPanic(leadCoeffs, params.MaxSlots()), "Leading term: ctLead = ctPowD * sparse leading-coefficient vector a_d")
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

// Homomorphic-operation diagnostic tracer for polynomial evaluation.
type MulTraceEntry struct {
	Index            int
	Name             string
	Kind             string
	In0Level         int
	In0QBits         int
	In1Level         int
	In1QBits         int
	OutLevel         int
	OutQBits         int
	Rescale          bool
	Duration         time.Duration
	ExpectedKnown    bool
	MaxCoeffNoiseAbs string
	NoiseBudgetBits  string
	RequiredBitsRaw  int
}

type MulTraceRecorder struct {
	Enabled    bool
	ProbeNoise bool // if true, decrypt/decode every logged output and fill noise columns; very expensive
	Params     bfv.Parameters
	Encoder    *bfv.Encoder
	Dec        *rlwe.Decryptor
	Mod        uint64
	Entries    []MulTraceEntry
	Expected   map[*rlwe.Ciphertext][]uint64
	ProbeTime  time.Duration // diagnostic time spent decrypting/probing after logged operations; not part of online HE time
}

var globalMulTracer *MulTraceRecorder
var globalMulTraceSummaryOnly bool

func newMulTraceRecorder(enabled bool, probeNoise bool, params bfv.Parameters, encoder *bfv.Encoder, dec *rlwe.Decryptor) *MulTraceRecorder {
	if !enabled {
		probeNoise = false
	}
	var expected map[*rlwe.Ciphertext][]uint64
	if probeNoise {
		expected = map[*rlwe.Ciphertext][]uint64{}
	}
	return &MulTraceRecorder{Enabled: enabled, ProbeNoise: probeNoise, Params: params, Encoder: encoder, Dec: dec, Mod: params.PlaintextModulus(), Expected: expected}
}

func qBitsOfLevel(params bfv.Parameters, level int) int {
	if level < 0 {
		return -1
	}
	if level > params.MaxLevel() {
		level = params.MaxLevel()
	}
	return params.RingQ().AtLevel(level).Modulus().BitLen()
}

func mulTraceName(helper, detail string) string {
	detail = strings.TrimSpace(detail)
	if detail == "" {
		return helper
	}
	return fmt.Sprintf("%s [%s]", detail, helper)
}

func mulTraceKindLabel(kind string) string {
	switch kind {
	case "ct-ct":
		return "ct×ct"
	case "ct-ct-lazy":
		return "ct×ct-lazy"
	case "ct-pt":
		return "ct×pt"
	case "ct-pt-LT":
		return "ct×pt-LT"
	case "ct-pt-StC":
		return "ct×pt-StC"
	case "ct-pt-Step1":
		return "ct×pt-Step1"
	case "ct-op":
		return "ct×op"
	case "rot-col":
		return "rot-col"
	case "rot-row":
		return "rot-row"
	case "add":
		return "add"
	case "checkpoint":
		return "checkpoint"
	default:
		return kind
	}
}

func formatCipherLevelQ(level, qbits int) string {
	if level < 0 {
		return "-"
	}
	return fmt.Sprintf("ct:L%d/%db", level, qbits)
}

func formatMulTraceInput1(e MulTraceEntry) string {
	if e.In1Level >= 0 {
		return formatCipherLevelQ(e.In1Level, e.In1QBits)
	}
	switch e.Kind {
	case "ct-pt", "ct-pt-LT", "ct-pt-StC", "ct-pt-Step1":
		return "pt:vector"
	case "ct-op":
		return "pt/op"
	default:
		return "-"
	}
}

func mulTraceActive() bool {
	tr := globalMulTracer
	return tr != nil && tr.Enabled
}

func mulTraceNoiseActive() bool {
	tr := globalMulTracer
	return tr != nil && tr.Enabled && tr.ProbeNoise
}

func polyClearExpected(ct *rlwe.Ciphertext) {
	if globalMulTracer == nil || !globalMulTracer.Enabled || !globalMulTracer.ProbeNoise || globalMulTracer.Expected == nil || ct == nil {
		return
	}
	delete(globalMulTracer.Expected, ct)
}

func polyRegisterExpected(ct *rlwe.Ciphertext, expected []uint64) {
	if globalMulTracer == nil || !globalMulTracer.Enabled || !globalMulTracer.ProbeNoise || globalMulTracer.Expected == nil || ct == nil {
		return
	}
	if expected == nil {
		polyClearExpected(ct)
		return
	}
	globalMulTracer.Expected[ct] = append([]uint64(nil), expected...)
}

func polyExpected(ct *rlwe.Ciphertext) ([]uint64, bool) {
	if globalMulTracer == nil || !globalMulTracer.Enabled || !globalMulTracer.ProbeNoise || globalMulTracer.Expected == nil || ct == nil {
		return nil, false
	}
	v, ok := globalMulTracer.Expected[ct]
	return v, ok
}

func polyExpectedClone(ct *rlwe.Ciphertext) []uint64 {
	if ev, ok := polyExpected(ct); ok && ev != nil {
		return append([]uint64(nil), ev...)
	}
	return nil
}

func polyRegisterExpectedAddSaved(dst *rlwe.Ciphertext, saved []uint64, rhs *rlwe.Ciphertext) {
	if dst == nil {
		return
	}
	if saved == nil || globalMulTracer == nil {
		polyClearExpected(dst)
		return
	}
	bv, okB := polyExpected(rhs)
	if !okB || len(saved) != len(bv) {
		polyClearExpected(dst)
		return
	}
	out := make([]uint64, len(saved))
	mod := globalMulTracer.Mod
	for i := range saved {
		out[i] = (saved[i] + bv[i]) % mod
	}
	polyRegisterExpected(dst, out)
}

func polyCopyExpected(src, dst *rlwe.Ciphertext) {
	if dst == nil {
		return
	}
	if ev, ok := polyExpected(src); ok {
		polyRegisterExpected(dst, ev)
		return
	}
	polyClearExpected(dst)
}

func polyRegisterExpectedAddPlain(dst, src *rlwe.Ciphertext, plain []uint64) {
	if dst == nil {
		return
	}
	if plain == nil {
		polyClearExpected(dst)
		return
	}
	if ev, ok := polyExpected(src); ok && len(ev) == len(plain) {
		out := make([]uint64, len(ev))
		mod := globalMulTracer.Mod
		for i := range ev {
			out[i] = (ev[i] + plain[i]) % mod
		}
		polyRegisterExpected(dst, out)
		return
	}
	polyClearExpected(dst)
}

func polyRegisterExpectedAdd(dst, a, b *rlwe.Ciphertext) {
	if dst == nil {
		return
	}
	av, okA := polyExpected(a)
	bv, okB := polyExpected(b)
	if okA && okB && len(av) == len(bv) {
		out := make([]uint64, len(av))
		mod := globalMulTracer.Mod
		for i := range av {
			out[i] = (av[i] + bv[i]) % mod
		}
		polyRegisterExpected(dst, out)
		return
	}
	polyClearExpected(dst)
}

func polyRotateSlotsForColumn(vec []uint64, shift int) []uint64 {
	// This matches the plaintext convention used by rotateWithinHalves in the LT code.
	return rotateWithinHalves(vec, shift)
}

func polyRowSwapSlots(vec []uint64) []uint64 {
	out := make([]uint64, len(vec))
	half := len(vec) / 2
	copy(out[:half], vec[half:])
	copy(out[half:], vec[:half])
	return out
}

func polyRegisterExpectedRotateColumns(dst, src *rlwe.Ciphertext, shift int) {
	if ev, ok := polyExpected(src); ok {
		polyRegisterExpected(dst, polyRotateSlotsForColumn(ev, shift))
		return
	}
	polyClearExpected(dst)
}

func polyRegisterExpectedRowSwap(dst, src *rlwe.Ciphertext) {
	if ev, ok := polyExpected(src); ok {
		polyRegisterExpected(dst, polyRowSwapSlots(ev))
		return
	}
	polyClearExpected(dst)
}

func mulSlotsMod(a, b []uint64, mod uint64) []uint64 {
	if len(a) != len(b) {
		return nil
	}
	out := make([]uint64, len(a))
	for i := range a {
		out[i] = mulMod(a[i], b[i], mod)
	}
	return out
}

func constSlotsFromSparseMask(mask []uint64, n int) []uint64 {
	if len(mask) == n {
		return append([]uint64(nil), mask...)
	}
	return nil
}

func logOpTrace(name, kind string, in0, in1, out *rlwe.Ciphertext, rescale bool, dur time.Duration, expectedOut []uint64) {
	tr := globalMulTracer
	if tr == nil || !tr.Enabled {
		return
	}
	entry := MulTraceEntry{
		Index:            len(tr.Entries) + 1,
		Name:             name,
		Kind:             kind,
		In0Level:         -1,
		In0QBits:         -1,
		In1Level:         -1,
		In1QBits:         -1,
		OutLevel:         -1,
		OutQBits:         -1,
		Rescale:          rescale,
		Duration:         dur,
		ExpectedKnown:    expectedOut != nil && tr.ProbeNoise,
		MaxCoeffNoiseAbs: "off",
		NoiseBudgetBits:  "off",
	}
	if in0 != nil {
		entry.In0Level = in0.Level()
		entry.In0QBits = qBitsOfLevel(tr.Params, in0.Level())
	}
	if in1 != nil {
		entry.In1Level = in1.Level()
		entry.In1QBits = qBitsOfLevel(tr.Params, in1.Level())
	}
	if out != nil {
		entry.OutLevel = out.Level()
		entry.OutQBits = qBitsOfLevel(tr.Params, out.Level())
		if tr.ProbeNoise && expectedOut != nil {
			polyRegisterExpected(out, expectedOut)
		}
	}
	if tr.ProbeNoise && out != nil && expectedOut != nil {
		probeStart := time.Now()
		probe, err := probeCipherNoiseAgainstSlots(tr.Params, tr.Encoder, tr.Dec, out, expectedOut, 0, name)
		tr.ProbeTime += time.Since(probeStart)
		if err == nil && probe != nil {
			entry.MaxCoeffNoiseAbs = probe.MaxCoeffNoiseAbs
			entry.RequiredBitsRaw = probe.RequiredBitsNoMargin
			entry.NoiseBudgetBits = fmt.Sprintf("%d", probe.CurrentLogQBits-probe.RequiredBitsNoMargin)
		} else if err != nil {
			entry.MaxCoeffNoiseAbs = "probe-error: " + err.Error()
			entry.NoiseBudgetBits = "n/a"
		}
	} else if tr.ProbeNoise {
		entry.MaxCoeffNoiseAbs = "n/a"
		entry.NoiseBudgetBits = "n/a"
	}
	tr.Entries = append(tr.Entries, entry)
}

func logMulTrace(name, kind string, in0, in1, out *rlwe.Ciphertext, rescale bool, dur time.Duration, expectedOut []uint64) {
	if out == nil {
		return
	}
	logOpTrace(name, kind, in0, in1, out, rescale, dur, expectedOut)
}

func probeCipherBrief(label string, ct *rlwe.Ciphertext) (budget string, maxNoise string) {
	tr := globalMulTracer
	if tr == nil || !tr.Enabled || !tr.ProbeNoise || ct == nil {
		return "off", "off"
	}
	expected, ok := polyExpected(ct)
	if !ok || expected == nil {
		return "unknown", "unknown"
	}
	probeStart := time.Now()
	probe, err := probeCipherNoiseAgainstSlots(tr.Params, tr.Encoder, tr.Dec, ct, expected, 0, label)
	tr.ProbeTime += time.Since(probeStart)
	if err != nil || probe == nil {
		if err != nil {
			return "probe-error", err.Error()
		}
		return "probe-error", "nil probe"
	}
	return fmt.Sprintf("%d", probe.CurrentLogQBits-probe.RequiredBitsNoMargin), probe.MaxCoeffNoiseAbs
}

func logInputPairCheckpoint(name, label0 string, ct0 *rlwe.Ciphertext, label1 string, ct1 *rlwe.Ciphertext) {
	tr := globalMulTracer
	if tr == nil || !tr.Enabled || !tr.ProbeNoise {
		return
	}
	b0, n0 := probeCipherBrief(name+"/"+label0, ct0)
	b1, n1 := probeCipherBrief(name+"/"+label1, ct1)
	entry := MulTraceEntry{
		Index:            len(tr.Entries) + 1,
		Name:             name,
		Kind:             "checkpoint",
		In0Level:         -1,
		In0QBits:         -1,
		In1Level:         -1,
		In1QBits:         -1,
		OutLevel:         -1,
		OutQBits:         -1,
		Rescale:          false,
		Duration:         0,
		ExpectedKnown:    true,
		NoiseBudgetBits:  fmt.Sprintf("%s:%s; %s:%s", label0, b0, label1, b1),
		MaxCoeffNoiseAbs: fmt.Sprintf("%s:%s; %s:%s", label0, n0, label1, n1),
	}
	if ct0 != nil {
		entry.In0Level = ct0.Level()
		entry.In0QBits = qBitsOfLevel(tr.Params, ct0.Level())
	}
	if ct1 != nil {
		entry.In1Level = ct1.Level()
		entry.In1QBits = qBitsOfLevel(tr.Params, ct1.Level())
	}
	tr.Entries = append(tr.Entries, entry)
}

func expectedForCtCtMul(out *rlwe.Ciphertext, a, b *rlwe.Ciphertext) []uint64 {
	av, okA := polyExpected(a)
	bv, okB := polyExpected(b)
	if okA && okB {
		return mulSlotsMod(av, bv, globalMulTracer.Mod)
	}
	return nil
}

func expectedForCtPlainMul(ct *rlwe.Ciphertext, plain []uint64) []uint64 {
	av, okA := polyExpected(ct)
	if !okA || plain == nil {
		return nil
	}
	if len(plain) != len(av) {
		return nil
	}
	return mulSlotsMod(av, plain, globalMulTracer.Mod)
}

func expectedForAdd(a, b *rlwe.Ciphertext) []uint64 {
	av, okA := polyExpected(a)
	bv, okB := polyExpected(b)
	if !okA || !okB || len(av) != len(bv) || globalMulTracer == nil {
		return nil
	}
	out := make([]uint64, len(av))
	mod := globalMulTracer.Mod
	for i := range av {
		out[i] = (av[i] + bv[i]) % mod
	}
	return out
}

func expectedForRotateColumns(ct *rlwe.Ciphertext, shift int) []uint64 {
	ev, ok := polyExpected(ct)
	if !ok {
		return nil
	}
	return polyRotateSlotsForColumn(ev, shift)
}

func expectedForRowSwap(ct *rlwe.Ciphertext) []uint64 {
	ev, ok := polyExpected(ct)
	if !ok {
		return nil
	}
	return polyRowSwapSlots(ev)
}

func printMulTraceSummary() {
	tr := globalMulTracer
	if tr == nil || !tr.Enabled {
		return
	}
	fmt.Println("========== Homomorphic operation-level trace ==========")
	fmt.Printf("operations logged      : %d\n", len(tr.Entries))
	fmt.Println("legend: ct:Lk/Qbits is a ciphertext at modulus-chain level k; pt:vector/pt-op is a plaintext operand, not a ciphertext level.")
	if tr.ProbeNoise {
		fmt.Println("noise columns are filled by diagnostic decrypt/decode probes; checkpoint rows do not perform HE work.")
	} else {
		fmt.Println("noise columns are disabled for speed; use -mul-trace-noise to recover noiseBudget/max|noise| at every row.")
	}
	if !globalMulTraceSummaryOnly {
		fmt.Println("# | op | rescale | in0 | in1 | out | noiseBudget | max|noise| | time | algorithm step")
	} else {
		fmt.Println("row printing             : disabled by -mul-trace-summary-only")
	}
	var total time.Duration
	byKind := map[string]time.Duration{}
	byKindCount := map[string]int{}
	for _, e := range tr.Entries {
		total += e.Duration
		byKind[e.Kind] += e.Duration
		byKindCount[e.Kind]++
		if !globalMulTraceSummaryOnly {
			fmt.Printf("%03d | %-10s | %-5v | %-11s | %-10s | %-11s | %-11s | %-14s | %-10v | %s\n",
				e.Index, mulTraceKindLabel(e.Kind), e.Rescale,
				formatCipherLevelQ(e.In0Level, e.In0QBits), formatMulTraceInput1(e), formatCipherLevelQ(e.OutLevel, e.OutQBits),
				e.NoiseBudgetBits, e.MaxCoeffNoiseAbs, e.Duration.Round(time.Microsecond), e.Name)
		}
	}
	fmt.Printf("operation time sum      : %v (sum of the table time column only; checkpoint rows have zero HE time)\n", total.Round(time.Microsecond))
	for _, kind := range []string{"ct-ct", "ct-ct-lazy", "ct-pt", "ct-pt-LT", "ct-pt-StC", "ct-pt-Step1", "ct-op", "rot-col", "rot-row", "add", "final-rescale", "checkpoint"} {
		if byKindCount[kind] > 0 {
			fmt.Printf("  - %-10s : %v over %d entries\n", mulTraceKindLabel(kind), byKind[kind].Round(time.Microsecond), byKindCount[kind])
		}
	}
	if tr.ProbeNoise || tr.ProbeTime > 0 {
		fmt.Printf("operation probe time    : %v (diagnostic decrypt/decode time, not included above)\n", tr.ProbeTime.Round(time.Microsecond))
	}
	fmt.Println("================================================")
}

func mulTraceKindCounts() map[string]int {
	out := map[string]int{}
	if globalMulTracer == nil {
		return out
	}
	for _, e := range globalMulTracer.Entries {
		out[e.Kind]++
	}
	return out
}

func mulTraceProbeTime() time.Duration {
	if globalMulTracer == nil {
		return 0
	}
	return globalMulTracer.ProbeTime
}

func polyNoiseProbeTime() time.Duration {
	if globalPolyNoiseTracer == nil || !globalPolyNoiseTracer.Enabled {
		return 0
	}
	return globalPolyNoiseTracer.ProbeTime
}

func stageBreakdownTotal(tm BenchPolyEvalTiming) time.Duration {
	return tm.Breakdown.BuildBasis +
		tm.Breakdown.SquareXRHalf +
		tm.Breakdown.BuildGrouped +
		tm.Breakdown.ParallelLT +
		tm.Breakdown.PointwiseMul +
		tm.Breakdown.RotateAndSum +
		tm.Breakdown.ComputeXD +
		tm.Breakdown.LeadingTerm +
		tm.Breakdown.FinalAdd +
		tm.Breakdown.FinalRescale
}
func parseBitListExpanded(spec string) ([]int, error) {
	spec = strings.TrimSpace(strings.NewReplacer("，", ",", "；", ";").Replace(spec))
	if spec == "" {
		return nil, errors.New("empty bit-size list")
	}
	fields := strings.Split(spec, ",")
	out := make([]int, 0, len(fields))
	for _, raw := range fields {
		part := strings.TrimSpace(raw)
		if part == "" {
			return nil, fmt.Errorf("empty bit-size entry in %q", spec)
		}
		rep := 1
		valuePart := part
		if pos := strings.IndexAny(part, "xX*"); pos >= 0 {
			valuePart = strings.TrimSpace(part[:pos])
			repPart := strings.TrimSpace(part[pos+1:])
			if valuePart == "" || repPart == "" {
				return nil, fmt.Errorf("invalid repeated bit-size %q", part)
			}
			if _, err := fmt.Sscan(repPart, &rep); err != nil || rep <= 0 {
				return nil, fmt.Errorf("invalid repeat count in %q", part)
			}
		}
		var v int
		if _, err := fmt.Sscan(valuePart, &v); err != nil || v <= 0 {
			return nil, fmt.Errorf("invalid bit-size in %q", part)
		}
		for i := 0; i < rep; i++ {
			out = append(out, v)
		}
	}
	return out, nil
}

func buildRandomPolynomialCoeffs(degree int, mod uint64, seed int64) []uint64 {
	rng := rand.New(rand.NewSource(seed))
	out := make([]uint64, degree+1)
	for i := range out {
		out[i] = uint64(rng.Int63n(int64(mod)))
	}
	return out
}

func splitPolynomialForAlg5(full []uint64, degree int, m int) (lower [][]uint64, lead []uint64, lowerLen int, splitTop bool, err error) {
	if degree < 0 {
		return nil, nil, 0, false, fmt.Errorf("degree must be non-negative")
	}
	if len(full) < degree+1 {
		return nil, nil, 0, false, fmt.Errorf("coeff list length %d < degree+1=%d", len(full), degree+1)
	}
	if isPow2(degree + 1) {
		lowerLen = degree + 1
		splitTop = false
	} else if degree > 0 && isPow2(degree) {
		lowerLen = degree
		splitTop = true
	} else {
		return nil, nil, 0, false, fmt.Errorf("need degree+1 or degree to be a power of two; got degree=%d", degree)
	}
	baseLower := append([]uint64(nil), full[:lowerLen]...)
	lower = replicateSinglePolynomial(baseLower, m)
	lead = make([]uint64, m)
	if splitTop {
		for i := range lead {
			lead[i] = full[degree]
		}
	}
	return lower, lead, lowerLen, splitTop, nil
}

func decodeSlots(params bfv.Parameters, encoder *bfv.Encoder, dec *rlwe.Decryptor, ct *rlwe.Ciphertext) ([]uint64, error) {
	pt := dec.DecryptNew(ct)
	out := make([]uint64, params.MaxSlots())
	if err := encoder.Decode(pt, out); err != nil {
		return nil, err
	}
	return out, nil
}

func printBenchPolyTiming(tm BenchPolyEvalTiming) {
	fmt.Printf("poly algorithm              : %s\n", tm.Algorithm)
	stageTotal := stageBreakdownTotal(tm)
	diagTotal := mulTraceProbeTime() + polyNoiseProbeTime()
	unaccounted := tm.Total - stageTotal
	if unaccounted < 0 {
		unaccounted = 0
	}
	fmt.Printf("poly homomorphic subtotal   : %v (sum of listed HE stages; use this for online benchmark)\n", stageTotal)
	fmt.Printf("poly wall/evaluator total   : %v (includes evaluator time plus final rescale time; diagnostics may add wall overhead)\n", tm.Total)
	fmt.Printf("poly unaccounted overhead   : %v (wall - stage subtotal; mostly trace/expected construction)\n", unaccounted)
	fmt.Printf("diagnostic probe overhead   : %v (mul-trace probes %v + checkpoint probes %v; subset of overhead)\n", diagTotal, mulTraceProbeTime(), polyNoiseProbeTime())
	fmt.Printf("  - build basis / P         : %v\n", tm.Breakdown.BuildBasis)
	fmt.Printf("  - square x^(r/2)          : %v\n", tm.Breakdown.SquareXRHalf)
	fmt.Printf("  - build grouped powers    : %v\n", tm.Breakdown.BuildGrouped)
	fmt.Printf("  - ParallelLT total        : %v\n", tm.Breakdown.ParallelLT)
	fmt.Printf("    · LT matrix build       : %v\n", tm.Breakdown.LTMatrixBuild)
	fmt.Printf("    · LT decompose          : %v\n", tm.Breakdown.LTDecompose)
	fmt.Printf("    · LT baby rotations     : %v\n", tm.Breakdown.LTBabyRotations)
	fmt.Printf("    · LT giant rotations    : %v\n", tm.Breakdown.LTGiantRotations)
	fmt.Printf("    · LT pt-ct multiplies   : %v\n", tm.Breakdown.LTPlaintextCipherMul)
	fmt.Printf("    · LT first-stage other  : %v\n", tm.Breakdown.LTFirstStageOther)
	fmt.Printf("    · LT second stage       : %v\n", tm.Breakdown.LTSecondStage)
	fmt.Printf("    · LT post-process       : %v\n", tm.Breakdown.LTPostProcess)
	fmt.Printf("    · LT post-rescale       : %v\n", tm.Breakdown.LTPostRescale)
	fmt.Printf("    · LT residual           : %v\n", tm.Breakdown.LTResidual)
	fmt.Printf("  - pointwise multiply      : %v\n", tm.Breakdown.PointwiseMul)
	fmt.Printf("  - rotate-and-sum          : %v\n", tm.Breakdown.RotateAndSum)
	fmt.Printf("  - compute x^d             : %v\n", tm.Breakdown.ComputeXD)
	fmt.Printf("  - leading term            : %v\n", tm.Breakdown.LeadingTerm)
	fmt.Printf("  - final add               : %v\n", tm.Breakdown.FinalAdd)
	fmt.Printf("  - final rescale/modswitch : %v\n", tm.Breakdown.FinalRescale)
}

func secondsOf(d time.Duration) float64 {
	return float64(d) / float64(time.Second)
}

func formatSeconds3(d time.Duration) string {
	return fmt.Sprintf("%.3f", secondsOf(d))
}

func formatGiB(bytes int64) string {
	if bytes <= 0 {
		return "0.00"
	}
	return fmt.Sprintf("%.2f", float64(bytes)/(1024.0*1024.0*1024.0))
}

func sumIntSlice(xs []int) int {
	s := 0
	for _, x := range xs {
		s += x
	}
	return s
}

func formatBitBudget(xs []int) string {
	if len(xs) == 0 {
		return "0"
	}
	parts := make([]string, 0)
	for i := 0; i < len(xs); {
		j := i + 1
		for j < len(xs) && xs[j] == xs[i] {
			j++
		}
		if j-i == 1 {
			parts = append(parts, fmt.Sprintf("%d", xs[i]))
		} else {
			parts = append(parts, fmt.Sprintf("%d×%d", xs[i], j-i))
		}
		i = j
	}
	return strings.Join(parts, ", ")
}

func formatDegreeForSummary(d int) string {
	if d > 0 && isPow2(d) {
		return fmt.Sprintf("2^%d", bits.Len(uint(d))-1)
	}
	if d >= 0 && isPow2(d+1) {
		return fmt.Sprintf("2^%d-1", bits.Len(uint(d+1))-1)
	}
	return fmt.Sprintf("%d", d)
}

func formatPowerOfTwoModulus(p uint64) string {
	if p > 0 && (p&(p-1)) == 0 {
		return fmt.Sprintf("2^%d", bits.Len64(p)-1)
	}
	return fmt.Sprintf("%d", p)
}

func failBoundLog2(B float64, denom float64) float64 {
	if B <= 0 || denom <= 0 {
		return math.Inf(1)
	}
	return 1.0 - (6.0*B*B)/(denom*math.Ln2)
}

func formatLog2FailBound(log2p float64) string {
	if math.IsInf(log2p, -1) {
		return "0"
	}
	if math.IsInf(log2p, 1) || math.IsNaN(log2p) {
		return "n/a"
	}
	if log2p <= 0 {
		return fmt.Sprintf("≤ 2^%.2f", log2p)
	}
	return fmt.Sprintf("≤ %.3g", math.Pow(2, log2p))
}

func displayWidth(s string) int {
	return len([]rune(s))
}

func padDisplayCell(s string, width int, rightAlign bool) string {
	pad := width - displayWidth(s)
	if pad <= 0 {
		return s
	}
	if rightAlign {
		return strings.Repeat(" ", pad) + s
	}
	return s + strings.Repeat(" ", pad)
}

func printAlignedPipeTable(headers []string, rows [][]string, rightAlign []bool) {
	cols := len(headers)
	widths := make([]int, cols)
	for i, h := range headers {
		widths[i] = displayWidth(h)
	}
	for _, row := range rows {
		for i := 0; i < cols && i < len(row); i++ {
			if w := displayWidth(row[i]); w > widths[i] {
				widths[i] = w
			}
		}
	}
	isRight := func(i int) bool {
		return i < len(rightAlign) && rightAlign[i]
	}
	printRow := func(row []string) {
		for i := 0; i < cols; i++ {
			if i > 0 {
				fmt.Print(" | ")
			}
			cell := ""
			if i < len(row) {
				cell = row[i]
			}
			fmt.Print(padDisplayCell(cell, widths[i], isRight(i)))
		}
		fmt.Println()
	}
	printRow(headers)
	for i := 0; i < cols; i++ {
		if i > 0 {
			fmt.Print("-+-")
		}
		fmt.Print(strings.Repeat("-", widths[i]))
	}
	fmt.Println()
	for _, row := range rows {
		printRow(row)
	}
}

func splitLogQForPaperSummary(logQBits []int, packingLevels, bufferLevels int, hasStC bool) (packing, polyEval, stc, buffer, base string) {
	n := len(logQBits)
	if n == 0 {
		return "0", "0", "0", "0", "0"
	}
	if packingLevels < 0 {
		packingLevels = 0
	}
	if bufferLevels < 0 {
		bufferLevels = 0
	}
	if packingLevels > n {
		packingLevels = n
	}
	end := n - packingLevels
	if end < 1 {
		end = 1
	}
	base = formatBitBudget(logQBits[:1])
	idx := 1
	if bufferLevels > 0 && idx < end {
		to := idx + bufferLevels
		if to > end {
			to = end
		}
		buffer = formatBitBudget(logQBits[idx:to])
		idx = to
	} else {
		buffer = "0"
	}
	if hasStC && idx < end {
		stc = formatBitBudget(logQBits[idx : idx+1])
		idx++
	} else {
		stc = "0"
	}
	if idx < end {
		polyEval = formatBitBudget(logQBits[idx:end])
	} else {
		polyEval = "0"
	}
	if packingLevels > 0 && end < n {
		packing = formatBitBudget(logQBits[end:])
	} else {
		packing = "0"
	}
	return packing, polyEval, stc, buffer, base
}

func formatSigmaForSummary(sigma float64, count int) string {
	if count < 2 {
		return "n/a"
	}
	return fmt.Sprintf("%.4f", sigma)
}

func printPaperStyleFBSummary(
	N, m, degree, lweN int,
	T, p uint64,
	logQBits, logPBits []int,
	packingLevels, bufferLevels int,
	hasStC bool,
	params bfv.Parameters,
	bootstrapKeyBytes int64,
	step1, step2EvalPower, step2BatchLT, step2Total, step3, onlineSubtotal, onlineWall time.Duration,
	sigmaEmp float64,
	noiseCount int,
	secretInfo TailSecretInfo,
) {
	packing, polyEval, stc, buffer, base := splitLogQForPaperSummary(logQBits, packingLevels, bufferLevels, hasStC)
	paramBits := 0
	if p > 0 {
		paramBits = bits.Len64(p - 1)
	}
	logPQ := qBitsOfLevel(params, params.MaxLevel()) + sumIntSlice(logPBits)
	B := float64(T / (2 * p))
	paperLog2 := failBoundLog2(B, float64(lweN+1))
	summaryLog2 := paperLog2
	if secretInfo.H > 0 {
		summaryLog2 = failBoundLog2(B, float64(secretInfo.H+1))
	}

	fmt.Println()
	fmt.Println("========== Paper-style functional bootstrapping summary ==========")
	fmt.Println("Parameter summary:")
	printAlignedPipeTable(
		[]string{"Parameter set", "N", "log(PQ)", "d", "q", "p", "logQ Packing", "logQ PolyEval", "logQ StC", "logQ Buffer", "logQ Base", "logP"},
		[][]string{{
			fmt.Sprintf("%d-bit (m=%d)", paramBits, m),
			fmt.Sprintf("%d", N),
			fmt.Sprintf("%d", logPQ),
			formatDegreeForSummary(degree),
			fmt.Sprintf("%d", T),
			formatPowerOfTwoModulus(p),
			packing,
			polyEval,
			stc,
			buffer,
			base,
			formatBitBudget(logPBits),
		}},
		[]bool{false, true, true, true, true, true, true, true, true, true, true, true},
	)

	fmt.Println()
	fmt.Println("Runtime/noise summary:")
	printAlignedPipeTable(
		[]string{"m", "p", "Bootstrap key (GiB, est.)", "Step 1", "Step 2 EvalPower", "Step 2 BatchLT", "Step 2 Total", "Step 3", "Online subtotal", "Online wall", "Noise σ_res", "Per-LWE fail. prob."},
		[][]string{{
			fmt.Sprintf("%d", m),
			fmt.Sprintf("%d", p),
			formatGiB(bootstrapKeyBytes),
			formatSeconds3(step1),
			formatSeconds3(step2EvalPower),
			formatSeconds3(step2BatchLT),
			formatSeconds3(step2Total),
			formatSeconds3(step3),
			formatSeconds3(onlineSubtotal),
			formatSeconds3(onlineWall),
			formatSigmaForSummary(sigmaEmp, noiseCount),
			formatLog2FailBound(summaryLog2),
		}},
		[]bool{true, true, true, true, true, true, true, true, true, true, true, false},
	)
}

func printFailureProbabilitySummary(T, p uint64, lweN int, secretInfo TailSecretInfo, sigmaEmp float64, observed TailNoiseStats) {
	if p == 0 || lweN <= 0 {
		return
	}
	B := float64(T / (2 * p))
	paperLog2 := failBoundLog2(B, float64(lweN+1))
	secretNormSq := secretInfo.H
	if secretNormSq <= 0 {
		secretNormSq = lweN
	}
	secretAwareLog2 := failBoundLog2(B, float64(secretNormSq+1))
	fmt.Println()
	fmt.Println("Failure-probability summary:")
	fmt.Printf("decoding radius B          : floor(T/(2p)) = %.0f\n", B)
	if observed.Count < 2 {
		fmt.Printf("empirical sigma_res        : n/a  (only %d output LWE noise sample; centered std. dev. is not meaningful; RMS=%.4f)\n", observed.Count, observed.RMS)
	} else {
		fmt.Printf("empirical sigma_res        : %.4f  (centered std. dev. over this invocation's %d output LWE noises; RMS=%.4f)\n", sigmaEmp, observed.Count, observed.RMS)
	}
	fmt.Printf("observed over-radius       : %d/%d, max|e|=%d\n", observed.OverBound, observed.Count, observed.MaxAbs)
	if observed.OverBound > 0 {
		fmt.Printf("observed failure warning   : empirical/theoretical sigma summaries are not a correctness certificate here; the observed phase error already exceeds the decoding radius.\n")
	}
	fmt.Printf("paper-style analytic bound : %s  using denominator n+1=%d\n", formatLog2FailBound(paperLog2), lweN+1)
	if secretInfo.H > 0 {
		fmt.Printf("secret-aware sparse bound  : %s  using ||s||_2^2+1=h+1=%d\n", formatLog2FailBound(secretAwareLog2), secretInfo.H+1)
	}
}

type RunPolynomialBuildResult struct {
	FullCoeffs  []uint64
	CoeffsLower [][]uint64
	LeadCoeffs  []uint64
	LowerLen    int
	SplitTop    bool
	CoeffDesc   string
	FuncTable   []uint64
	FuncDesc    string
	Timing      BenchDynamicSetupTiming
}

func buildRunPolynomialCoeffs(T, p uint64, degree, m int, coeffMode, funcSpec, funcTableInline, funcFile string, coeffSeed, funcSeed int64, schemeD bool, schemeDScaleS uint64) (RunPolynomialBuildResult, error) {
	var out RunPolynomialBuildResult
	mode := strings.ToLower(strings.TrimSpace(coeffMode))
	var full []uint64
	var desc string
	var err error
	switch mode {
	case "lut":
		stFunc := time.Now()
		funcTable, funcDesc, err := buildFunctionTableWithSeed(p, funcSpec, funcTableInline, funcFile, funcSeed)
		out.Timing.FunctionTable = time.Since(stFunc)
		if err != nil {
			return out, err
		}
		out.FuncTable = append([]uint64(nil), funcTable...)
		out.FuncDesc = funcDesc
		if degree < int(T)-1 {
			return out, fmt.Errorf("degree=%d is smaller than the full-field LUT degree %d; use degree >= T-1 and pad with zero high coefficients", degree, T-1)
		}
		stLUT := time.Now()
		scale := uint64(1)
		if schemeD {
			scale = schemeDScaleS
		}
		full, err = buildStrictFunctionalLUTPolynomialCoefficients(T, p, funcTable, 1, scale)
		out.Timing.LUTBuild = time.Since(stLUT)
		if err != nil {
			return out, err
		}
		full = padPolynomialCoefficientsToDegree(full, degree)
		if schemeD {
			desc = fmt.Sprintf("Scheme-D strict LUT polynomial for %s; Scheme-D output-scaled LUT F(Delta*m+e)=S*f_phase(m), f_phase=Delta*f_msg, S=%d", funcDesc, schemeDScaleS)
		} else {
			desc = "strict interval LUT polynomial for " + funcDesc
		}
	case "random":
		st := time.Now()
		full = buildRandomPolynomialCoeffs(degree, T, coeffSeed)
		out.Timing.LUTBuild = time.Since(st)
		if schemeD {
			full = scalarMulVectorMod(full, schemeDScaleS, T)
			desc = fmt.Sprintf("random degree-%d polynomial; Scheme-D output-scaled polynomial F(x)=S*P(x), S=%d", degree, schemeDScaleS)
		} else {
			desc = fmt.Sprintf("random degree-%d polynomial", degree)
		}
	default:
		return out, fmt.Errorf("unknown -coeff-mode=%q; use random or lut", coeffMode)
	}
	if degree >= len(full) {
		full = padPolynomialCoefficientsToDegree(full, degree)
	}
	coeffsLower, leadCoeffs, lowerLen, splitTop, err := splitPolynomialForAlg5(full, degree, m)
	if err != nil {
		return out, err
	}
	out.FullCoeffs = full
	out.CoeffsLower = coeffsLower
	out.LeadCoeffs = leadCoeffs
	out.LowerLen = lowerLen
	out.SplitTop = splitTop
	out.CoeffDesc = desc
	return out, nil
}

func scaleRunPolynomialBuildResult(in RunPolynomialBuildResult, scalar, mod uint64, label string) RunPolynomialBuildResult {
	if scalar%mod == 1 || mod == 0 {
		return in
	}
	out := in
	out.FullCoeffs = scalarMulVectorMod(in.FullCoeffs, scalar, mod)
	out.CoeffsLower = scaleMatrixMod(in.CoeffsLower, scalar, mod)
	out.LeadCoeffs = scalarMulVectorMod(in.LeadCoeffs, scalar, mod)
	if label == "" {
		label = fmt.Sprintf("scaled by %d", scalar%mod)
	}
	out.CoeffDesc = in.CoeffDesc + "; " + label
	return out
}

func benchPolyEvalWithPlan(params bfv.Parameters, eval *bfv.Evaluator, ctIn *rlwe.Ciphertext, m, lowerLen, r int, coeffsLower [][]uint64, leadCoeffs []uint64, pre *PreprocessedPolyEval, largeAlg5Branch bool, dropBeforeLT bool, effectiveLTLevel int, effectiveLTPostLevel int, ltScaleAfterMul bool) (*rlwe.Ciphertext, BenchPolyEvalTiming, error) {
	if m == 1 && lowerLen <= r {
		if pre != nil {
			return benchPolyEvalSingleSlotDirectPrecomp(params, eval, ctIn, pre)
		}
		return benchPolyEvalSingleSlotDirect(params, eval, ctIn, m, coeffsLower, leadCoeffs)
	}
	if largeAlg5Branch {
		var preLT *PreprocessedParallelLT3
		if pre != nil {
			preLT = pre.LT
		}
		return benchPolyEvalSparsePow2Alg5LargeBranch(params, eval, ctIn, m, coeffsLower, leadCoeffs, preLT, dropBeforeLT, effectiveLTLevel, effectiveLTPostLevel, ltScaleAfterMul)
	}
	if pre != nil {
		return benchPolyEvalSparsePow2Alg5Precomp(params, eval, ctIn, pre, dropBeforeLT, effectiveLTLevel, effectiveLTPostLevel, ltScaleAfterMul)
	}
	return benchPolyEvalSparsePow2Alg5(params, eval, ctIn, m, coeffsLower, leadCoeffs, dropBeforeLT, effectiveLTLevel, effectiveLTPostLevel, ltScaleAfterMul)
}

func resetMulTraceForRun(params bfv.Parameters, encoder *bfv.Encoder, dec *rlwe.Decryptor, enabled bool, probeNoise bool) {
	globalMulTracer = newMulTraceRecorder(enabled, probeNoise, params, encoder, dec)
}

func appendTailNoiseDiffs(dst []int64, actual, target []uint64, mod uint64) []int64 {
	n := len(actual)
	if len(target) < n {
		n = len(target)
	}
	for i := 0; i < n; i++ {
		dst = append(dst, centeredDiff(actual[i], target[i], mod))
	}
	return dst
}

func maxAbsInt64Slice(v []int64) int64 {
	var m int64
	for _, x := range v {
		ax := abs64(x)
		if ax > m {
			m = ax
		}
	}
	return m
}

func meanAbsInt64(v []int64) float64 {
	if len(v) == 0 {
		return 0
	}
	var s float64
	for _, x := range v {
		s += float64(abs64(x))
	}
	return s / float64(len(v))
}

func rmsInt64(v []int64) float64 {
	if len(v) == 0 {
		return 0
	}
	var s float64
	for _, x := range v {
		f := float64(x)
		s += f * f
	}
	return math.Sqrt(s / float64(len(v)))
}

func formatQPrimeNoiseDiffSummary(label string, diffs []int64) string {
	if len(diffs) == 0 {
		return fmt.Sprintf("%s: n/a", label)
	}
	return fmt.Sprintf("%s: samples=%d, max|e|=%d, RMS=%.3f, mean|e|=%.3f, std=%.3f", label, len(diffs), maxAbsInt64Slice(diffs), rmsInt64(diffs), meanAbsInt64(diffs), stdDevInt64(diffs))
}

func projectedTNoiseFromQPrime(maxAbsQ int64, qPrime, t uint64) float64 {
	if maxAbsQ < 0 {
		maxAbsQ = -maxAbsQ
	}
	if qPrime == 0 {
		return 0
	}
	return float64(maxAbsQ) * float64(t) / float64(qPrime)
}

func minQPrimeForProjectedTNoise(maxAbsQ int64, t, radius uint64) *big.Int {
	if maxAbsQ < 0 {
		maxAbsQ = -maxAbsQ
	}
	if maxAbsQ == 0 || t == 0 || radius == 0 {
		return big.NewInt(0)
	}
	num := new(big.Int).SetInt64(maxAbsQ)
	num.Mul(num, new(big.Int).SetUint64(t))
	den := new(big.Int).SetUint64(radius)
	// ceil(num / den). This is a heuristic threshold for max_Q * T / Q' < radius.
	q := new(big.Int).Add(num, new(big.Int).Sub(den, big.NewInt(1)))
	q.Div(q, den)
	return q
}

func addPolyTiming(dst *BenchPolyEvalTiming, src BenchPolyEvalTiming) {
	dst.Total += src.Total
	dst.Breakdown.BuildBasis += src.Breakdown.BuildBasis
	dst.Breakdown.SquareXRHalf += src.Breakdown.SquareXRHalf
	dst.Breakdown.BuildGrouped += src.Breakdown.BuildGrouped
	dst.Breakdown.ParallelLT += src.Breakdown.ParallelLT
	dst.Breakdown.LTMatrixBuild += src.Breakdown.LTMatrixBuild
	dst.Breakdown.LTDecompose += src.Breakdown.LTDecompose
	dst.Breakdown.LTBabyRotations += src.Breakdown.LTBabyRotations
	dst.Breakdown.LTGiantRotations += src.Breakdown.LTGiantRotations
	dst.Breakdown.LTPlaintextCipherMul += src.Breakdown.LTPlaintextCipherMul
	dst.Breakdown.LTFirstStageOther += src.Breakdown.LTFirstStageOther
	dst.Breakdown.LTSecondStage += src.Breakdown.LTSecondStage
	dst.Breakdown.LTPostProcess += src.Breakdown.LTPostProcess
	dst.Breakdown.LTPostRescale += src.Breakdown.LTPostRescale
	dst.Breakdown.LTResidual += src.Breakdown.LTResidual
	dst.Breakdown.PointwiseMul += src.Breakdown.PointwiseMul
	dst.Breakdown.RotateAndSum += src.Breakdown.RotateAndSum
	dst.Breakdown.ComputeXD += src.Breakdown.ComputeXD
	dst.Breakdown.LeadingTerm += src.Breakdown.LeadingTerm
	dst.Breakdown.FinalAdd += src.Breakdown.FinalAdd
	dst.Breakdown.FinalRescale += src.Breakdown.FinalRescale
	dst.Breakdown.PowerGen += src.Breakdown.PowerGen
	dst.Breakdown.OuterCombine += src.Breakdown.OuterCombine
}

func main() {
	NFlag := flag.Int("N", 0, "required: BFV ring degree / slot count N")
	mFlag := flag.Int("m", 0, "required: number of logical sparse messages m")
	degreeFlag := flag.Int("degree", 0, "required: polynomial degree to evaluate; supports degree+1 pow2 or degree pow2 split-top")
	TFlag := flag.Uint64("T", 0, "required: BFV plaintext modulus")
	logQFlag := flag.String("logq", "", "required: LogQ bit-size list, supports forms like 40x3,47x16")
	logPFlag := flag.String("logp", "", "required: LogP bit-size list")
	inputFlag := flag.String("x", "", "comma-separated raw input values in Z_T of length m; used when -input-mode=raw, or as explicit phase values when -input-mode=phase-raw")
	inputSeedFlag := flag.Int64("input-seed", 12345, "base seed for random raw inputs or random messages; run i uses base+i")
	inputModeFlag := flag.String("input-mode", "phase", "input mode: phase directly encrypts RLWE slots x=Delta*m+e; lwe first generates LWE ciphertexts and homomorphically converts them to sparse RLWE slots by paper Step 1; Scheme-D does not scale the input, only the LUT output")
	lweToRLWEFlag := flag.Bool("lwe-to-rlwe", true, "alias for -input-mode=lwe: generate LWE ciphertexts and homomorphically decrypt/pack them into sparse RLWE slots before polynomial evaluation")
	lweStep1RescaleLevelsFlag := flag.Int("lwe-step1-rescale-levels", 1, "when -lwe-to-rlwe is enabled, immediately rescale/drop this many top Q levels after Step 1 before polynomial evaluation")
	messageFlag := flag.String("message", "", "comma-separated messages m_i in Z_p for -input-mode=phase; default deterministic random; explicit messages are reused across runs")
	phaseErrorFlag := flag.String("phase-error", "", "comma-separated signed input phase errors e_i for -input-mode=phase; explicit errors are reused across runs")
	phaseErrorSigmaFlag := flag.Float64("phase-error-sigma", 3.2, "stddev for rounded Gaussian input phase error e_i in x=Delta*m_i+e_i; 0 gives noise-free phase")
	phaseErrorSeedFlag := flag.Int64("phase-error-seed", 20260614, "base seed for random input phase errors; run i uses base+i")
	phaseErrorBoundFlag := flag.Int64("phase-error-bound", -1, "exclusive bound |e_i| < bound for random phase errors; -1 uses Delta/2")
	coeffModeFlag := flag.String("coeff-mode", "lut", "polynomial coefficients: random or lut")
	coeffSeedFlag := flag.Int64("coeff-seed", 20260613, "base seed for random polynomial coefficients; run i uses base+i when coeff-mode=random")
	pFlag := flag.Uint64("p", 0, "required: message modulus p for coeff-mode=lut")
	funcSpecFlag := flag.String("func", "", "required: function for coeff-mode=lut: random|identity|square|cube|neg|affine:a,b|table")
	funcTableFlag := flag.String("func-table", "", "inline function table for coeff-mode=lut; reused across runs")
	funcFileFlag := flag.String("func-file", "", "function table file; reused across runs")
	funcSeedFlag := flag.Int64("func-seed", 20260402, "base random function seed; run i uses base+i when the function is random")
	precomputeFlag := flag.Bool("poly-precompute-pt", true, "precompute polynomial plaintexts for Algorithm 5; plaintexts are encoded at the operation level, and the large branch precomputes only BatchLT masks")
	dropBeforeLTFlag := flag.Bool("drop-before-lt", true, "drop ct1/ctP before ParallelLT; default policy drops to ct2.Level()")
	ltLevelFlag := flag.Int("lt-level", -2, "level at which ParallelLT/BatchLT is evaluated; default -2 means auto ct2.Level()+1, -1 means fast auto ct2.Level(), >=0 sets a manual level")
	ltDropLevelFlag := flag.Int("lt-drop-level", -1, "deprecated alias for -lt-level; ignored when -lt-level is set")
	ltPostLevelFlag := flag.Int("lt-post-level", -2, "post-ParallelLT rescale target level; default -2 means auto ct2.Level(), -1 disables, >=0 sets a manual level")
	ltScaleAfterMulFlag := flag.Bool("lt-scale-after-mul", false, "experimental: skip post-ParallelLT rescale and let the following ct3*ct2 multiplication do the scale/rescale")
	finalLevelFlag := flag.Int("final-level", 0, "target level for the final output ciphertext after polynomial evaluation; 0 leaves only the base Q prime, -1 disables")
	polyNoiseTraceFlag := flag.Bool("poly-noise-trace", false, "print exact decrypted coefficient-noise for major polynomial-evaluation steps")
	polyNoisePreviewFlag := flag.Int("poly-noise-preview", 4, "number of coefficient-noise samples shown per major step")
	mulTraceFlag := flag.Bool("mul-trace", false, "print operation-level level/Qbits timing diagnostics for multiplications, rotate-and-add, and selected checkpoints")
	mulTraceNoiseFlag := flag.Bool("mul-trace-noise", false, "with -mul-trace, also decrypt/decode after every logged operation to fill noiseBudget/max|noise| columns; very slow")
	mulTraceSummaryOnlyFlag := flag.Bool("mul-trace-summary-only", false, "with -mul-trace, print only the operation summary instead of all per-row trace lines")
	progressFlag := flag.Bool("progress", false, "print progress logs")
	progressBlocksFlag := flag.Bool("progress-blocks", false, "print fine-grained block progress")
	schemeDFlag := flag.Bool("scheme-d", true, "use Scheme-D output scaling")
	extractLWEFlag := flag.Bool("extract-lwe", true, "after polynomial evaluation, run sparse SlotToCoeff, rescale to Q'=Q[0], final key switch, SampleExtract, and Q'->T LWE modulus switch")
	qprimeKSNoiseFlag := flag.Bool("qprime-ks-noise", true, "when -extract-lwe, print Qprime-domain noise before final key switch, after final key switch, and after SampleExtract for verbose single-run output")
	outputNoiseTableFlag := flag.Bool("output-noise-table", false, "print a per-output LWE noise table after Qprime->T; also printed automatically on final LWE failure")
	outputNoiseTableLimitFlag := flag.Int("output-noise-table-limit", 64, "maximum number of rows printed by -output-noise-table; <=0 means all rows")
	ct2NoiseProbeFlag := flag.Bool("ct2-noise-probe", false, "print only the immediate c2/ct2 grouped-powers noise probe even when the full -poly-noise-trace is off")
	stcBufferLevelFlag := flag.Int("stc-buffer-level", 0, "when -extract-lwe is used, first rescale the post-StC/no-StC tail ciphertext to this positive buffer level, then rescale to Q'=Q[0]; 0 disables the two-step tail")
	skipStCM1Flag := flag.Bool("skip-stc-m1", true, "when -extract-lwe and m=1, skip sparse SlotToCoeff because all slots are already the constant polynomial")
	m1ScaleFixFlag := flag.Bool("m1-scale-fix", true, "when -skip-stc-m1 and Scheme-D, multiply the m=1 polynomial output by gamma^{-1} if needed")
	m1AbsorbGammaInPolyFlag := flag.Bool("m1-absorb-gamma-in-poly", true, "for Scheme-D with m=1 and -skip-stc-m1, absorb the final gamma^{-1} into the polynomial/LUT coefficients; m>1 polynomials are not modified")
	deferPointwiseRescaleFlag := flag.Bool("defer-pointwise-rescale", true, "for Algorithm 5, compute ct3*ct2 with relin but without rescale, run RotateAndSum at that level, then rescale once after RotateAndSum; applies to m=1 and m>1")
	m1DeferPointwiseRescaleFlag := flag.Bool("m1-defer-pointwise-rescale", true, "deprecated compatibility alias for -defer-pointwise-rescale; set false to disable deferred pointwise rescale")
	m1GammaOneQFlag := flag.Bool("m1-gamma-one-q", false, "when -skip-stc-m1 and m=1, replace Q[1] by a special NTT prime so the final m=1 gamma is 1 and the scale-fix plaintext multiplication is skipped")
	m1GammaOnePrevGammaInvFlag := flag.Uint64("m1-gamma-one-prev-gamma-inv", 0, "optional legacy/debug input: previous run's printed gamma^{-1} modulo T; if omitted, the program predicts it from the planned scale and computes Q[1] automatically")
	m1GammaOneTargetResidueFlag := flag.Uint64("m1-gamma-one-target-residue", 0, "manual target residue for the special Q[1] modulo T; overrides the automatic m=1 gamma-one computation")
	m1GammaOneQMaxExtraBitsFlag := flag.Int("m1-gamma-one-q-max-extra-bits", 12, "maximum number of extra bits allowed when searching the special m=1 gamma-one Q[1] modulus")
	lweNFlag := flag.Int("lwe-n", 0, "required: output LWE secret dimension for the final extracted ciphertexts")
	lweSecretFlag := flag.String("lwe-secret", "sparseternary", "LWE secret distribution: sparseternary, fixedweight, ternary, or sign")
	lweHFlag := flag.Int("lwe-h", 0, "required: Hamming weight for -lwe-secret sparseternary/fixedweight")
	lweSecretSeedFlag := flag.Int64("lwe-secret-seed", 20260615, "PRNG seed for the LWE secret and final key-switch randomness stream")
	lweASeedFlag := flag.Int64("lwe-a-seed", 20260616, "base PRNG seed for uniformly random a-vectors of generated input LWE ciphertexts; run i uses base+i")
	ksBaseLogFlag := flag.Int("ks-base-log", 2, "base-2 gadget decomposition log for the final Q'-only no-P key switch")
	ksCenteredFlag := flag.Bool("ks-centered", true, "use centered signed gadget digits for the final Q'-only key switch; requires -ks-base-log >= 2")
	finalKSSigmaFlag := flag.Float64("final-ks-sigma", 3.2, "Gaussian stddev for manual final Q'-only key-switch key")
	levelAwareKeysFlag := flag.Bool("level-aware-keys", true, "generate evaluation keys only up to the maximum Q level where each key is used")
	keyLevelSummaryFlag := flag.Bool("key-level-summary", true, "print the level distribution and size of generated relinearization/Galois keys")
	runsFlag := flag.Int("run", 1, "number of online benchmark runs; parameters, BFV secret key, evaluation keys, and the LWE secret are generated once")
	runVerboseFlag := flag.Bool("run-verbose", false, "with -run > 1, print the detailed per-run diagnostic blocks instead of only compact per-run summaries")
	gcEveryFlag := flag.Int("gc-every", 0, "after clearing per-run references, explicitly run Go GC every k runs; 0 disables explicit run-level GC")
	freeOSMemoryFlag := flag.Bool("free-os-memory", false, "when explicit run-level GC is triggered, also ask Go to return idle heap pages to the OS")
	memProgressFlag := flag.Bool("mem-progress", false, "print Go heap statistics before and after explicit run-level GC")
	flag.Parse()
	if rest := flag.Args(); len(rest) > 0 {
		panic(fmt.Sprintf("unexpected positional argument(s) after flags: %v; did you forget a leading '-' before a flag name?", rest))
	}

	seenFlags := map[string]bool{}
	flag.Visit(func(f *flag.Flag) { seenFlags[f.Name] = true })
	requiredCoreFlags := []string{"N", "m", "degree", "T", "p", "func", "logq", "logp", "lwe-n", "lwe-h"}
	missingCoreFlags := make([]string, 0)
	for _, name := range requiredCoreFlags {
		if !seenFlags[name] {
			missingCoreFlags = append(missingCoreFlags, "-"+name)
		}
	}
	if len(missingCoreFlags) > 0 {
		panic(fmt.Sprintf("missing required core flag(s): %s. Keep these explicit; all other flags use optimized defaults.", strings.Join(missingCoreFlags, ", ")))
	}
	if *runsFlag < 1 {
		panic("-run must be at least 1")
	}
	if *mulTraceNoiseFlag && !*mulTraceFlag {
		*mulTraceFlag = true
	}
	globalMulTraceSummaryOnly = *mulTraceSummaryOnlyFlag
	globalCt2NoiseProbe = *ct2NoiseProbeFlag || *polyNoiseTraceFlag
	globalDeferPointwiseRescale = *deferPointwiseRescaleFlag && *m1DeferPointwiseRescaleFlag
	if *stcBufferLevelFlag < 0 {
		panic(fmt.Sprintf("-stc-buffer-level must be >= 0, got %d", *stcBufferLevelFlag))
	}
	if *lweStep1RescaleLevelsFlag < 0 {
		panic(fmt.Sprintf("-lwe-step1-rescale-levels must be >= 0, got %d", *lweStep1RescaleLevelsFlag))
	}
	if *ltLevelFlag < ltLevelExtraCT2Level {
		panic(fmt.Sprintf("-lt-level must be -2, -1, or >= 0, got %d", *ltLevelFlag))
	}
	if *ltDropLevelFlag < ltLevelExtraCT2Level {
		panic(fmt.Sprintf("-lt-drop-level must be -2, -1, or >= 0, got %d", *ltDropLevelFlag))
	}
	if *ltPostLevelFlag < ltPostAutoCT2Level {
		panic(fmt.Sprintf("-lt-post-level must be -2, -1, or >= 0, got %d", *ltPostLevelFlag))
	}
	if *ksCenteredFlag && *ksBaseLogFlag < 2 {
		panic("-ks-centered requires -ks-base-log >= 2")
	}

	globalProgress = newProgressLogger(*progressFlag)
	globalProgressBlocks = *progressBlocksFlag

	N := *NFlag
	m := *mFlag
	degree := *degreeFlag
	T := *TFlag
	if !isPow2(N) {
		panic(fmt.Sprintf("N=%d must be a power of two", N))
	}
	if !isPow2(m) {
		panic(fmt.Sprintf("m=%d must be a power of two", m))
	}
	if N%m != 0 {
		panic(fmt.Sprintf("m=%d must divide N=%d", m, N))
	}
	if T%(2*uint64(N)) != 1 {
		panic(fmt.Sprintf("T=%d must satisfy T = 1 mod 2N=%d", T, 2*N))
	}
	logN := log2Pow2(N)
	r := N / m
	inputModeNorm := strings.ToLower(strings.TrimSpace(*inputModeFlag))
	useLWEInput := isLWEToRLWEInputMode(inputModeNorm) || *lweToRLWEFlag
	phaseBuilderMode := inputModeNorm
	if useLWEInput {
		phaseBuilderMode = "phase"
	}

	placeholder := make([]uint64, degree+1)
	_, _, lowerLen, splitTop, err := splitPolynomialForAlg5(placeholder, degree, m)
	if err != nil {
		panic(err)
	}
	if !(m == 1 && lowerLen <= r) && (lowerLen <= r || lowerLen > r*r || lowerLen%r != 0) {
		panic(fmt.Sprintf("Algorithm 5 requires r < lowerLen <= r^2 and r|lowerLen unless m=1 direct path, got lowerLen=%d r=%d m=%d", lowerLen, r, m))
	}
	requiredDepth := 1
	if m == 1 && lowerLen <= r {
		requiredDepth = monomialConsumedDepth(lowerLen) + 2
	} else {
		requiredDepth, err = autoDepthForWrappedPolyEval(r, lowerLen)
		if err != nil {
			panic(err)
		}
	}
	if useLWEInput && *lweStep1RescaleLevelsFlag > 0 {
		requiredDepth += *lweStep1RescaleLevelsFlag
	}
	if *extractLWEFlag {
		if *stcBufferLevelFlag > 0 {
			requiredDepth += *stcBufferLevelFlag
		} else if *skipStCM1Flag && m == 1 && requiredDepth > 0 {
			requiredDepth--
		}
	}

	var logQBits, logPBits []int
	if strings.TrimSpace(*logQFlag) == "" || strings.TrimSpace(*logPFlag) == "" {
		prof, err := chooseAutoProfileForLogNDepth(logN, requiredDepth)
		if err != nil {
			panic(err)
		}
		autoLit, err := prof.BuildLiteral(requiredDepth, T)
		if err != nil {
			panic(err)
		}
		if strings.TrimSpace(*logQFlag) == "" {
			logQBits = append([]int(nil), autoLit.LogQ...)
		}
		if strings.TrimSpace(*logPFlag) == "" {
			logPBits = append([]int(nil), autoLit.LogP...)
		}
	}
	if strings.TrimSpace(*logQFlag) != "" {
		logQBits, err = parseBitListExpanded(*logQFlag)
		if err != nil {
			panic(fmt.Errorf("invalid -logq: %w", err))
		}
	}
	if strings.TrimSpace(*logPFlag) != "" {
		logPBits, err = parseBitListExpanded(*logPFlag)
		if err != nil {
			panic(fmt.Errorf("invalid -logp: %w", err))
		}
	}
	if len(logQBits)-1 < requiredDepth {
		panic(fmt.Sprintf("insufficient LogQ: MaxLevel=%d, requiredDepth=%d", len(logQBits)-1, requiredDepth))
	}
	literal, err := chooseLiteral(logN, T, logQBits, logPBits)
	if err != nil {
		panic(err)
	}
	params, err := bfv.NewParametersFromLiteral(literal)
	if err != nil {
		panic(err)
	}

	skipStCForM1 := *skipStCM1Flag && m == 1
	m1AbsorbGammaEnabled := *m1AbsorbGammaInPolyFlag && *schemeDFlag && *extractLWEFlag && skipStCForM1
	if m1AbsorbGammaEnabled && *m1GammaOneQFlag {
		fmt.Println("m=1 gamma absorb note     : -m1-absorb-gamma-in-poly=true, so -m1-gamma-one-q is ignored; the polynomial is pre-scaled instead of changing Q[1]")
		*m1GammaOneQFlag = false
	}
	effectiveLTLevel := *ltLevelFlag
	if effectiveLTLevel < 0 && *ltDropLevelFlag >= 0 {
		effectiveLTLevel = *ltDropLevelFlag
	}
	effectiveLTPostLevel := *ltPostLevelFlag
	leadingTermEvaluated := !useLargeAlg5Branch(N, m, lowerLen)

	var m1GammaOneInfo *M1GammaOneQInfo
	if *m1GammaOneQFlag {
		if !(*extractLWEFlag && *schemeDFlag && skipStCForM1) {
			panic("-m1-gamma-one-q requires -extract-lwe=true, -scheme-d=true, -skip-stc-m1=true, and m=1")
		}
		planForM1 := newRotationKeyPlan()
		polyInputLevelForM1 := params.MaxLevel()
		if useLWEInput {
			polyInputLevelForM1 -= *lweStep1RescaleLevelsFlag
		}
		polyLevelInfoForM1, err := addPolyEvalRotationKeyUses(params, planForM1, polyInputLevelForM1, m, lowerLen, *dropBeforeLTFlag, effectiveLTLevel, effectiveLTPostLevel, *ltScaleAfterMulFlag, leadingTermEvaluated)
		if err != nil {
			panic(fmt.Errorf("m=1 gamma-one level planning failed: %w", err))
		}
		polyInputScaleForM1, err := estimatePolynomialInputScaleModT(params, polyInputLevelForM1, useLWEInput, T)
		if err != nil {
			panic(fmt.Errorf("m=1 gamma-one input-scale planning failed: %w", err))
		}
		autoTargetResidue, autoOutputScale, autoTailRestProduct, autoOldGamma, autoOldGammaInv, err := estimateM1GammaOneQ1TargetResidue(params, T, m, lowerLen, polyInputLevelForM1, polyInputScaleForM1, *dropBeforeLTFlag, effectiveLTLevel, effectiveLTPostLevel, *ltScaleAfterMulFlag, leadingTermEvaluated, polyLevelInfoForM1.OutputLevel)
		if err != nil {
			panic(fmt.Errorf("m=1 gamma-one automatic residue computation failed: %w", err))
		}
		literal, logQBits, m1GammaOneInfo, err = specializeM1GammaOneQFromObservedGamma(params, literal, logQBits, logN, T, m, polyLevelInfoForM1.OutputLevel, *m1GammaOnePrevGammaInvFlag, *m1GammaOneTargetResidueFlag, autoTargetResidue, autoOutputScale, autoTailRestProduct, autoOldGamma, autoOldGammaInv, *m1GammaOneQMaxExtraBitsFlag)
		if err != nil {
			panic(fmt.Errorf("m=1 gamma-one Q selection failed: %w", err))
		}
		params, err = bfv.NewParametersFromLiteral(literal)
		if err != nil {
			panic(fmt.Errorf("rebuild parameters with m=1 gamma-one Q[1]: %w", err))
		}
	}

	encoder := bfv.NewEncoder(params)
	qPrime := params.Q()[0]
	schemeDTargetScale := uint64(0)
	schemeDScaleS := uint64(1)
	schemeDInvS := uint64(1)
	if *schemeDFlag {
		schemeDTargetScale, schemeDScaleS, err = tailSchemeDScale(qPrime, T)
		if err != nil {
			panic(err)
		}
		schemeDInvS, err = tailInvModUint64(schemeDScaleS, T)
		if err != nil {
			panic(err)
		}
	}

	var step1Plan LWEToRLWEPackingPlan
	if useLWEInput {
		if *lweNFlag <= 0 || *lweNFlag > N {
			panic(fmt.Sprintf("-input-mode=lwe requires -lwe-n in [1,N], got lwe-n=%d, N=%d", *lweNFlag, N))
		}
		step1Plan, err = planLWEToRLWEStep1(N, m, *lweNFlag)
		if err != nil {
			panic(err)
		}
	}

	rotationPlan := newRotationKeyPlan()
	polyInputLevelForPlan := params.MaxLevel()
	if useLWEInput {
		polyInputLevelForPlan -= *lweStep1RescaleLevelsFlag
	}
	if polyInputLevelForPlan < 0 {
		panic(fmt.Sprintf("polynomial input level became negative: MaxLevel=%d, lwe-step1-rescale-levels=%d", params.MaxLevel(), *lweStep1RescaleLevelsFlag))
	}
	polyLevelInfo, err := addPolyEvalRotationKeyUses(params, rotationPlan, polyInputLevelForPlan, m, lowerLen, *dropBeforeLTFlag, effectiveLTLevel, effectiveLTPostLevel, *ltScaleAfterMulFlag, leadingTermEvaluated)
	if err != nil {
		panic(err)
	}
	var stcDiagExt [][]uint64
	var stcStep int
	if useLWEInput {
		if err := addSparseRotateAndSumKeyUses(params, rotationPlan, m, step1Plan.InnerPeriod, params.MaxLevel(), "LWE->RLWE Step1 row-sum"); err != nil {
			panic(fmt.Errorf("add LWE->RLWE Step1 rotation keys: %w", err))
		}
	}
	if *extractLWEFlag {
		if *lweNFlag <= 0 || *lweNFlag > N {
			panic(fmt.Sprintf("-lwe-n must be in [1,N], got lwe-n=%d, N=%d", *lweNFlag, N))
		}
		stcStep = (N / 2) / m
		if !skipStCForM1 {
			_, matrixU, _, err := buildBasisMatrixU(params, encoder, N, m, T)
			if err != nil {
				panic(fmt.Errorf("build sparse SlotToCoeff basis: %w", err))
			}
			diagMod, _ := buildRightMulDiagonals(matrixU, T)
			stcDiagExt = make([][]uint64, len(diagMod))
			for j := range diagMod {
				stcDiagExt[j] = repeatVector(diagMod[j], r)
			}
			stcInputLevel := polyLevelInfo.OutputLevel
			if stcInputLevel < 1 {
				stcInputLevel = params.MaxLevel()
			}
			if err := addSlotToCoeffBSGSKeyUses(params, rotationPlan, m, stcInputLevel); err != nil {
				panic(err)
			}
		}
	}
	if !*levelAwareKeysFlag {
		rotationPlan.ForceLevel(params.MaxLevel())
	}
	galEls := rotationPlan.GaloisElements()
	relinKeyLevel := polyInputLevelForPlan
	if relinKeyLevel < 0 || relinKeyLevel > params.MaxLevel() || !*levelAwareKeysFlag {
		relinKeyLevel = params.MaxLevel()
	}

	keyStart := time.Now()
	kgen := rlwe.NewKeyGenerator(params)
	sk := kgen.GenSecretKeyNew()
	relinLevelForKey := relinKeyLevel
	rlk := kgen.GenRelinearizationKeyNew(sk, rlwe.EvaluationKeyParameters{LevelQ: &relinLevelForKey})
	gks, rotationKeyLevelStats, galoisKeySizeBytes, err := generateGaloisKeysFromPlan(params, kgen, sk, rotationPlan)
	if err != nil {
		panic(fmt.Errorf("generate level-aware Galois keys: %w", err))
	}
	evaluationKeys := rlwe.NewMemEvaluationKeySet(rlk, gks...)
	relinKeySizeBytes := int64(rlk.BinarySize())
	evalKeySizeBytes := relinKeySizeBytes + galoisKeySizeBytes
	keyTime := time.Since(keyStart)
	enc := bfv.NewEncryptor(params, sk)
	dec := bfv.NewDecryptor(params, sk)
	eval := bfv.NewEvaluator(params, evaluationKeys, false)

	var fixedLWESecretSigned []int64
	var fixedLWESecretInfo TailSecretInfo
	var finalKSRng *rand.Rand
	if useLWEInput || *extractLWEFlag {
		finalKSRng = rand.New(rand.NewSource(*lweSecretSeedFlag))
		fixedLWESecretSigned, fixedLWESecretInfo, err = tailSampleLWESecret(*lweNFlag, *lweSecretFlag, *lweHFlag, finalKSRng)
		if err != nil {
			panic(err)
		}
	}

	fmt.Println("========== One-time setup ==========")
	fmt.Printf("parameters                 : LogN=%d, N=%d, m=%d, r=%d, T=%d\n", logN, N, m, r, T)
	fmt.Printf("LogQ / LogP                : %v / %v\n", logQBits, logPBits)
	fmt.Printf("initial ciphertext modulus : L%d/%db\n", params.MaxLevel(), qBitsOfLevel(params, params.MaxLevel()))
	fmt.Printf("degree / lowerLen          : %d / %d, splitTop=%v\n", degree, lowerLen, splitTop)
	fmt.Printf("Galois keys                : %d\n", len(galEls))
	fmt.Printf("key generation             : %v\n", keyTime)
	if *keyLevelSummaryFlag {
		printEvaluationKeyLevelSummary(params, relinKeyLevel, relinKeySizeBytes, rotationKeyLevelStats, evalKeySizeBytes, *levelAwareKeysFlag)
	}
	fmt.Printf("ParallelLT level policy    : %s\n", formatParallelLTLevelPolicy(*dropBeforeLTFlag, effectiveLTLevel, effectiveLTPostLevel, *ltScaleAfterMulFlag))
	fmt.Println("ParallelLT implementation  : hoisted BSGS / double-hoisted Algorithm-3 path")
	if globalDeferPointwiseRescale {
		fmt.Println("Algorithm 5 final-sum rescale : deferred after line 7/12 RotateAndSum")
	}
	if *schemeDFlag {
		fmt.Printf("Scheme-D Qprime/S/K        : Qprime=%d, S=%d, K=ceil(Qprime/T)=%d, S^{-1}=%d mod T\n", qPrime, schemeDScaleS, schemeDTargetScale, schemeDInvS)
	}
	if m1GammaOneInfo != nil {
		if m1GammaOneInfo.OutputLevel > 0 {
			fmt.Printf("m=1 gamma-one Q[1]        : Q[1]=%d (%d bits), Q[1] mod T=%d, target residue=%d; mode=%s; output before final tail L%d\n", m1GammaOneInfo.Prime, m1GammaOneInfo.Bits, m1GammaOneInfo.Prime%T, m1GammaOneInfo.TargetResidueModT, m1GammaOneInfo.Mode, m1GammaOneInfo.OutputLevel)
		} else {
			fmt.Printf("m=1 gamma-one Q[1]        : Q[1]=%d (%d bits), Q[1] mod T=%d, target residue=%d; mode=%s; polynomial output L0, so Q[1] is specialized as the last polynomial-evaluation modulus\n", m1GammaOneInfo.Prime, m1GammaOneInfo.Bits, m1GammaOneInfo.Prime%T, m1GammaOneInfo.TargetResidueModT, m1GammaOneInfo.Mode)
		}
		if m1GammaOneInfo.AutoComputed {
			if m1GammaOneInfo.OutputLevel > 0 {
				fmt.Printf("m=1 gamma-one auto        : predicted output scale σ=%d, product Q[2..L%d]=%d mod T, old gamma=%d, old gamma^{-1}=%d\n", m1GammaOneInfo.OutputScaleModT, m1GammaOneInfo.OutputLevel, m1GammaOneInfo.TailRestProductModT, m1GammaOneInfo.PredictedOldGammaModT, m1GammaOneInfo.PredictedOldGammaInvModT)
			} else {
				fmt.Printf("m=1 gamma-one auto        : old polynomial output scale σ=%d, old gamma=%d, old gamma^{-1}=%d; target Q[1] residue = σ * old Q[1] mod T\n", m1GammaOneInfo.OutputScaleModT, m1GammaOneInfo.PredictedOldGammaModT, m1GammaOneInfo.PredictedOldGammaInvModT)
			}
		}
		if m1GammaOneInfo.OldGammaInvModT != 0 {
			fmt.Printf("m=1 gamma-one legacy      : supplied old gamma^{-1}=%d, old gamma=%d, old Q[1] mod T=%d\n", m1GammaOneInfo.OldGammaInvModT, m1GammaOneInfo.OldGammaModT, m1GammaOneInfo.OldQ1ResidueModT)
		}
		if m1GammaOneInfo.OutputLevel > 0 {
			fmt.Printf("m=1 gamma-one final Q'    : Q[0]=%d (%d bits); product Q[1..L%d] mod T=%d\n", m1GammaOneInfo.FinalQPrime, m1GammaOneInfo.FinalQPrimeBits, m1GammaOneInfo.OutputLevel, m1GammaOneInfo.ProductDroppedModT)
		} else {
			fmt.Printf("m=1 gamma-one final Q'    : Q[0]=%d (%d bits); no tail dropped product; Q[1] is consumed inside polynomial evaluation\n", m1GammaOneInfo.FinalQPrime, m1GammaOneInfo.FinalQPrimeBits)
			fmt.Printf("m=1 gamma-one warning     : poly-last-Q[1] is experimental; changing a modulus consumed inside polynomial evaluation can change Lattigo plaintext-scale semantics. Prefer keeping output at L1 and specializing the tail Q[1], or pre-scale the LUT coefficients.\n")
		}
		if m1GammaOneInfo.Bits != m1GammaOneInfo.RequestedBits {
			fmt.Printf("m=1 gamma-one note        : requested %d-bit Q[1] had no suitable prime; used %d-bit Q[1] instead\n", m1GammaOneInfo.RequestedBits, m1GammaOneInfo.Bits)
		}
	}
	if useLWEInput {
		fmt.Printf("fixed LWE secret           : %s; h=%d, #+1=%d, #-1=%d\n", fixedLWESecretInfo.Name, fixedLWESecretInfo.H, fixedLWESecretInfo.Pos, fixedLWESecretInfo.Neg)
	}
	fmt.Println("====================================")
	fmt.Println()

	detailed := *runsFlag == 1 || *runVerboseFlag
	allCorrect := true
	allNoiseDiffs := make([]int64, 0, (*runsFlag)*m)
	allQBeforeKSDiffs := make([]int64, 0, (*runsFlag)*m)
	allQAfterKSDiffs := make([]int64, 0, (*runsFlag)*m)
	allQKSDiffs := make([]int64, 0, (*runsFlag)*m)
	allQExtractedDiffs := make([]int64, 0, (*runsFlag)*m)
	runResults := make([]BenchRunSummary, 0, *runsFlag)
	var sumDynamic BenchDynamicSetupTiming
	var sumOnline BenchOnlineTiming
	var sumRunWall time.Duration
	var sumQPrimeProbeWall time.Duration
	var lastTailSecretInfo TailSecretInfo
	var lastTailDigits int
	var lastTailNoiseT TailNoiseStats
	programWallStart := time.Now()
	m1GammaAbsorbScale := uint64(1)
	m1GammaAbsorbCalibrated := !m1AbsorbGammaEnabled

	for runIdx := 0; runIdx < *runsFlag; runIdx++ {
		runNo := runIdx + 1
		runWallStart := time.Now()
		runFuncSeed := *funcSeedFlag + int64(runIdx)
		runCoeffSeed := *coeffSeedFlag + int64(runIdx)
		runInputSeed := *inputSeedFlag + int64(runIdx)
		runPhaseErrorSeed := *phaseErrorSeedFlag + int64(runIdx)
		runLWEASeed := *lweASeedFlag + int64(runIdx)
		progressf("run %d/%d: dynamic setup", runNo, *runsFlag)
		resetMulTraceForRun(params, encoder, dec, *mulTraceFlag && detailed, *mulTraceNoiseFlag && detailed)

		var runRes BenchRunSummary
		runRes.Run = runNo
		runRes.FuncSeed = runFuncSeed
		runRes.LWENoiseSeed = runPhaseErrorSeed
		runRes.LWEASeed = runLWEASeed
		runRes.MsgSeed = runInputSeed

		polyBuild, err := buildRunPolynomialCoeffs(T, *pFlag, degree, m, *coeffModeFlag, *funcSpecFlag, *funcTableFlag, *funcFileFlag, runCoeffSeed, runFuncSeed, *schemeDFlag, schemeDScaleS)
		if err != nil {
			panic(err)
		}
		if polyBuild.LowerLen != lowerLen || polyBuild.SplitTop != splitTop {
			panic("internal run polynomial split changed across runs")
		}
		runRes.Dynamic.FunctionTable += polyBuild.Timing.FunctionTable
		runRes.Dynamic.LUTBuild += polyBuild.Timing.LUTBuild
		runRes.FuncDesc = polyBuild.FuncDesc

		inputParsed, err := parseVector(*inputFlag)
		if err != nil {
			panic(err)
		}
		phaseX, inputMessages, inputErrors, inputDesc, err := buildRLWEPhaseInputs(phaseBuilderMode, inputParsed, *messageFlag, *phaseErrorFlag, m, T, *pFlag, runInputSeed, runPhaseErrorSeed, *phaseErrorSigmaFlag, *phaseErrorBoundFlag)
		if err != nil {
			panic(err)
		}

		var inputLWECts []LWECiphertext
		if useLWEInput {
			if len(inputMessages) != m || len(inputErrors) != m {
				panic("-input-mode=lwe requires phase/message generation; internal message/error vectors are missing")
			}
			alpha := T / *pFlag
			stLWE := time.Now()
			var lwePhaseX []uint64
			inputLWECts, lwePhaseX, err = generateRandomLWECiphertexts(inputMessages, fixedLWESecretSigned, alpha, T, inputErrors, runLWEASeed)
			runRes.Dynamic.LWECiphertexts = time.Since(stLWE)
			if err != nil {
				panic(fmt.Errorf("generate input LWE ciphertexts: %w", err))
			}
			if bad := firstMismatch(lwePhaseX, phaseX); bad >= 0 {
				panic(fmt.Sprintf("internal LWE phase mismatch at item %d: generated=%d expected=%d", bad, lwePhaseX[bad], phaseX[bad]))
			}
			for i := range inputLWECts {
				gotPhase := rawDecryptLWE(inputLWECts[i], fixedLWESecretSigned, T)
				if gotPhase != phaseX[i] {
					panic(fmt.Sprintf("generated LWE ciphertext %d decrypts to phase %d, want %d", i, gotPhase, phaseX[i]))
				}
			}
			inputDesc = fmt.Sprintf("LWE->RLWE Step 1: %s; generated LWE phases x=Delta*m+e in Z_%d", step1Plan.Desc, T)
		}

		polyInputX := append([]uint64(nil), phaseX...)
		slots, rCheck, err := sparsePackMod(polyInputX, N)
		if err != nil {
			panic(err)
		}
		if rCheck != r {
			panic("internal r mismatch")
		}

		var ctIn *rlwe.Ciphertext
		var step1Wall, step1NormalizeTime time.Duration
		var step1Stats LWEToRLWEStats
		var step1StartLevel, step1RescaleTarget int
		if useLWEInput {
			stStep1 := time.Now()
			secretModT := tailSignedCoeffsToMod(fixedLWESecretSigned, T)
			ctIn, step1Stats, err = homomorphicDecryptLWEToSparseRLWE(params, encoder, enc, eval, inputLWECts, secretModT, step1Plan, m)
			if err != nil {
				panic(fmt.Errorf("LWE->RLWE Step 1 failed: %w", err))
			}
			step1Wall = time.Since(stStep1)
			step1StartLevel = ctIn.Level()
			step1RescaleTarget = ctIn.Level()
			if *lweStep1RescaleLevelsFlag > 0 {
				step1RescaleTarget = ctIn.Level() - *lweStep1RescaleLevelsFlag
				if step1RescaleTarget < 0 {
					panic(fmt.Sprintf("-lwe-step1-rescale-levels=%d exceeds Step1 output level L%d", *lweStep1RescaleLevelsFlag, ctIn.Level()))
				}
				step1NormalizeTime, err = rescaleCiphertextToLevelWithTrace(eval, ctIn, step1RescaleTarget, "LWE->RLWE Step1 normalization before polynomial evaluation")
				if err != nil {
					panic(fmt.Errorf("LWE->RLWE Step1 normalization failed: %w", err))
				}
			}
		} else {
			ptIn, err := encodeBatchedPlaintextAtMaxLevel(params, encoder, slots)
			if err != nil {
				panic(err)
			}
			ctIn, err = enc.EncryptNew(ptIn)
			if err != nil {
				panic(err)
			}
		}
		polyRegisterExpected(ctIn, slots)

		largeAlg5Branch := useLargeAlg5Branch(N, m, lowerLen)
		if m1AbsorbGammaEnabled && !m1GammaAbsorbCalibrated {
			stCalib := time.Now()
			var calibPre *PreprocessedPolyEval
			if *precomputeFlag {
				calibPre, err = preprocessPolyEvalPlaintextsAligned(params, encoder, m, lowerLen, polyBuild.CoeffsLower, polyBuild.LeadCoeffs, ctIn.Level(), *dropBeforeLTFlag, effectiveLTLevel, effectiveLTPostLevel, *ltScaleAfterMulFlag, largeAlg5Branch)
				if err != nil {
					panic(fmt.Errorf("m=1 gamma absorb calibration plaintext precompute failed: %w", err))
				}
			}
			savedMulTracer := globalMulTracer
			globalMulTracer = newMulTraceRecorder(false, false, params, encoder, dec)
			ctCalibIn := ctIn.CopyNew()
			polyCopyExpected(ctIn, ctCalibIn)
			ctCalibOut, _, err := benchPolyEvalWithPlan(params, eval, ctCalibIn, m, lowerLen, r, polyBuild.CoeffsLower, polyBuild.LeadCoeffs, calibPre, largeAlg5Branch, *dropBeforeLTFlag, effectiveLTLevel, effectiveLTPostLevel, *ltScaleAfterMulFlag)
			globalMulTracer = savedMulTracer
			if err != nil {
				panic(fmt.Errorf("m=1 gamma absorb calibration polynomial evaluation failed: %w", err))
			}
			calibGamma, err := tailScaleAfterRescaleToLevel(params, scaleModUint64(ctCalibOut.Scale, T), ctCalibOut.Level(), 0, T)
			if err != nil {
				panic(fmt.Errorf("m=1 gamma absorb calibration scale computation failed: %w", err))
			}
			m1GammaAbsorbScale, err = tailInvModUint64(calibGamma, T)
			if err != nil {
				panic(fmt.Errorf("m=1 gamma absorb calibration gamma=%d is not invertible mod T=%d: %w", calibGamma, T, err))
			}
			m1GammaAbsorbCalibrated = true
			runRes.Dynamic.M1GammaCalibration += time.Since(stCalib)
			if detailed {
				fmt.Printf("m=1 gamma absorb calibration: output L%d, raw gamma=%d, pre-scale gamma^{-1}=%d, time=%v (offline; not counted in online)\n", ctCalibOut.Level(), calibGamma, m1GammaAbsorbScale, runRes.Dynamic.M1GammaCalibration)
			}
			ctCalibIn = nil
			ctCalibOut = nil
			calibPre = nil
		}
		m1GammaAbsorbThisRun := m1AbsorbGammaEnabled && m1GammaAbsorbCalibrated && m1GammaAbsorbScale%T != 1
		if m1GammaAbsorbThisRun {
			polyBuild = scaleRunPolynomialBuildResult(polyBuild, m1GammaAbsorbScale, T, fmt.Sprintf("m=1 gamma^{-1} pre-absorbed into polynomial, gamma^{-1}=%d", m1GammaAbsorbScale))
		}

		var pre *PreprocessedPolyEval
		if *precomputeFlag {
			st := time.Now()
			pre, err = preprocessPolyEvalPlaintextsAligned(params, encoder, m, lowerLen, polyBuild.CoeffsLower, polyBuild.LeadCoeffs, ctIn.Level(), *dropBeforeLTFlag, effectiveLTLevel, effectiveLTPostLevel, *ltScaleAfterMulFlag, largeAlg5Branch)
			if err != nil {
				panic(err)
			}
			runRes.Dynamic.PolyPrecompute = time.Since(st)
		}
		runRes.Dynamic.Total = runRes.Dynamic.FunctionTable + runRes.Dynamic.LUTBuild + runRes.Dynamic.LWECiphertexts + runRes.Dynamic.PolyPrecompute + runRes.Dynamic.M1GammaCalibration

		polyNoiseTracer := makePolyNoiseTracer(*polyNoiseTraceFlag && detailed, params, encoder, dec, *polyNoisePreviewFlag, false)
		setPolyNoiseTraceContext(polyNoiseTracer, polyInputX, polyBuild.CoeffsLower, polyBuild.LeadCoeffs)

		if pre != nil && runIdx == 0 && !detailed {
			fmt.Printf("plaintext precompute       : %v for run 1 (dynamic/offline per run)\n", runRes.Dynamic.PolyPrecompute)
			printPolyPrecomputePlaintextMemorySummary(params, pre)
		}
		if detailed {
			fmt.Printf("========== Run %d/%d ==========%s", runNo, *runsFlag, "\n")
			fmt.Printf("dynamic setup time         : %v (lwe=%v, func=%v, lut=%v, pt=%v, gamma=%v)\n", runRes.Dynamic.Total, runRes.Dynamic.LWECiphertexts, runRes.Dynamic.FunctionTable, runRes.Dynamic.LUTBuild, runRes.Dynamic.PolyPrecompute, runRes.Dynamic.M1GammaCalibration)
			fmt.Printf("coefficients               : %s\n", polyBuild.CoeffDesc)
			fmt.Printf("plaintext precompute       : %v (offline for this run)\n", runRes.Dynamic.PolyPrecompute)
			if pre != nil {
				printPolyPrecomputePlaintextMemorySummary(params, pre)
			}
			fmt.Printf("input mode                 : %s\n", inputDesc)
			if useLWEInput {
				fmt.Printf("LWE->RLWE Step1            : raw level=L%d/%db -> input level=L%d/%db, blocks=%d, period=%d, CMult=%d, rotations=%d, rowrots=%d, adds=%d, bsk-enc=%d, time=%v, normalize=%v\n", step1StartLevel, qBitsOfLevel(params, step1StartLevel), ctIn.Level(), qBitsOfLevel(params, ctIn.Level()), step1Stats.Blocks, step1Stats.InnerPeriod, step1Stats.CMults, step1Stats.Rotations, step1Stats.RowRotations, step1Stats.Additions, step1Stats.Encryptions, step1Wall, step1NormalizeTime)
			}
			if len(inputMessages) > 0 {
				fmt.Printf("input messages m[0:%d]     : %v\n", minInt(len(inputMessages), 8), inputMessages[:minInt(len(inputMessages), 8)])
			}
			if len(inputErrors) > 0 {
				fmt.Printf("input phase errors e[0:%d] : %v\n", minInt(len(inputErrors), 8), inputErrors[:minInt(len(inputErrors), 8)])
			}
			fmt.Printf("input phase x[0:%d]        : %v\n", minInt(len(phaseX), 8), phaseX[:minInt(len(phaseX), 8)])
		}

		var ctOut *rlwe.Ciphertext
		var tm BenchPolyEvalTiming
		start := time.Now()
		ctOut, tm, err = benchPolyEvalWithPlan(params, eval, ctIn, m, lowerLen, r, polyBuild.CoeffsLower, polyBuild.LeadCoeffs, pre, largeAlg5Branch, *dropBeforeLTFlag, effectiveLTLevel, effectiveLTPostLevel, *ltScaleAfterMulFlag)
		if err != nil {
			panic(err)
		}

		expectedFirst := fullPolyValues(polyInputX, polyBuild.CoeffsLower, polyBuild.LeadCoeffs, lowerLen, T)
		m1GammaAbsorbUndoScale := uint64(1)
		logicalExpectedFirst := expectedFirst
		if m1GammaAbsorbThisRun {
			m1GammaAbsorbUndoScale, err = tailInvModUint64(m1GammaAbsorbScale, T)
			if err != nil {
				panic(fmt.Errorf("m=1 gamma absorb pre-scale %d is not invertible modulo T=%d: %w", m1GammaAbsorbScale, T, err))
			}
			logicalExpectedFirst = scalarMulVectorMod(expectedFirst, m1GammaAbsorbUndoScale, T)
		}
		expectedSlots := repeatVector(expectedFirst, r)
		polyRegisterExpected(ctOut, expectedSlots)
		finalLevelBeforeRescale := ctOut.Level()
		finalQBitsBeforeRescale := qBitsOfLevel(params, ctOut.Level())
		if !*extractLWEFlag && *finalLevelFlag >= 0 {
			if *finalLevelFlag > ctOut.Level() {
				panic(fmt.Sprintf("-final-level=%d exceeds current output level L%d", *finalLevelFlag, ctOut.Level()))
			}
			finalRescaleTime, err := rescaleCiphertextToLevelWithTrace(eval, ctOut, *finalLevelFlag, "Polynomial output normalization")
			if err != nil {
				panic(err)
			}
			tm.Breakdown.FinalRescale = finalRescaleTime
			tm.Total += finalRescaleTime
		}
		polyOnlineTime := time.Since(start)
		clearPolyNoiseTraceContext()

		gotSlots, err := decodeSlots(params, encoder, dec, ctOut)
		if err != nil {
			panic(err)
		}
		ok := firstMismatch(gotSlots, expectedSlots) < 0
		runRes.PolyPlainOK = ok
		if !ok && detailed {
			bad := firstMismatch(gotSlots, expectedSlots)
			fmt.Printf("polynomial plaintext mismatch: first=%d, got=%d, want=%d\n", bad, gotSlots[bad], expectedSlots[bad])
		}

		var expectedOutputMessages, decodedOutputMessages []uint64
		messageOK := true
		if len(inputMessages) > 0 && len(polyBuild.FuncTable) == int(*pFlag) {
			alpha := T / *pFlag
			expectedOutputMessages = make([]uint64, len(inputMessages))
			decodedOutputMessages = make([]uint64, len(inputMessages))
			for i := range inputMessages {
				expectedOutputMessages[i] = polyBuild.FuncTable[int(inputMessages[i]%*pFlag)] % *pFlag
				phaseForDecode := gotSlots[i]
				if *schemeDFlag {
					phaseForDecode = tailMulMod(phaseForDecode, schemeDInvS, T)
					if m1GammaAbsorbThisRun {
						phaseForDecode = tailMulMod(phaseForDecode, m1GammaAbsorbUndoScale, T)
					}
				}
				decodedOutputMessages[i] = decodePhaseToMessageModP(phaseForDecode, alpha, *pFlag, T)
				if decodedOutputMessages[i] != expectedOutputMessages[i] {
					messageOK = false
				}
			}
		}

		var stcWall, tailRescaleWall, tailBufferRescaleWall, tailFinalRescaleWall, finalKSWall, sampleExtractWall, qToTWall time.Duration
		var qprimeNoiseProbeWall time.Duration
		var tailNoiseT TailNoiseStats
		var tailSecretInfo TailSecretInfo
		var tailDigits int
		var tailPhaseT, tailExpectedPhase, tailMuOut []uint64
		var targetQ []uint64
		var tailOK = true
		var tailCoeffPlaintextOK = true
		var tailCoeffBad = -1
		var tailCoeffGot, tailCoeffWant uint64
		var tailNoiseQBeforeKS, tailNoiseQAfterKSRLWE, tailNoiseQAfterExtract, tailNoiseQKSDelta, tailNoiseQExtractDelta TailNoiseStats
		var tailPhaseQBeforeKS, tailPhaseQAfterKSRLWE, tailPhaseQAfterExtract []uint64
		var tailNoiseQBuffer TailBigNoiseStats
		var stcStats BSGSStats
		stcRawScaleModT := uint64(1)
		stcResidualScaleModT := uint64(1)
		stcPreAbsorbScaleModT := uint64(1)
		stcScaleCorrection := uint64(1)

		if *extractLWEFlag {
			if !*schemeDFlag && detailed {
				fmt.Println("warning: -extract-lwe is intended for -scheme-d=true; ordinary BGV raw t^{-1}M generally does not Q'->T to M")
			}
			if !skipStCForM1 && ctOut.Level() < 1 {
				panic(fmt.Sprintf("sparse SlotToCoeff needs at least one remaining level; got poly output L%d", ctOut.Level()))
			}
			tailExpectedPhase = append([]uint64(nil), logicalExpectedFirst...)
			stcPlainTarget := append([]uint64(nil), expectedFirst...)
			stcDiagForRun := stcDiagExt
			if *schemeDFlag {
				tailExpectedPhase = scalarMulVectorMod(logicalExpectedFirst, schemeDInvS, T)
			}
			stcRawScaleModT = 1
			stcScaleCorrection = 1
			st := time.Now()
			var ctCoeff *rlwe.Ciphertext
			if skipStCForM1 {
				ctCoeff = ctOut.CopyNew()
				polyCopyExpected(ctOut, ctCoeff)
				if *schemeDFlag {
					stcRawScaleModT, err = tailScaleAfterRescaleToLevel(params, scaleModUint64(ctOut.Scale, T), ctOut.Level(), 0, T)
					if err != nil {
						panic(fmt.Errorf("compute m=1 final BGV scale: %w", err))
					}
					stcResidualScaleModT = stcRawScaleModT
					if m1GammaAbsorbThisRun {
						stcPreAbsorbScaleModT = m1GammaAbsorbScale % T
						stcResidualScaleModT = tailMulMod(stcRawScaleModT, stcPreAbsorbScaleModT, T)
					}
					if stcResidualScaleModT != 1 {
						stcScaleCorrection, err = tailInvModUint64(stcResidualScaleModT, T)
						if err != nil {
							panic(fmt.Errorf("m=1 residual BGV scale is not invertible modulo T: %w", err))
						}
						if *m1ScaleFixFlag {
							corrSlots := make([]uint64, N)
							for i := range corrSlots {
								corrSlots[i] = stcScaleCorrection
							}
							before := ctCoeff.CopyNew()
							polyCopyExpected(ctCoeff, before)
							mulStart := time.Now()
							ctCoeff, err = eval.MulNew(ctCoeff, corrSlots)
							mulDur := time.Since(mulStart)
							if err != nil {
								panic(fmt.Errorf("m=1 residual gamma^{-1} plaintext correction failed: %w", err))
							}
							logMulTrace(fmt.Sprintf("m=1 no-StC residual scale correction: multiply by residual gamma^{-1}=%d before extraction", stcScaleCorrection), "ct-pt-StC", before, nil, ctCoeff, false, mulDur, expectedForCtPlainMul(before, corrSlots))
							stcStats.PlainCipherMults++
							stcPlainTarget = scalarMulVectorMod(expectedFirst, stcScaleCorrection, T)
						}
					}
				}
			} else {
				if *schemeDFlag {
					stcRawScaleModT, err = tailScaleAfterRescaleToLevel(params, scaleModUint64(ctOut.Scale, T), ctOut.Level(), 0, T)
					if err != nil {
						panic(fmt.Errorf("compute post-StC BGV scale: %w", err))
					}
					stcScaleCorrection, err = tailInvModUint64(stcRawScaleModT, T)
					if err != nil {
						panic(fmt.Errorf("post-StC scale is not invertible modulo T: %w", err))
					}
					stcPlainTarget = scalarMulVectorMod(expectedFirst, stcScaleCorrection, T)
					if stcScaleCorrection != 1 {
						stcDiagForRun = scaleMatrixMod(stcDiagExt, stcScaleCorrection, T)
					}
				}
				ctCoeff, stcStats, err = HomomorphicSparseLinearTransformBSGS(params, eval, ctOut, stcDiagForRun)
				if err != nil {
					panic(fmt.Errorf("sparse SlotToCoeff failed: %w", err))
				}
			}
			stcWall = time.Since(st)
			ctCoeff.IsBatched = false
			targetScaledCoeffs := tailTauInvariantTargetCoeffs(stcPlainTarget, N, m, stcStep, T)
			extractPositions, err := tailExtractionPositions(N, m, stcStep)
			if err != nil {
				panic(err)
			}
			if ctCoeff.Level() > 0 {
				tailName := "post-StC"
				labelPrefix := "Post-StC"
				if skipStCForM1 {
					tailName = "post-polyeval"
					labelPrefix = "Post-polyeval"
				}
				stcBufferLevelReached := -1
				if *stcBufferLevelFlag > 0 {
					bufferLevel := *stcBufferLevelFlag
					if bufferLevel <= ctCoeff.Level() {
						if bufferLevel < ctCoeff.Level() {
							stBuffer := time.Now()
							if tailBufferRescaleWall, err = rescaleCiphertextToLevelWithTrace(eval, ctCoeff, bufferLevel, fmt.Sprintf("%s first normalization Q -> buffer L%d", labelPrefix, bufferLevel)); err != nil {
								panic(err)
							}
							ctCoeff.IsBatched = false
							tailBufferRescaleWall = time.Since(stBuffer)
						}
						stcBufferLevelReached = ctCoeff.Level()
						if *qprimeKSNoiseFlag {
							stProbe := time.Now()
							phaseBuffer, qBuffer, err := tailRLWEPhaseAtPositionsBig(params, ctCoeff, sk, extractPositions)
							if err != nil {
								panic(fmt.Errorf("probe %s buffer RLWE phase: %w", tailName, err))
							}
							targetBuffer, err := tailTargetRawPhasesFromPlainAtLevel(stcPlainTarget, scaleModUint64(ctCoeff.Scale, T), qBuffer, T)
							if err != nil {
								panic(fmt.Errorf("build %s buffer raw target: %w", tailName, err))
							}
							tailNoiseQBuffer = tailComputeNoiseStatsBig(phaseBuffer, targetBuffer, qBuffer, nil)
							qprimeNoiseProbeWall += time.Since(stProbe)
						}
					}
				}
				if ctCoeff.Level() > 0 {
					label := fmt.Sprintf("%s normalization Q -> Qprime", labelPrefix)
					if stcBufferLevelReached >= 0 && ctCoeff.Level() == stcBufferLevelReached {
						label = fmt.Sprintf("%s buffer -> Qprime", labelPrefix)
					}
					stFinal := time.Now()
					if tailFinalRescaleWall, err = rescaleCiphertextToLevelWithTrace(eval, ctCoeff, 0, label); err != nil {
						panic(err)
					}
					tailFinalRescaleWall = time.Since(stFinal)
				}
			}
			tailRescaleWall = tailBufferRescaleWall + tailFinalRescaleWall
			ctCoeff.IsBatched = false
			coeffDecoded, err := tailDecryptCoeffs(params, encoder, dec, ctCoeff)
			if err != nil {
				panic(fmt.Errorf("decrypt post-StC/no-StC coeffs: %w", err))
			}
			if badCoeff := firstMismatch(coeffDecoded, targetScaledCoeffs); badCoeff >= 0 {
				tailCoeffPlaintextOK = false
				tailCoeffBad = badCoeff
				tailCoeffGot = coeffDecoded[badCoeff]
				tailCoeffWant = targetScaledCoeffs[badCoeff]
			}
			runRes.CoeffOK = tailCoeffPlaintextOK
			targetQ, err = tailTargetRawPhasesSchemeD(tailExpectedPhase, schemeDScaleS, qPrime, T)
			if err != nil {
				panic(err)
			}
			if *qprimeKSNoiseFlag {
				stProbe := time.Now()
				skBeforeKS, err := tailSecretKeyCoeffsAtQPrime(params, sk)
				if err != nil {
					panic(fmt.Errorf("extract input secret at Qprime before final key switch: %w", err))
				}
				tailPhaseQBeforeKS, err = tailRLWEPhaseAtPositionsQPrime(params, ctCoeff, skBeforeKS, extractPositions)
				if err != nil {
					panic(fmt.Errorf("probe Qprime noise before final key switch: %w", err))
				}
				tailNoiseQBeforeKS = tailComputeNoiseStats(tailPhaseQBeforeKS, targetQ, qPrime, 0)
				qprimeNoiseProbeWall += time.Since(stProbe)
			}
			lweSecretSigned := fixedLWESecretSigned
			secInfo := fixedLWESecretInfo
			tailSecretInfo = secInfo
			st = time.Now()
			ctOutQ, digits, err := tailManualFinalKeySwitchNoSpecialQPrime(params, ctCoeff, sk, lweSecretSigned, *ksBaseLogFlag, *ksCenteredFlag, *finalKSSigmaFlag, finalKSRng)
			if err != nil {
				panic(fmt.Errorf("final Qprime-only key switch failed: %w", err))
			}
			tailDigits = digits
			finalKSWall = time.Since(st)
			ctOutQ.IsBatched = false
			if *qprimeKSNoiseFlag {
				stProbe := time.Now()
				skAfterKS := tailSignedSecretPaddedMod(lweSecretSigned, N, qPrime)
				tailPhaseQAfterKSRLWE, err = tailRLWEPhaseAtPositionsQPrime(params, ctOutQ, skAfterKS, extractPositions)
				if err != nil {
					panic(fmt.Errorf("probe Qprime noise after final key switch before SampleExtract: %w", err))
				}
				tailNoiseQAfterKSRLWE = tailComputeNoiseStats(tailPhaseQAfterKSRLWE, targetQ, qPrime, 0)
				tailNoiseQKSDelta = tailComputeNoiseStats(tailPhaseQAfterKSRLWE, tailPhaseQBeforeKS, qPrime, 0)
				qprimeNoiseProbeWall += time.Since(stProbe)
			}
			st = time.Now()
			lweQ, err := tailSampleExtractMany(params, ctOutQ, *lweNFlag, m, stcStep)
			if err != nil {
				panic(err)
			}
			sampleExtractWall = time.Since(st)
			stProbeExtractQ := time.Now()
			tailPhaseQAfterExtract = make([]uint64, m)
			skQp := tailSignedCoeffsToMod(lweSecretSigned, qPrime)
			for i := 0; i < m; i++ {
				tailPhaseQAfterExtract[i] = tailDecryptLWEPhase(lweQ[i], skQp, qPrime)
			}
			tailNoiseQAfterExtract = tailComputeNoiseStats(tailPhaseQAfterExtract, targetQ, qPrime, 0)
			if *qprimeKSNoiseFlag {
				tailNoiseQExtractDelta = tailComputeNoiseStats(tailPhaseQAfterExtract, tailPhaseQAfterKSRLWE, qPrime, 0)
			}
			qprimeNoiseProbeWall += time.Since(stProbeExtractQ)
			st = time.Now()
			lweOutT := make([]LWECiphertext, m)
			tailPhaseT = make([]uint64, m)
			tailMuOut = make([]uint64, m)
			skT := tailSignedCoeffsToMod(lweSecretSigned, T)
			alpha := T / *pFlag
			for i := 0; i < m; i++ {
				lweOutT[i] = tailLWEModSwitch(lweQ[i], qPrime, T)
				tailPhaseT[i] = tailDecryptLWEPhase(lweOutT[i], skT, T)
				tailMuOut[i] = decodePhaseToMessageModP(tailPhaseT[i], alpha, *pFlag, T)
			}
			qToTWall = time.Since(st)
			tailNoiseT = tailComputeNoiseStats(tailPhaseT, tailExpectedPhase, T, alpha/2)
			tailOK = tailNoiseT.OverBound == 0
			if len(expectedOutputMessages) > 0 {
				tailOK = firstMismatch(tailMuOut, expectedOutputMessages) < 0
			}
			runRes.DecodeOK = tailOK
		} else {
			runRes.CoeffOK = true
			runRes.DecodeOK = messageOK
		}

		onlineTime := time.Since(start)
		if qprimeNoiseProbeWall > 0 && onlineTime >= qprimeNoiseProbeWall {
			onlineTime -= qprimeNoiseProbeWall
		}
		if useLWEInput {
			onlineTime += step1Wall + step1NormalizeTime
		}
		step2EvalPower := tm.Breakdown.BuildBasis + tm.Breakdown.SquareXRHalf + tm.Breakdown.BuildGrouped + tm.Breakdown.ComputeXD
		step2BatchLT := tm.Breakdown.ParallelLT
		step2Total := stageBreakdownTotal(tm)
		step3Total := stcWall + tailRescaleWall + finalKSWall + sampleExtractWall + qToTWall
		_ = step2EvalPower
		_ = step2BatchLT
		_ = polyOnlineTime
		_ = finalLevelBeforeRescale
		_ = finalQBitsBeforeRescale
		_ = tailNoiseQBeforeKS
		_ = tailNoiseQAfterKSRLWE
		_ = tailNoiseQAfterExtract
		_ = tailNoiseQKSDelta
		_ = tailNoiseQExtractDelta
		_ = tailNoiseQBuffer
		_ = stcStats

		noiseDiffs := make([]int64, 0, m)
		if len(tailPhaseT) > 0 {
			noiseDiffs = appendTailNoiseDiffs(noiseDiffs, tailPhaseT, tailExpectedPhase, T)
		}
		qBeforeDiffs := make([]int64, 0, m)
		qAfterDiffs := make([]int64, 0, m)
		qKSDiffs := make([]int64, 0, m)
		qExtractDiffs := make([]int64, 0, m)
		if len(tailPhaseQBeforeKS) > 0 {
			qBeforeDiffs = appendTailNoiseDiffs(qBeforeDiffs, tailPhaseQBeforeKS, targetQ, qPrime)
		}
		if len(tailPhaseQAfterKSRLWE) > 0 {
			qAfterDiffs = appendTailNoiseDiffs(qAfterDiffs, tailPhaseQAfterKSRLWE, targetQ, qPrime)
		}
		if len(tailPhaseQAfterKSRLWE) > 0 && len(tailPhaseQBeforeKS) > 0 {
			qKSDiffs = appendTailNoiseDiffs(qKSDiffs, tailPhaseQAfterKSRLWE, tailPhaseQBeforeKS, qPrime)
		}
		if len(tailPhaseQAfterExtract) > 0 {
			qExtractDiffs = appendTailNoiseDiffs(qExtractDiffs, tailPhaseQAfterExtract, targetQ, qPrime)
		}
		runRes.NoiseMean = meanInt64(noiseDiffs)
		runRes.NoiseStd = stdDevInt64(noiseDiffs)
		runRes.NoiseMaxAbs = maxAbsInt64Slice(noiseDiffs)
		runRes.QBeforeDiffs = qBeforeDiffs
		runRes.QAfterDiffs = qAfterDiffs
		runRes.QKSDiffs = qKSDiffs
		runRes.QExtractDiffs = qExtractDiffs
		runRes.Online.Pack = step1Wall + step1NormalizeTime
		runRes.Online.Poly = tm
		runRes.Online.SlotToCoeff = stcWall + tailRescaleWall
		runRes.Online.KeySwitch = finalKSWall
		runRes.Online.ModSwitch = qToTWall
		runRes.Online.SampleExtract = sampleExtractWall
		runRes.Online.Total = onlineTime
		// PolyPlainOK/CoeffOK are Lattigo Decode/plaintext diagnostics. They can be false
		// when -m1-gamma-one-q deliberately chooses a dropped prime Q[1] that is not
		// 1 mod T; the definitive correctness test for functional bootstrapping is
		// the final Qprime->T decoded LWE phase/message check stored in DecodeOK.
		if *extractLWEFlag {
			runRes.Correct = runRes.DecodeOK
		} else {
			runRes.Correct = runRes.PolyPlainOK && messageOK
		}
		allCorrect = allCorrect && runRes.Correct
		allNoiseDiffs = append(allNoiseDiffs, noiseDiffs...)
		allQBeforeKSDiffs = append(allQBeforeKSDiffs, qBeforeDiffs...)
		allQAfterKSDiffs = append(allQAfterKSDiffs, qAfterDiffs...)
		allQKSDiffs = append(allQKSDiffs, qKSDiffs...)
		allQExtractedDiffs = append(allQExtractedDiffs, qExtractDiffs...)
		sumQPrimeProbeWall += qprimeNoiseProbeWall
		runResults = append(runResults, runRes)
		sumDynamic.FunctionTable += runRes.Dynamic.FunctionTable
		sumDynamic.LUTBuild += runRes.Dynamic.LUTBuild
		sumDynamic.LWECiphertexts += runRes.Dynamic.LWECiphertexts
		sumDynamic.PolyPrecompute += runRes.Dynamic.PolyPrecompute
		sumDynamic.M1GammaCalibration += runRes.Dynamic.M1GammaCalibration
		sumDynamic.Total += runRes.Dynamic.Total
		sumOnline.Pack += runRes.Online.Pack
		addPolyTiming(&sumOnline.Poly, runRes.Online.Poly)
		sumOnline.SlotToCoeff += runRes.Online.SlotToCoeff
		sumOnline.KeySwitch += runRes.Online.KeySwitch
		sumOnline.ModSwitch += runRes.Online.ModSwitch
		sumOnline.SampleExtract += runRes.Online.SampleExtract
		sumOnline.Total += runRes.Online.Total
		runRes.Wall = time.Since(runWallStart)
		sumRunWall += runRes.Wall
		lastTailSecretInfo = tailSecretInfo
		lastTailDigits = tailDigits
		lastTailNoiseT = tailNoiseT

		if detailed {
			fmt.Println()
			fmt.Println("========== Polynomial evaluation summary ==========")
			printBenchPolyTiming(tm)
			if *extractLWEFlag {
				fmt.Printf("poly wall before tail      : %v\n", polyOnlineTime)
			}
			fmt.Printf("online wall time           : %v\n", onlineTime)
			fmt.Printf("run wall time              : %v (dynamic setup + online + diagnostics before printing)\n", runRes.Wall)
			fmt.Printf("pre-final-rescale level    : L%d/%db\n", finalLevelBeforeRescale, finalQBitsBeforeRescale)
			fmt.Printf("operation counts           : %v\n", mulTraceKindCounts())
			fmt.Printf("correctness                : %v\n", ok)
			if len(expectedOutputMessages) > 0 {
				fmt.Printf("decoded message correctness: %v\n", messageOK)
				fmt.Printf("expected msg outputs       : %v\n", expectedOutputMessages[:minInt(len(expectedOutputMessages), 8)])
				fmt.Printf("decoded msg outputs        : %v\n", decodedOutputMessages[:minInt(len(decodedOutputMessages), 8)])
			}
			fmt.Printf("expected first outputs     : %v\n", expectedFirst[:minInt(len(expectedFirst), 8)])
			if m1GammaAbsorbThisRun {
				fmt.Printf("logical first outputs      : %v  (after undoing m=1 gamma pre-scale)\n", logicalExpectedFirst[:minInt(len(logicalExpectedFirst), 8)])
			}
			fmt.Printf("decoded first outputs      : %v\n", gotSlots[:minInt(len(gotSlots), 8)])
			if *extractLWEFlag {
				fmt.Println()
				fmt.Println("========== StC / extraction / Qprime->T summary ==========")
				fmt.Printf("StC/scale-fix time / ops   : %v; CMult=%d, rotations=%d, baby=%d, giant=%d, additions=%d\n", stcWall, stcStats.PlainCipherMults, stcStats.Rotations, stcStats.BabyRotations, stcStats.GiantRotations, stcStats.Additions)
				if skipStCForM1 && *schemeDFlag {
					status := "skipped"
					if stcResidualScaleModT != 1 && *m1ScaleFixFlag {
						status = "applied"
					} else if stcResidualScaleModT != 1 && !*m1ScaleFixFlag {
						status = "needed but disabled"
					}
					fmt.Printf("m=1 no-StC BGV scale gamma : raw=%d mod T, polynomial-pre-scale=%d, residual=%d, residual^{-1}=%d; correction %s\n", stcRawScaleModT, stcPreAbsorbScaleModT, stcResidualScaleModT, stcScaleCorrection, status)
				}
				fmt.Printf("post-StC total rescale time: %v\n", tailRescaleWall)
				if !tailCoeffPlaintextOK {
					fmt.Printf("coefficient plaintext check: false; first coeff mismatch %d, got=%d, want=%d\n", tailCoeffBad, tailCoeffGot, tailCoeffWant)
				} else {
					fmt.Printf("coefficient plaintext check: true\n")
				}
				fmt.Printf("final key-switch           : %v; digits=%d, base=2^%d, centered=%v, sigma=%.2f, no special P\n", finalKSWall, tailDigits, *ksBaseLogFlag, *ksCenteredFlag, *finalKSSigmaFlag)
				fmt.Printf("sample extract time        : %v\n", sampleExtractWall)
				if qprimeNoiseProbeWall > 0 {
					fmt.Printf("Qprime noise probe time    : %v (diagnostic only; excluded from online total)\n", qprimeNoiseProbeWall)
				}
				fmt.Printf("Qprime -> T time           : %v\n", qToTWall)
				if len(qBeforeDiffs) > 0 {
					fmt.Printf("noise at Qprime before KS  : max|e|=%d, RMS=%.3f, mean|e|=%.3f, std=%.3f, samples=%d\n", maxAbsInt64Slice(qBeforeDiffs), rmsInt64(qBeforeDiffs), meanAbsInt64(qBeforeDiffs), stdDevInt64(qBeforeDiffs), len(qBeforeDiffs))
				}
				if len(qAfterDiffs) > 0 {
					fmt.Printf("noise at Qprime after KS   : max|e|=%d, RMS=%.3f, mean|e|=%.3f, std=%.3f, samples=%d  (before Qprime->T)\n", maxAbsInt64Slice(qAfterDiffs), rmsInt64(qAfterDiffs), meanAbsInt64(qAfterDiffs), stdDevInt64(qAfterDiffs), len(qAfterDiffs))
				}
				if len(qKSDiffs) > 0 {
					fmt.Printf("KS-added noise at Qprime   : max|Δe|=%d, RMS=%.3f, mean|Δe|=%.3f, std=%.3f, samples=%d\n", maxAbsInt64Slice(qKSDiffs), rmsInt64(qKSDiffs), meanAbsInt64(qKSDiffs), stdDevInt64(qKSDiffs), len(qKSDiffs))
				}
				if len(qExtractDiffs) > 0 {
					maxQ := maxAbsInt64Slice(qExtractDiffs)
					proj := projectedTNoiseFromQPrime(maxQ, qPrime, T)
					reqQ := minQPrimeForProjectedTNoise(maxQ, T, (T / *pFlag)/2)
					fmt.Printf("noise at Qprime extracted  : max|e|=%d, RMS=%.3f, mean|e|=%.3f, std=%.3f, samples=%d  (immediately before Qprime->T)\n", maxQ, rmsInt64(qExtractDiffs), meanAbsInt64(qExtractDiffs), stdDevInt64(qExtractDiffs), len(qExtractDiffs))
					if reqQ.Sign() > 0 {
						fmt.Printf("Qprime sizing estimate     : projected T max≈%.3f; min Q' for projected max < radius ≈ %s (%d bits), +2/+4 margin ≈ %d/%d bits\n", proj, reqQ.String(), reqQ.BitLen(), reqQ.BitLen()+2, reqQ.BitLen()+4)
					}
				}
				fmt.Printf("noise after Qprime->T      : max|e|=%d at item %d, RMS=%.3f, mean|e|=%.3f, std=%.3f, decoding radius=%d, over-radius=%d/%d\n", tailNoiseT.MaxAbs, tailNoiseT.MaxIndex, tailNoiseT.RMS, tailNoiseT.MeanAbs, tailNoiseT.StdDev, (T / *pFlag)/2, tailNoiseT.OverBound, tailNoiseT.Count)
				fmt.Printf("final phase[0:%d]          : %v\n", minInt(len(tailPhaseT), 8), tailPhaseT[:minInt(len(tailPhaseT), 8)])
				fmt.Printf("target phase[0:%d]         : %v\n", minInt(len(tailExpectedPhase), 8), tailExpectedPhase[:minInt(len(tailExpectedPhase), 8)])
				fmt.Printf("final decoded mu[0:%d]     : %v\n", minInt(len(tailMuOut), 8), tailMuOut[:minInt(len(tailMuOut), 8)])
				fmt.Printf("final LWE correctness      : %v\n", tailOK)
				if *outputNoiseTableFlag || !tailOK {
					printTailOutputNoiseTable(tailPhaseT, tailExpectedPhase, tailMuOut, expectedOutputMessages, T, (T / *pFlag)/2, *outputNoiseTableLimitFlag)
				}
			}
			if (polyNoiseTracer != nil && polyNoiseTracer.Enabled) || mulTraceProbeTime() > 0 {
				fmt.Printf("noise trace overhead       : %v checkpoint probes + %v operation probes = %v (diagnostic only; excluded from HE operation total)\n", polyNoiseProbeTime(), mulTraceProbeTime(), polyNoiseProbeTime()+mulTraceProbeTime())
			}
			polyNoiseTracer.Print()
			printMulTraceSummary()
		}

		runNoiseStdText := formatSigmaForSummary(runRes.NoiseStd, len(noiseDiffs))
		fmt.Printf("Run %d/%d: func-seed=%d, input-seed=%d, phase-error-seed=%d, lwe-a-seed=%d, correct=%v, setup=%v (lwe=%v, func=%v, lut=%v, pt=%v, gamma=%v), online=%v, wall=%v, step1=%v, step2=%v, step3=%v, noise mean=%.4f, noise std=%s, max|.|=%d\n", runNo, *runsFlag, runFuncSeed, runInputSeed, runPhaseErrorSeed, runLWEASeed, runRes.Correct, runRes.Dynamic.Total, runRes.Dynamic.LWECiphertexts, runRes.Dynamic.FunctionTable, runRes.Dynamic.LUTBuild, runRes.Dynamic.PolyPrecompute, runRes.Dynamic.M1GammaCalibration, onlineTime, runRes.Wall, step1Wall+step1NormalizeTime, step2Total, step3Total, runRes.NoiseMean, runNoiseStdText, runRes.NoiseMaxAbs)
		if *qprimeKSNoiseFlag && len(qExtractDiffs) > 0 && !detailed {
			maxExtractQ := maxAbsInt64Slice(qExtractDiffs)
			proj := projectedTNoiseFromQPrime(maxExtractQ, qPrime, T)
			reqQ := minQPrimeForProjectedTNoise(maxExtractQ, T, (T / *pFlag)/2)
			reqText := "n/a"
			if reqQ.Sign() > 0 {
				reqText = fmt.Sprintf("%d bits (+2=%d, +4=%d)", reqQ.BitLen(), reqQ.BitLen()+2, reqQ.BitLen()+4)
			}
			fmt.Printf("  Qprime noise: beforeKS max=%d, afterKS max=%d, KSΔ max=%d, extracted/pre-Q->T max=%d, projected T max≈%.3f, required Q'≈%s\n", maxAbsInt64Slice(qBeforeDiffs), maxAbsInt64Slice(qAfterDiffs), maxAbsInt64Slice(qKSDiffs), maxExtractQ, proj, reqText)
		}

		ctIn = nil
		ctOut = nil
		pre = nil
		inputLWECts = nil
		slots = nil
		gotSlots = nil
		expectedSlots = nil
		expectedFirst = nil
		polyBuild.FullCoeffs = nil
		polyBuild.CoeffsLower = nil
		polyBuild.LeadCoeffs = nil
		polyBuild.FuncTable = nil
		maybeCollectRunGarbage(runIdx, *runsFlag, *gcEveryFlag, *freeOSMemoryFlag, *memProgressFlag)
	}

	fmt.Println()
	fmt.Println("========== Aggregated multi-run summary ==========")
	fmt.Printf("runs                       : %d\n", *runsFlag)
	fmt.Printf("all runs correct           : %v\n", allCorrect)
	fmt.Printf("average dynamic setup      : %v\n", benchAvgDuration(sumDynamic.Total, *runsFlag))
	fmt.Printf("average run wall time      : %v\n", benchAvgDuration(sumRunWall, *runsFlag))
	fmt.Printf("  - fresh LWE ciphertexts  : %v\n", benchAvgDuration(sumDynamic.LWECiphertexts, *runsFlag))
	fmt.Printf("  - function table         : %v\n", benchAvgDuration(sumDynamic.FunctionTable, *runsFlag))
	fmt.Printf("  - LUT/coeff build        : %v\n", benchAvgDuration(sumDynamic.LUTBuild, *runsFlag))
	fmt.Printf("  - poly plaintext prep    : %v\n", benchAvgDuration(sumDynamic.PolyPrecompute, *runsFlag))
	if sumDynamic.M1GammaCalibration > 0 {
		fmt.Printf("  - m=1 gamma calibration  : %v\n", benchAvgDuration(sumDynamic.M1GammaCalibration, *runsFlag))
	}
	fmt.Printf("average online total       : %v\n", benchAvgDuration(sumOnline.Total, *runsFlag))
	fmt.Printf("  - LWE->RLWE Step1        : %v\n", benchAvgDuration(sumOnline.Pack, *runsFlag))
	fmt.Printf("  - poly eval total        : %v\n", benchAvgDuration(sumOnline.Poly.Total, *runsFlag))
	fmt.Printf("    · build basis / P      : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.BuildBasis, *runsFlag))
	fmt.Printf("    · square x^(r/2)       : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.SquareXRHalf, *runsFlag))
	fmt.Printf("    · build grouped powers : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.BuildGrouped, *runsFlag))
	fmt.Printf("    · ParallelLT           : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.ParallelLT, *runsFlag))
	fmt.Printf("      · LT decompose       : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTDecompose, *runsFlag))
	fmt.Printf("      · baby rotations     : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTBabyRotations, *runsFlag))
	fmt.Printf("      · giant rotations    : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTGiantRotations, *runsFlag))
	fmt.Printf("      · pt-ct multiplies   : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTPlaintextCipherMul, *runsFlag))
	fmt.Printf("      · first-stage other  : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTFirstStageOther, *runsFlag))
	fmt.Printf("      · post-process       : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTPostProcess, *runsFlag))
	fmt.Printf("      · post-LT rescale    : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LTPostRescale, *runsFlag))
	fmt.Printf("    · pointwise multiply   : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.PointwiseMul, *runsFlag))
	fmt.Printf("    · rotate-and-sum       : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.RotateAndSum, *runsFlag))
	fmt.Printf("    · compute x^d          : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.ComputeXD, *runsFlag))
	fmt.Printf("    · leading term         : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.LeadingTerm, *runsFlag))
	fmt.Printf("    · final add            : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.FinalAdd, *runsFlag))
	fmt.Printf("    · final rescale        : %v\n", benchAvgDuration(sumOnline.Poly.Breakdown.FinalRescale, *runsFlag))
	fmt.Printf("  - StC/rescale            : %v\n", benchAvgDuration(sumOnline.SlotToCoeff, *runsFlag))
	fmt.Printf("  - final key switch       : %v\n", benchAvgDuration(sumOnline.KeySwitch, *runsFlag))
	fmt.Printf("  - Qprime -> T            : %v\n", benchAvgDuration(sumOnline.ModSwitch, *runsFlag))
	fmt.Printf("  - sample extraction      : %v\n", benchAvgDuration(sumOnline.SampleExtract, *runsFlag))
	fmt.Printf("output noise samples       : %d\n", len(allNoiseDiffs))
	fmt.Printf("output noise mean          : %.4f\n", meanInt64(allNoiseDiffs))
	if len(allNoiseDiffs) < 2 {
		fmt.Printf("output noise std dev       : n/a (need at least 2 samples; use RMS/max|e| for a single m=1 run)\n")
	} else {
		fmt.Printf("output noise std dev       : %.4f\n", stdDevInt64(allNoiseDiffs))
	}
	fmt.Printf("output noise max |e|       : %d\n", maxAbsInt64Slice(allNoiseDiffs))
	if len(allQExtractedDiffs) > 0 {
		fmt.Println("Qprime-domain noise summary:")
		if sumQPrimeProbeWall > 0 {
			fmt.Printf("  - probe overhead avg     : %v (diagnostic only; excluded from online total)\n", benchAvgDuration(sumQPrimeProbeWall, *runsFlag))
		}
		if len(allQBeforeKSDiffs) > 0 {
			fmt.Printf("  - %s\n", formatQPrimeNoiseDiffSummary("before final KS", allQBeforeKSDiffs))
		}
		if len(allQAfterKSDiffs) > 0 {
			fmt.Printf("  - %s\n", formatQPrimeNoiseDiffSummary("after final KS", allQAfterKSDiffs))
		}
		if len(allQKSDiffs) > 0 {
			fmt.Printf("  - %s\n", formatQPrimeNoiseDiffSummary("KS-added", allQKSDiffs))
		}
		fmt.Printf("  - %s\n", formatQPrimeNoiseDiffSummary("extracted / before Qprime->T", allQExtractedDiffs))
		radius := (T / *pFlag) / 2
		maxQ := maxAbsInt64Slice(allQExtractedDiffs)
		proj := projectedTNoiseFromQPrime(maxQ, qPrime, T)
		reqQ := minQPrimeForProjectedTNoise(maxQ, T, radius)
		if reqQ.Sign() > 0 {
			fmt.Printf("Qprime sizing heuristic    : current Q'=%d (%d bits), T=%d, radius=%d, max extracted |e_Q|=%d, projected max after Q'->T≈%.3f; min Q' for projected max < radius ≈ %s (%d bits), with +2/+4/+8-bit margin ≈ %d/%d/%d bits\n", qPrime, bits.Len64(qPrime), T, radius, maxQ, proj, reqQ.String(), reqQ.BitLen(), reqQ.BitLen()+2, reqQ.BitLen()+4, reqQ.BitLen()+8)
		}
	}
	fmt.Printf("total wall time            : %v\n", time.Since(programWallStart))
	fmt.Println("==============================================")

	if *extractLWEFlag {
		bootstrapKeyBytes := evalKeySizeBytes
		if useLWEInput && step1Plan.Blocks > 0 {
			bootstrapKeyBytes += int64(step1Plan.Blocks) * int64(bfv.NewCiphertext(params, 1, params.MaxLevel()).BinarySize())
		}
		if lastTailDigits > 0 {
			bootstrapKeyBytes += int64(lastTailDigits) * int64(2*N*8)
		}
		packingLevels := 0
		if useLWEInput && *lweStep1RescaleLevelsFlag > 0 {
			packingLevels = *lweStep1RescaleLevelsFlag
		}
		bufferLevels := 0
		if *stcBufferLevelFlag > 0 {
			bufferLevels = *stcBufferLevelFlag
		}
		sigmaRes := stdDevInt64(allNoiseDiffs)
		avgStep2Total := benchAvgDuration(sumOnline.Poly.Total, *runsFlag)
		avgStep3Total := benchAvgDuration(sumOnline.SlotToCoeff+sumOnline.KeySwitch+sumOnline.ModSwitch+sumOnline.SampleExtract, *runsFlag)
		printPaperStyleFBSummary(N, m, degree, *lweNFlag, T, *pFlag, logQBits, logPBits, packingLevels, bufferLevels, !skipStCForM1, params, bootstrapKeyBytes, benchAvgDuration(sumOnline.Pack, *runsFlag), benchAvgDuration(sumOnline.Poly.Breakdown.BuildBasis+sumOnline.Poly.Breakdown.SquareXRHalf+sumOnline.Poly.Breakdown.BuildGrouped+sumOnline.Poly.Breakdown.ComputeXD, *runsFlag), benchAvgDuration(sumOnline.Poly.Breakdown.ParallelLT, *runsFlag), avgStep2Total, avgStep3Total, benchAvgDuration(sumOnline.Total, *runsFlag), benchAvgDuration(sumOnline.Total, *runsFlag), sigmaRes, len(allNoiseDiffs), lastTailSecretInfo)
		printFailureProbabilitySummary(T, *pFlag, *lweNFlag, lastTailSecretInfo, sigmaRes, lastTailNoiseT)
	}

	if !allCorrect {
		os.Exit(2)
	}
}

// ================= Scheme-D + sparse StC/extraction tail helpers =================

func firstMismatch(a, b []uint64) int {
	n := len(a)
	if len(b) < n {
		n = len(b)
	}
	for i := 0; i < n; i++ {
		if a[i] != b[i] {
			return i
		}
	}
	if len(a) != len(b) {
		return n
	}
	return -1
}

func scalarMulVectorMod(v []uint64, scalar, mod uint64) []uint64 {
	out := make([]uint64, len(v))
	for i := range v {
		out[i] = tailMulMod(v[i]%mod, scalar%mod, mod)
	}
	return out
}

func tailSchemeDScale(qPrime, t uint64) (targetScale, S uint64, err error) {
	c := qPrime % t
	if c == 0 {
		return 0, 0, fmt.Errorf("Qprime divisible by T")
	}
	targetScale = (qPrime + t - 1) / t
	S = t - c
	if S == 0 || tailGCDUint64(S, t) != 1 {
		return 0, 0, fmt.Errorf("invalid Scheme-D S=%d modulo T=%d", S, t)
	}
	return targetScale, S, nil
}

// Legacy helper for the old scaled-input variant. The current Scheme-D tail does not
// use it: the polynomial input remains x=Delta*m+e, and the LUT output is scaled
// directly by S, i.e. F(x)=S*P(x) on the valid noisy intervals.
func scalePolynomialCoefficientsForSchemeD(coeffs []uint64, S, mod uint64) ([]uint64, error) {
	invS, err := tailInvModUint64(S%mod, mod)
	if err != nil {
		return nil, err
	}
	out := make([]uint64, len(coeffs))
	powInv := uint64(1)
	for j, a := range coeffs {
		_ = j
		out[j] = tailMulMod(tailMulMod(a%mod, S%mod, mod), powInv, mod)
		powInv = tailMulMod(powInv, invS, mod)
	}
	return out, nil
}

func scaleMatrixMod(mat [][]uint64, scalar, mod uint64) [][]uint64 {
	out := make([][]uint64, len(mat))
	for i := range mat {
		out[i] = scalarMulVectorMod(mat[i], scalar, mod)
	}
	return out
}

func tailScaleAfterRescaleToLevel(params bfv.Parameters, inputScale uint64, fromLevel, targetLevel int, modT uint64) (uint64, error) {
	if targetLevel < 0 || targetLevel > fromLevel {
		return 0, fmt.Errorf("invalid target level L%d from L%d", targetLevel, fromLevel)
	}
	scale := inputScale % modT
	for level := fromLevel; level > targetLevel; level-- {
		qi := params.Q()[level] % modT
		invQi, err := tailInvModUint64(qi, modT)
		if err != nil {
			return 0, fmt.Errorf("Q[%d]=%d is not invertible modulo T=%d", level, params.Q()[level], modT)
		}
		scale = tailMulMod(scale, invQi, modT)
	}
	return scale, nil
}

func tailTauInvariantTargetCoeffs(x []uint64, N, m, tau int, q uint64) []uint64 {
	coeffs := make([]uint64, N)
	if len(x) == 0 {
		return coeffs
	}
	coeffs[0] = x[0] % q
	for j := 1; j < m && j < len(x); j++ {
		coeffs[j*tau] = x[j] % q
		if x[j]%q == 0 {
			coeffs[(2*m-j)*tau] = 0
		} else {
			coeffs[(2*m-j)*tau] = q - (x[j] % q)
		}
	}
	return coeffs
}

func tailDecryptCoeffs(params bfv.Parameters, encoder *bfv.Encoder, decryptor *rlwe.Decryptor, ct *rlwe.Ciphertext) ([]uint64, error) {
	pt := decryptor.DecryptNew(ct)
	pt.IsBatched = false
	out := make([]uint64, params.N())
	if err := encoder.Decode(pt, out); err != nil {
		return nil, err
	}
	for i := range out {
		out[i] %= params.PlaintextModulus()
	}
	return out, nil
}

func tailExtractionPositions(N, m, tau int) ([]int, error) {
	if m <= 0 {
		return nil, fmt.Errorf("invalid m=%d", m)
	}
	if tau <= 0 {
		return nil, fmt.Errorf("invalid extraction stride tau=%d", tau)
	}
	out := make([]int, m)
	for i := 0; i < m; i++ {
		pos := i * tau
		if pos < 0 || pos >= N {
			return nil, fmt.Errorf("extraction position %d*tau=%d outside [0,%d)", i, pos, N)
		}
		out[i] = pos
	}
	return out, nil
}

func tailSecretKeyCoeffsAtQPrime(params bfv.Parameters, sk *rlwe.SecretKey) ([]uint64, error) {
	ringQ := params.RingQ().AtLevel(0)
	skPoly := tailPolyToCoeffNormal(ringQ, sk.Value.Q, true, true)
	out := make([]uint64, params.N())
	copy(out, skPoly.Coeffs[0])
	Qp := params.Q()[0]
	for i := range out {
		out[i] %= Qp
	}
	return out, nil
}

func tailSignedSecretPaddedMod(secret []int64, N int, mod uint64) []uint64 {
	out := make([]uint64, N)
	for i, c := range secret {
		if i >= N {
			break
		}
		out[i] = tailSignedToMod(c, mod)
	}
	return out
}

func tailRLWEPhaseAtPositionsQPrime(params bfv.Parameters, ct *rlwe.Ciphertext, secretMod []uint64, positions []int) ([]uint64, error) {
	if ct.Level() != 0 {
		return nil, fmt.Errorf("expected level 0/Qprime ciphertext, got level %d", ct.Level())
	}
	N := params.N()
	Qp := params.Q()[0]
	ringQ := params.RingQ().AtLevel(0)
	c0 := tailPolyToCoeffNormal(ringQ, ct.Value[0], ct.IsNTT, ct.IsMontgomery)
	c1 := tailPolyToCoeffNormal(ringQ, ct.Value[1], ct.IsNTT, ct.IsMontgomery)
	skPoly := ringQ.NewPoly()
	for i := 0; i < N && i < len(secretMod); i++ {
		skPoly.Coeffs[0][i] = secretMod[i] % Qp
	}
	phasePoly := tailMulPolyCoeffNormal(ringQ, c1, skPoly)
	ringQ.Add(c0, phasePoly, phasePoly)
	out := make([]uint64, len(positions))
	for i, pos := range positions {
		if pos < 0 || pos >= N {
			return nil, fmt.Errorf("position %d outside [0,%d)", pos, N)
		}
		out[i] = phasePoly.Coeffs[0][pos] % Qp
	}
	return out, nil
}

func tailSampleExtractMany(params bfv.Parameters, ct *rlwe.Ciphertext, lweN, m, tau int) ([]LWECiphertext, error) {
	if ct.Level() != 0 {
		return nil, fmt.Errorf("expected level 0 before SampleExtract, got %d", ct.Level())
	}
	ringQ := params.RingQ().AtLevel(0)
	p0 := tailPolyToCoeffNormal(ringQ, ct.Value[0], ct.IsNTT, ct.IsMontgomery)
	p1 := tailPolyToCoeffNormal(ringQ, ct.Value[1], ct.IsNTT, ct.IsMontgomery)
	c0 := p0.Coeffs[0]
	c1 := p1.Coeffs[0]
	Qp := params.Q()[0]
	N := params.N()
	if lweN > N {
		return nil, fmt.Errorf("lweN=%d exceeds ring degree N=%d", lweN, N)
	}
	out := make([]LWECiphertext, m)
	for item := 0; item < m; item++ {
		k := item * tau
		if k >= N {
			return nil, fmt.Errorf("extraction index k=%d exceeds N=%d", k, N)
		}
		a := make([]uint64, lweN)
		for j := 0; j < lweN; j++ {
			var coeff uint64
			if j <= k {
				coeff = c1[k-j]
			} else {
				coeff = c1[N+k-j]
				if coeff != 0 {
					coeff = Qp - coeff
				}
			}
			// LWE convention is b - <a,s>; RLWE phase is c0 + c1*s.
			// Therefore the extracted LWE vector uses a_j = -coeff.
			if coeff == 0 {
				a[j] = 0
			} else {
				a[j] = Qp - coeff
			}
		}
		out[item] = LWECiphertext{A: a, B: c0[k]}
	}
	return out, nil
}

func tailLWEModSwitch(ct LWECiphertext, qFrom, qTo uint64) LWECiphertext {
	out := LWECiphertext{A: make([]uint64, len(ct.A)), B: tailRoundedScaleCentered(ct.B, qFrom, qTo)}
	for i := range ct.A {
		out.A[i] = tailRoundedScaleCentered(ct.A[i], qFrom, qTo)
	}
	return out
}

func tailDecryptLWEPhase(ct LWECiphertext, secret []uint64, mod uint64) uint64 {
	acc := ct.B % mod
	for i, ai := range ct.A {
		prod := tailMulMod(ai%mod, secret[i]%mod, mod)
		acc = tailSubMod(acc, prod, mod)
	}
	return acc
}

func tailTargetRawPhasesSchemeD(y []uint64, scaleS, qPrime, t uint64) ([]uint64, error) {
	invT, err := tailInvModUint64(t%qPrime, qPrime)
	if err != nil {
		return nil, err
	}
	out := make([]uint64, len(y))
	for i, yi := range y {
		pt := tailMulMod(scaleS%t, yi%t, t)
		out[i] = tailMulMod(pt, invT, qPrime)
	}
	return out, nil
}

type TailNoiseStats struct {
	Count     int
	NonZero   int
	OverBound int
	MaxAbs    int64
	MaxIndex  int
	Mean      float64
	MeanAbs   float64
	RMS       float64
	StdDev    float64
}

type TailBigNoiseStats struct {
	Count      int
	NonZero    int
	OverBound  int
	MaxAbs     string
	MaxAbsBits int
	MaxIndex   int
	MeanAbs    float64
	RMS        float64
}

func tailComputeNoiseStatsBig(actual, target []*big.Int, mod *big.Int, bound *big.Int) TailBigNoiseStats {
	st := TailBigNoiseStats{Count: len(actual), MaxIndex: -1, MaxAbs: "0"}
	if mod == nil || mod.Sign() <= 0 {
		return st
	}
	maxAbs := big.NewInt(0)
	var sumAbs, sumSq float64
	for i := range actual {
		if i >= len(target) || actual[i] == nil || target[i] == nil {
			continue
		}
		d := centeredModBig(new(big.Int).Sub(actual[i], target[i]), mod)
		abs := new(big.Int).Abs(d)
		if abs.Sign() != 0 {
			st.NonZero++
		}
		if bound != nil && bound.Sign() > 0 && abs.Cmp(bound) >= 0 {
			st.OverBound++
		}
		if st.MaxIndex < 0 || abs.Cmp(maxAbs) > 0 {
			maxAbs.Set(abs)
			st.MaxIndex = i
		}
		absFloat, _ := new(big.Float).SetInt(abs).Float64()
		sumAbs += absFloat
		sumSq += absFloat * absFloat
	}
	if st.Count > 0 {
		st.MeanAbs = sumAbs / float64(st.Count)
		st.RMS = math.Sqrt(sumSq / float64(st.Count))
	}
	st.MaxAbs = maxAbs.String()
	if maxAbs.Sign() > 0 {
		st.MaxAbsBits = maxAbs.BitLen() - 1
	}
	return st
}

func tailTargetRawPhasesFromPlainAtLevel(plain []uint64, scaleModT uint64, qLevel *big.Int, t uint64) ([]*big.Int, error) {
	if qLevel == nil || qLevel.Sign() <= 0 {
		return nil, errors.New("invalid non-positive Q level modulus")
	}
	tBig := new(big.Int).SetUint64(t)
	invT := new(big.Int).ModInverse(tBig, qLevel)
	if invT == nil {
		return nil, fmt.Errorf("T=%d is not invertible modulo Q_level=%s", t, qLevel.String())
	}
	out := make([]*big.Int, len(plain))
	for i, v := range plain {
		coeffT := tailMulMod(scaleModT%t, v%t, t)
		raw := new(big.Int).Mul(new(big.Int).SetUint64(coeffT), invT)
		raw.Mod(raw, qLevel)
		out[i] = centeredModBig(raw, qLevel)
	}
	return out, nil
}

func tailRLWEPhaseAtPositionsBig(params bfv.Parameters, ct *rlwe.Ciphertext, sk *rlwe.SecretKey, positions []int) ([]*big.Int, *big.Int, error) {
	if ct == nil || sk == nil {
		return nil, nil, errors.New("nil ciphertext or secret key")
	}
	level := ct.Level()
	if level < 0 || level > params.MaxLevel() {
		return nil, nil, fmt.Errorf("invalid ciphertext level %d", level)
	}
	N := params.N()
	ringQ := params.RingQ().AtLevel(level)
	c0 := tailPolyToCoeffNormal(ringQ, ct.Value[0], ct.IsNTT, ct.IsMontgomery)
	c1 := tailPolyToCoeffNormal(ringQ, ct.Value[1], ct.IsNTT, ct.IsMontgomery)
	skPoly := tailPolyToCoeffNormal(ringQ, sk.Value.Q, true, true)
	phasePoly := tailMulPolyCoeffNormal(ringQ, c1, skPoly)
	ringQ.Add(c0, phasePoly, phasePoly)
	phaseAll := polyToBigintCentered(ringQ, phasePoly, false, false)
	out := make([]*big.Int, len(positions))
	for i, pos := range positions {
		if pos < 0 || pos >= N {
			return nil, nil, fmt.Errorf("position %d outside [0,%d)", pos, N)
		}
		out[i] = new(big.Int).Set(phaseAll[pos])
	}
	return out, ringQ.Modulus(), nil
}

func tailComputeNoiseStats(actual, target []uint64, mod uint64, bound uint64) TailNoiseStats {
	st := TailNoiseStats{Count: len(actual), MaxIndex: -1}
	var sumSigned, sumAbs, sumSq float64
	for i := range actual {
		d := centeredDiff(actual[i], target[i], mod)
		ad := d
		if ad < 0 {
			ad = -ad
		}
		if ad != 0 {
			st.NonZero++
		}
		if bound > 0 && uint64(ad) >= bound {
			st.OverBound++
		}
		if ad > st.MaxAbs || st.MaxIndex < 0 {
			st.MaxAbs = ad
			st.MaxIndex = i
		}
		df := float64(d)
		af := float64(ad)
		sumSigned += df
		sumAbs += af
		sumSq += df * df
	}
	if st.Count > 0 {
		invN := 1.0 / float64(st.Count)
		st.Mean = sumSigned * invN
		st.MeanAbs = sumAbs * invN
		st.RMS = math.Sqrt(sumSq * invN)
		variance := sumSq*invN - st.Mean*st.Mean
		if variance < 0 && variance > -1e-9 {
			variance = 0
		}
		if variance > 0 {
			st.StdDev = math.Sqrt(variance)
		}
	}
	return st
}

func printTailOutputNoiseTable(actual, target, decoded, expected []uint64, mod uint64, radius uint64, maxRows int) {
	if len(actual) == 0 || len(target) == 0 || mod == 0 {
		return
	}
	n := len(actual)
	if len(target) < n {
		n = len(target)
	}
	if maxRows <= 0 || maxRows > n {
		maxRows = n
	}
	fmt.Println()
	fmt.Println("========== Output LWE noise table ==========")
	fmt.Printf("showing %d/%d rows; radius=%d\n", maxRows, n, radius)
	fmt.Println("i | phase_T | target_T | noise | |noise| | decoded | expected | ok")
	fmt.Println("--+---------+----------+-------+---------+---------+----------+----")
	for i := 0; i < maxRows; i++ {
		d := centeredDiff(actual[i], target[i], mod)
		ad := d
		if ad < 0 {
			ad = -ad
		}
		decStr := "-"
		if i < len(decoded) {
			decStr = fmt.Sprintf("%d", decoded[i])
		}
		expStr := "-"
		if i < len(expected) {
			expStr = fmt.Sprintf("%d", expected[i])
		}
		ok := radius == 0 || uint64(ad) < radius
		if i < len(decoded) && i < len(expected) {
			ok = ok && decoded[i] == expected[i]
		}
		fmt.Printf("%d | %d | %d | %d | %d | %s | %s | %v\n", i, actual[i], target[i], d, ad, decStr, expStr, ok)
	}
	if maxRows < n {
		fmt.Printf("... %d more rows omitted; increase -output-noise-table-limit to show more.\n", n-maxRows)
	}
	fmt.Println("===========================================")
}

type TailSecretInfo struct {
	Name string
	H    int
	Pos  int
	Neg  int
}

func tailSampleLWESecret(n int, dist string, h int, rng *rand.Rand) ([]int64, TailSecretInfo, error) {
	d := strings.ToLower(strings.TrimSpace(dist))
	switch d {
	case "sparseternary", "balanced-sparseternary", "balanced":
		if h <= 0 {
			return nil, TailSecretInfo{}, fmt.Errorf("-lwe-secret sparseternary requires -lwe-h > 0")
		}
		if h > n {
			return nil, TailSecretInfo{}, fmt.Errorf("-lwe-h=%d exceeds n=%d", h, n)
		}
		if h%2 != 0 {
			return nil, TailSecretInfo{}, fmt.Errorf("sparseternary requires even -lwe-h, got %d", h)
		}
		out := make([]int64, n)
		perm := rng.Perm(n)
		pos := h / 2
		neg := h / 2
		for i := 0; i < pos; i++ {
			out[perm[i]] = 1
		}
		for i := 0; i < neg; i++ {
			out[perm[pos+i]] = -1
		}
		return out, TailSecretInfo{Name: fmt.Sprintf("SparseTernary(+1=%d,-1=%d,n=%d)", pos, neg, n), H: h, Pos: pos, Neg: neg}, nil
	case "fixedweight", "fixed-weight":
		if h <= 0 || h > n {
			return nil, TailSecretInfo{}, fmt.Errorf("invalid fixed-weight h=%d for n=%d", h, n)
		}
		out := make([]int64, n)
		perm := rng.Perm(n)
		pos, neg := 0, 0
		for i := 0; i < h; i++ {
			if rng.Intn(2) == 0 {
				out[perm[i]] = -1
				neg++
			} else {
				out[perm[i]] = 1
				pos++
			}
		}
		return out, TailSecretInfo{Name: fmt.Sprintf("FixedWeightRandomSigns(h=%d,n=%d)", h, n), H: h, Pos: pos, Neg: neg}, nil
	case "ternary", "uniformternary", "uniform-ternary":
		out := make([]int64, n)
		pos, neg, hw := 0, 0, 0
		for i := range out {
			out[i] = int64(rng.Intn(3) - 1)
			if out[i] > 0 {
				pos++
				hw++
			} else if out[i] < 0 {
				neg++
				hw++
			}
		}
		return out, TailSecretInfo{Name: fmt.Sprintf("UniformTernary(n=%d)", n), H: hw, Pos: pos, Neg: neg}, nil
	case "sign", "dense-sign":
		out := make([]int64, n)
		pos, neg := 0, 0
		for i := range out {
			if rng.Intn(2) == 0 {
				out[i] = -1
				neg++
			} else {
				out[i] = 1
				pos++
			}
		}
		return out, TailSecretInfo{Name: fmt.Sprintf("DenseSign(n=%d)", n), H: n, Pos: pos, Neg: neg}, nil
	default:
		return nil, TailSecretInfo{}, fmt.Errorf("unknown -lwe-secret=%q; use sparseternary, fixedweight, ternary, or sign", dist)
	}
}

func tailSignedCoeffsToMod(coeffs []int64, mod uint64) []uint64 {
	out := make([]uint64, len(coeffs))
	for i, c := range coeffs {
		out[i] = tailSignedToMod(c, mod)
	}
	return out
}

func tailSignedToMod(c int64, mod uint64) uint64 {
	if c >= 0 {
		return uint64(c) % mod
	}
	v := uint64(-c) % mod
	if v == 0 {
		return 0
	}
	return mod - v
}

func tailPolyToCoeffNormal(ringQ *ring.Ring, pIn ring.Poly, isNTT, isMontgomery bool) ring.Poly {
	out := ringQ.NewPoly()
	level := len(out.Coeffs) - 1
	if isNTT {
		ringQ.INTT(pIn, out)
	} else {
		out.CopyLvl(level, pIn)
	}
	if isMontgomery {
		ringQ.IMForm(out, out)
	}
	return out
}

func tailManualFinalKeySwitchNoSpecialQPrime(params bfv.Parameters, ct *rlwe.Ciphertext, skIn *rlwe.SecretKey, skOutSigned []int64, baseLog int, centered bool, sigma float64, rng *rand.Rand) (*rlwe.Ciphertext, int, error) {
	if ct.Level() != 0 {
		return nil, 0, fmt.Errorf("manual final key-switch expects level 0, got %d", ct.Level())
	}
	if baseLog <= 0 || baseLog >= 63 {
		return nil, 0, fmt.Errorf("invalid base log %d", baseLog)
	}

	ringQ := params.RingQ().AtLevel(0)
	Qp := params.Q()[0]
	N := params.N()
	base := uint64(1) << baseLog
	if centered && baseLog < 2 {
		return nil, 0, fmt.Errorf("centered signed decomposition requires baseLog >= 2")
	}
	digits := (bits.Len64(Qp-1) + baseLog - 1) / baseLog
	if centered {
		digits += 3
	}

	c0 := tailPolyToCoeffNormal(ringQ, ct.Value[0], ct.IsNTT, ct.IsMontgomery)
	c1 := tailPolyToCoeffNormal(ringQ, ct.Value[1], ct.IsNTT, ct.IsMontgomery)
	skInCoeffPoly := tailPolyToCoeffNormal(ringQ, skIn.Value.Q, true, true)
	skInCoeff := skInCoeffPoly.Coeffs[0]

	digitCoeffs, err := tailDecomposePolyDigits(c1.Coeffs[0], Qp, baseLog, digits, centered)
	if err != nil {
		return nil, 0, err
	}

	skOutPoly := ringQ.NewPoly()
	for i, c := range skOutSigned {
		if i >= N {
			break
		}
		skOutPoly.Coeffs[0][i] = tailSignedToMod(c, Qp)
	}

	out0 := ringQ.NewPoly()
	out1 := ringQ.NewPoly()
	copy(out0.Coeffs[0], c0.Coeffs[0])

	powB := uint64(1)
	for d := 0; d < digits; d++ {
		digitPoly := ringQ.NewPoly()
		copy(digitPoly.Coeffs[0], digitCoeffs[d])

		msg := ringQ.NewPoly()
		for i := 0; i < N; i++ {
			msg.Coeffs[0][i] = tailMulMod(powB, skInCoeff[i], Qp)
		}

		aPoly := ringQ.NewPoly()
		for i := 0; i < N; i++ {
			aPoly.Coeffs[0][i] = uint64(rng.Int63n(int64(Qp)))
		}
		aTimesSout := tailMulPolyCoeffNormal(ringQ, aPoly, skOutPoly)

		k0 := ringQ.NewPoly()
		for i := 0; i < N; i++ {
			errCoeff := tailSampleSmallGaussianMod(sigma, Qp, rng)
			v := tailAddMod(msg.Coeffs[0][i], errCoeff, Qp)
			v = tailSubMod(v, aTimesSout.Coeffs[0][i], Qp)
			k0.Coeffs[0][i] = v
		}
		k1 := aPoly

		prod0 := tailMulPolyCoeffNormal(ringQ, digitPoly, k0)
		prod1 := tailMulPolyCoeffNormal(ringQ, digitPoly, k1)
		ringQ.Add(out0, prod0, out0)
		ringQ.Add(out1, prod1, out1)

		powB = tailMulMod(powB, base%Qp, Qp)
	}

	out := bfv.NewCiphertext(params, 1, 0)
	out.Value[0].Copy(out0)
	out.Value[1].Copy(out1)
	out.IsNTT = false
	out.IsMontgomery = false
	out.IsBatched = false
	out.Scale = ct.Scale
	return out, digits, nil
}

func tailMulPolyCoeffNormal(ringQ *ring.Ring, a, b ring.Poly) ring.Poly {
	pa := ringQ.NewPoly()
	pb := ringQ.NewPoly()
	pc := ringQ.NewPoly()
	pa.Copy(a)
	pb.Copy(b)
	ringQ.NTT(pa, pa)
	ringQ.MForm(pa, pa)
	ringQ.NTT(pb, pb)
	ringQ.MForm(pb, pb)
	ringQ.MulCoeffsMontgomery(pa, pb, pc)
	ringQ.INTT(pc, pc)
	ringQ.IMForm(pc, pc)
	return pc
}

func tailDecomposePolyDigits(coeffs []uint64, mod uint64, baseLog, digits int, centered bool) ([][]uint64, error) {
	out := make([][]uint64, digits)
	for d := 0; d < digits; d++ {
		out[d] = make([]uint64, len(coeffs))
	}
	base := int64(1) << baseLog
	if !centered {
		mask := uint64(1<<baseLog) - 1
		for d := 0; d < digits; d++ {
			shift := d * baseLog
			for i, x := range coeffs {
				if shift >= 64 {
					out[d][i] = 0
				} else {
					out[d][i] = (x >> shift) & mask
				}
			}
		}
		return out, nil
	}
	if baseLog < 2 {
		return nil, fmt.Errorf("centered decomposition requires baseLog >= 2")
	}
	for i, x := range coeffs {
		carry := tailCenteredLift(x, mod)
		for d := 0; d < digits; d++ {
			rem := carry % base
			if rem < 0 {
				rem += base
			}
			if rem >= base/2 {
				rem -= base
			}
			out[d][i] = tailSignedToMod(rem, mod)
			carry = (carry - rem) / base
		}
		if carry != 0 {
			return nil, fmt.Errorf("centered decomposition did not terminate at coeff %d; increase guard digits", i)
		}
	}
	return out, nil
}

func tailCenteredLift(x, mod uint64) int64 {
	x %= mod
	if x > mod/2 {
		return -int64(mod - x)
	}
	return int64(x)
}

func tailSampleSmallGaussianMod(sigma float64, mod uint64, rng *rand.Rand) uint64 {
	if sigma == 0 {
		return 0
	}
	e := int64(math.Round(rng.NormFloat64() * sigma))
	return tailSignedToMod(e, mod)
}

func tailAddMod(a, b, mod uint64) uint64 {
	c := a + b
	if c >= mod || c < a {
		c -= mod
	}
	return c
}

func tailSubMod(a, b, mod uint64) uint64 {
	if a >= b {
		return (a - b) % mod
	}
	return mod - ((b - a) % mod)
}

func tailMulMod(a, b, mod uint64) uint64 {
	if mod == 0 {
		return 0
	}
	if bits.Len64(a)+bits.Len64(b) <= 63 {
		return (a * b) % mod
	}
	A := new(big.Int).SetUint64(a)
	B := new(big.Int).SetUint64(b)
	M := new(big.Int).SetUint64(mod)
	A.Mul(A, B).Mod(A, M)
	return A.Uint64()
}

func tailRoundedScaleCentered(x, q, t uint64) uint64 {
	if x > q/2 {
		mag := q - x
		y := tailDivRoundMul(mag, t, q)
		y %= t
		if y == 0 {
			return 0
		}
		return t - y
	}
	return tailDivRoundMul(x, t, q) % t
}

func tailDivRoundMul(x, mul, div uint64) uint64 {
	X := new(big.Int).SetUint64(x)
	M := new(big.Int).SetUint64(mul)
	D := new(big.Int).SetUint64(div)
	X.Mul(X, M)
	X.Add(X, new(big.Int).Rsh(new(big.Int).Set(D), 1))
	X.Quo(X, D)
	return X.Uint64()
}

func tailInvModUint64(a, mod uint64) (uint64, error) {
	A := new(big.Int).SetUint64(a)
	M := new(big.Int).SetUint64(mod)
	I := new(big.Int).ModInverse(A, M)
	if I == nil {
		return 0, fmt.Errorf("%d has no inverse mod %d", a, mod)
	}
	return I.Uint64(), nil
}

func tailGCDUint64(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func scaleModUint64(scale rlwe.Scale, mod uint64) uint64 {
	if mod == 0 {
		return 0
	}
	z := scale.BigInt()
	z.Mod(z, new(big.Int).SetUint64(mod))
	return z.Uint64()
}

type m1LevelScaleState struct {
	Level int
	Scale uint64
}

func estimatePolynomialInputScaleModT(params bfv.Parameters, polyInputLevel int, useLWEInput bool, modT uint64) (uint64, error) {
	if polyInputLevel < 0 || polyInputLevel > params.MaxLevel() {
		return 0, fmt.Errorf("invalid polynomial input level L%d for MaxLevel=%d", polyInputLevel, params.MaxLevel())
	}
	// Fresh BGV/BFV raw phase and the LWE->RLWE Step1 raw phase both start with
	// metadata scale 1 modulo T in this prototype. If Step1 normalization drops
	// top levels, each BGV rescale multiplies the metadata scale by Q_i^{-1} mod T.
	if useLWEInput {
		return tailScaleAfterRescaleToLevel(params, 1, params.MaxLevel(), polyInputLevel, modT)
	}
	return 1 % modT, nil
}

func m1RescaleState(params bfv.Parameters, st m1LevelScaleState, modT uint64) (m1LevelScaleState, error) {
	if st.Level <= 0 {
		return st, fmt.Errorf("cannot rescale state at L%d", st.Level)
	}
	invQ, err := tailInvModUint64(params.Q()[st.Level]%modT, modT)
	if err != nil {
		return st, fmt.Errorf("Q[%d]=%d is not invertible modulo T=%d", st.Level, params.Q()[st.Level], modT)
	}
	return m1LevelScaleState{Level: st.Level - 1, Scale: tailMulMod(st.Scale%modT, invQ, modT)}, nil
}

func m1MulPlainRescaleState(params bfv.Parameters, st m1LevelScaleState, modT uint64) (m1LevelScaleState, error) {
	// The plaintext vectors used by this program have unit metadata scale; the
	// following BGV rescale is therefore the only scale-changing part.
	return m1RescaleState(params, st, modT)
}

func m1MulCtRelinRescaleState(params bfv.Parameters, a, b m1LevelScaleState, modT uint64) (m1LevelScaleState, error) {
	level := minInt(a.Level, b.Level)
	if level <= 0 {
		return m1LevelScaleState{}, fmt.Errorf("cannot multiply/rescale at min level L%d", level)
	}
	prodScale := tailMulMod(a.Scale%modT, b.Scale%modT, modT)
	invQ, err := tailInvModUint64(params.Q()[level]%modT, modT)
	if err != nil {
		return m1LevelScaleState{}, fmt.Errorf("Q[%d]=%d is not invertible modulo T=%d", level, params.Q()[level], modT)
	}
	return m1LevelScaleState{Level: level - 1, Scale: tailMulMod(prodScale, invQ, modT)}, nil
}
func m1MulCtRelinNoRescaleState(a, b m1LevelScaleState, modT uint64) (m1LevelScaleState, error) {
	level := minInt(a.Level, b.Level)
	if level < 0 {
		return m1LevelScaleState{}, fmt.Errorf("invalid multiply level L%d", level)
	}
	prodScale := tailMulMod(a.Scale%modT, b.Scale%modT, modT)
	return m1LevelScaleState{Level: level, Scale: prodScale}, nil
}

func m1DropStateToLevel(st m1LevelScaleState, targetLevel int) (m1LevelScaleState, error) {
	if targetLevel < 0 || targetLevel > st.Level {
		return st, fmt.Errorf("cannot drop state from L%d to L%d", st.Level, targetLevel)
	}
	st.Level = targetLevel
	return st, nil
}

func estimateMonomialGenExtraState(params bfv.Parameters, input m1LevelScaleState, m, s int, wantExtra bool, modT uint64) (out m1LevelScaleState, extra m1LevelScaleState, hasExtra bool, err error) {
	if m <= 0 || !isPow2(m) {
		return out, extra, false, fmt.Errorf("m=%d must be a positive power of two", m)
	}
	if s <= 0 || !isPow2(s) {
		return out, extra, false, fmt.Errorf("s=%d must be a positive power of two", s)
	}
	slots := params.MaxSlots()
	if slots%m != 0 {
		return out, extra, false, fmt.Errorf("m=%d must divide MaxSlots=%d", m, slots)
	}
	r := slots / m
	if s > r || r%s != 0 {
		return out, extra, false, fmt.Errorf("invalid MonomialGen shape: s=%d, r=%d", s, r)
	}
	if s == 1 {
		// MonomialGen's constant case builds zero from the input ciphertext and adds
		// a plaintext. The output keeps the input ciphertext metadata scale.
		return input, m1LevelScaleState{}, false, nil
	}
	ell := bits.TrailingZeros(uint(s))
	xPow := make([]m1LevelScaleState, ell)
	xPow[0] = input
	for i := 1; i < ell; i++ {
		xPow[i], err = m1MulCtRelinRescaleState(params, xPow[i-1], xPow[i-1], modT)
		if err != nil {
			return out, extra, false, fmt.Errorf("scale simulation for xPow[%d] failed: %w", i, err)
		}
	}
	if wantExtra {
		extra = xPow[ell-1]
		hasExtra = true
	}
	acc, err := m1MulPlainRescaleState(params, xPow[0], modT)
	if err != nil {
		return out, extra, hasExtra, fmt.Errorf("scale simulation for first masked plaintext multiply failed: %w", err)
	}
	for i := 1; i < ell; i++ {
		factor, err := m1MulPlainRescaleState(params, xPow[i], modT)
		if err != nil {
			return out, extra, hasExtra, fmt.Errorf("scale simulation for masked plaintext multiply %d failed: %w", i, err)
		}
		acc, err = m1MulCtRelinRescaleState(params, acc, factor, modT)
		if err != nil {
			return out, extra, hasExtra, fmt.Errorf("scale simulation for accumulator multiply %d failed: %w", i, err)
		}
	}
	return acc, extra, hasExtra, nil
}

func estimatePolyEvalOutputState(params bfv.Parameters, modT uint64, m, d int, inputLevel int, inputScale uint64, dropBeforeLT bool, ltLevel int, ltPostLevel int, deferLTPostRescale bool, leadingTermEvaluated bool) (m1LevelScaleState, error) {
	if d <= 0 || !isPow2(d) {
		return m1LevelScaleState{}, fmt.Errorf("d=%d must be a positive power of two", d)
	}
	input := m1LevelScaleState{Level: inputLevel, Scale: inputScale % modT}
	r := params.MaxSlots() / m
	if m == 1 && d <= r {
		ctBase, ctHalf, hasHalf, err := estimateMonomialGenExtraState(params, input, m, d, leadingTermEvaluated, modT)
		if err != nil {
			return m1LevelScaleState{}, err
		}
		if !leadingTermEvaluated {
			return ctBase, nil
		}
		var ctPowD m1LevelScaleState
		if d == 1 {
			ctPowD = input
		} else {
			if !hasHalf {
				return m1LevelScaleState{}, errors.New("missing x^(d/2) scale state")
			}
			var err error
			ctPowD, err = m1MulCtRelinRescaleState(params, ctHalf, ctHalf, modT)
			if err != nil {
				return m1LevelScaleState{}, err
			}
		}
		ctLead, err := m1MulPlainRescaleState(params, ctPowD, modT)
		if err != nil {
			return m1LevelScaleState{}, err
		}
		outLevel := minInt(ctBase.Level, ctLead.Level)
		ctBase, err = m1DropStateToLevel(ctBase, outLevel)
		if err != nil {
			return m1LevelScaleState{}, err
		}
		return ctBase, nil
	}
	if d <= r || d > r*r || d%r != 0 {
		return m1LevelScaleState{}, fmt.Errorf("Algorithm 5 scale simulation requires r < d <= r^2 and r|d unless m=1 direct path, got d=%d r=%d m=%d", d, r, m)
	}
	s := d / r
	ctP, ctHalf, hasHalf, err := estimateMonomialGenExtraState(params, input, m, r, true, modT)
	if err != nil {
		return m1LevelScaleState{}, fmt.Errorf("first MonomialGen scale simulation failed: %w", err)
	}
	if !hasHalf {
		return m1LevelScaleState{}, errors.New("missing x^(r/2) scale state")
	}
	ctR, err := m1MulCtRelinRescaleState(params, ctHalf, ctHalf, modT)
	if err != nil {
		return m1LevelScaleState{}, fmt.Errorf("x^r scale simulation failed: %w", err)
	}
	ctG, ctDHalf, hasDHalf, err := estimateMonomialGenExtraState(params, ctR, m, s, true, modT)
	if err != nil {
		return m1LevelScaleState{}, fmt.Errorf("second MonomialGen scale simulation failed: %w", err)
	}
	if !hasDHalf {
		return m1LevelScaleState{}, errors.New("missing x^(d/2) scale state")
	}
	ltInputLevel, ltOutputLevel, err := resolveParallelLTLevelPolicy(ctP.Level, ctG.Level, dropBeforeLT, ltLevel, ltPostLevel, deferLTPostRescale)
	if err != nil {
		return m1LevelScaleState{}, err
	}
	ctP, err = m1DropStateToLevel(ctP, ltInputLevel)
	if err != nil {
		return m1LevelScaleState{}, err
	}
	ctY := ctP
	if ltOutputLevel >= 0 {
		for ctY.Level > ltOutputLevel {
			ctY, err = m1RescaleState(params, ctY, modT)
			if err != nil {
				return m1LevelScaleState{}, fmt.Errorf("post-LT scale rescale failed: %w", err)
			}
		}
	}
	var collapsed m1LevelScaleState
	if globalDeferPointwiseRescale && m == 1 {
		collapsed, err = m1MulCtRelinNoRescaleState(ctY, ctG, modT)
		if err != nil {
			return m1LevelScaleState{}, fmt.Errorf("collapsed ct3*ct2 no-rescale scale simulation failed: %w", err)
		}
		collapsed, err = m1RescaleState(params, collapsed, modT)
		if err != nil {
			return m1LevelScaleState{}, fmt.Errorf("deferred rescale after RotateAndSum scale simulation failed: %w", err)
		}
	} else {
		collapsed, err = m1MulCtRelinRescaleState(params, ctY, ctG, modT)
		if err != nil {
			return m1LevelScaleState{}, fmt.Errorf("collapsed ct3*ct2 scale simulation failed: %w", err)
		}
	}
	ctBase := collapsed
	if !leadingTermEvaluated {
		return ctBase, nil
	}
	ctPowD, err := m1MulCtRelinRescaleState(params, ctDHalf, ctDHalf, modT)
	if err != nil {
		return m1LevelScaleState{}, fmt.Errorf("x^d scale simulation failed: %w", err)
	}
	ctLead, err := m1MulPlainRescaleState(params, ctPowD, modT)
	if err != nil {
		return m1LevelScaleState{}, fmt.Errorf("leading plaintext multiply scale simulation failed: %w", err)
	}
	outLevel := minInt(ctBase.Level, ctLead.Level)
	ctBase, err = m1DropStateToLevel(ctBase, outLevel)
	if err != nil {
		return m1LevelScaleState{}, err
	}
	return ctBase, nil
}

func estimateM1GammaOneQ1TargetResidue(params bfv.Parameters, modT uint64, m int, d int, inputLevel int, inputScale uint64, dropBeforeLT bool, ltLevel int, ltPostLevel int, deferLTPostRescale bool, leadingTermEvaluated bool, plannedOutputLevel int) (targetResidue uint64, outputScale uint64, tailRestProduct uint64, oldGamma uint64, oldGammaInv uint64, err error) {
	out, err := estimatePolyEvalOutputState(params, modT, m, d, inputLevel, inputScale, dropBeforeLT, ltLevel, ltPostLevel, deferLTPostRescale, leadingTermEvaluated)
	if err != nil {
		return 0, 0, 0, 0, 0, err
	}
	if out.Level != plannedOutputLevel {
		return 0, 0, 0, 0, 0, fmt.Errorf("scale simulator output level L%d disagrees with planner output level L%d", out.Level, plannedOutputLevel)
	}
	outputScale = out.Scale % modT
	if out.Level <= 0 {
		// There is no post-polynomial tail rescale left. In this case gamma is the
		// polynomial-output scale itself. The last polynomial rescale has consumed
		// Q[1], so with the old chain:
		//     outputScale_old = preDropScale * Q[1]^{-1} mod T.
		// To force the new output scale to be 1, choose
		//     Q[1]_new = preDropScale = outputScale_old * Q[1]_old mod T.
		if len(params.Q()) <= 1 {
			return 0, 0, 0, 0, 0, fmt.Errorf("output level L%d has no tail modulus and the Q-chain has no Q[1] to use as the last polynomial modulus", out.Level)
		}
		targetResidue = tailMulMod(outputScale, params.Q()[1]%modT, modT)
		oldGamma = outputScale
		oldGammaInv, err = tailInvModUint64(oldGamma, modT)
		if err != nil {
			return 0, 0, 0, 0, 0, err
		}
		return targetResidue, outputScale, 1, oldGamma, oldGammaInv, nil
	}
	tailRestProduct = uint64(1)
	for i := 2; i <= out.Level; i++ {
		tailRestProduct = tailMulMod(tailRestProduct, params.Q()[i]%modT, modT)
	}
	invRest, err := tailInvModUint64(tailRestProduct, modT)
	if err != nil {
		return 0, 0, 0, 0, 0, fmt.Errorf("product Q[2..L%d]=%d is not invertible modulo T=%d", out.Level, tailRestProduct, modT)
	}
	targetResidue = tailMulMod(outputScale, invRest, modT)
	oldDroppedProduct := tailMulMod(params.Q()[1]%modT, tailRestProduct, modT)
	invOldDropped, err := tailInvModUint64(oldDroppedProduct, modT)
	if err != nil {
		return 0, 0, 0, 0, 0, err
	}
	oldGamma = tailMulMod(outputScale, invOldDropped, modT)
	oldGammaInv, err = tailInvModUint64(oldGamma, modT)
	if err != nil {
		return 0, 0, 0, 0, 0, err
	}
	return targetResidue, outputScale, tailRestProduct, oldGamma, oldGammaInv, nil
}

type M1GammaOneQInfo struct {
	Index                    int
	Mode                     string
	Prime                    uint64
	Bits                     int
	RequestedBits            int
	TargetResidueModT        uint64
	AutoComputed             bool
	OutputScaleModT          uint64
	TailRestProductModT      uint64
	PredictedOldGammaModT    uint64
	PredictedOldGammaInvModT uint64
	OldGammaInvModT          uint64
	OldGammaModT             uint64
	OldQ1ResidueModT         uint64
	OutputLevel              int
	ProductDroppedModT       uint64
	FinalQPrime              uint64
	FinalQPrimeBits          int
}

func specializeM1GammaOneQFromObservedGamma(params bfv.Parameters, literal bfv.ParametersLiteral, logQBits []int, logN int, plainMod uint64, m int, outputLevel int, oldGammaInv uint64, manualTargetResidue uint64, autoTargetResidue uint64, autoOutputScale uint64, autoTailRestProduct uint64, autoOldGamma uint64, autoOldGammaInv uint64, maxExtraBits int) (bfv.ParametersLiteral, []int, *M1GammaOneQInfo, error) {
	if m != 1 {
		return literal, logQBits, nil, fmt.Errorf("-m1-gamma-one-q requires m=1, got m=%d", m)
	}
	mode := "tail-Q[1]"
	if outputLevel <= 0 {
		mode = "poly-last-Q[1]"
	}
	if len(params.Q()) <= 1 || len(logQBits) <= 1 {
		return literal, logQBits, nil, fmt.Errorf("Q-chain too short for m=1 gamma-one specialization: outputLevel=L%d, #Q=%d", outputLevel, len(params.Q()))
	}
	if outputLevel > 0 && len(params.Q()) <= outputLevel {
		return literal, logQBits, nil, fmt.Errorf("Q-chain too short for m=1 gamma-one tail specialization: outputLevel=L%d, #Q=%d", outputLevel, len(params.Q()))
	}
	if maxExtraBits < 0 {
		return literal, logQBits, nil, fmt.Errorf("max extra bits must be non-negative, got %d", maxExtraBits)
	}

	oldGamma := uint64(0)
	autoComputed := false
	targetResidue := manualTargetResidue % plainMod
	if targetResidue == 0 && oldGammaInv != 0 {
		var err error
		oldGamma, err = tailInvModUint64(oldGammaInv%plainMod, plainMod)
		if err != nil {
			return literal, logQBits, nil, fmt.Errorf("old gamma^{-1}=%d is not invertible modulo T=%d: %w", oldGammaInv, plainMod, err)
		}
		// Legacy mode. Old run: gamma_old = inputScale / (Q[1]*...*Q[Lout]) mod T.
		// New run changes only Q[1]. To force gamma_new = 1, we need
		//     Q[1]_new * Q[2]*...*Q[Lout] = inputScale
		// hence Q[1]_new = gamma_old * Q[1]_old mod T.
		targetResidue = tailMulMod(oldGamma, params.Q()[1]%plainMod, plainMod)
	}
	if targetResidue == 0 {
		if autoTargetResidue == 0 {
			return literal, logQBits, nil, fmt.Errorf("automatic m=1 gamma-one target residue is zero; pass -m1-gamma-one-target-residue or -m1-gamma-one-prev-gamma-inv explicitly")
		}
		targetResidue = autoTargetResidue % plainMod
		autoComputed = true
	}
	if targetResidue == 0 || tailGCDUint64(targetResidue, plainMod) != 1 {
		return literal, logQBits, nil, fmt.Errorf("target residue %d is not a unit modulo T=%d", targetResidue, plainMod)
	}

	requestedBits := logQBits[1]
	prime, actualBits, err := findSpecialNTTPrimeCRT(logN, requestedBits, requestedBits+maxExtraBits, plainMod, targetResidue)
	if err != nil {
		return literal, logQBits, nil, err
	}

	q := append([]uint64(nil), params.Q()...)
	p := append([]uint64(nil), params.P()...)
	for i, qi := range q {
		if i != 1 && qi == prime {
			return literal, logQBits, nil, fmt.Errorf("special Q[1]=%d duplicates existing Q[%d]", prime, i)
		}
	}
	for i, pi := range p {
		if pi == prime {
			return literal, logQBits, nil, fmt.Errorf("special Q[1]=%d duplicates P[%d]", prime, i)
		}
	}
	q[1] = prime
	newLogQBits := append([]int(nil), logQBits...)
	newLogQBits[1] = actualBits

	productDropped := uint64(1)
	for i := 1; i <= outputLevel; i++ {
		productDropped = tailMulMod(productDropped, q[i]%plainMod, plainMod)
	}

	newLiteral := bfv.ParametersLiteral{
		LogN:             logN,
		Q:                q,
		P:                p,
		PlaintextModulus: plainMod,
	}
	info := &M1GammaOneQInfo{
		Index:                    1,
		Mode:                     mode,
		Prime:                    prime,
		Bits:                     actualBits,
		RequestedBits:            requestedBits,
		TargetResidueModT:        targetResidue,
		AutoComputed:             autoComputed,
		OutputScaleModT:          autoOutputScale % plainMod,
		TailRestProductModT:      autoTailRestProduct % plainMod,
		PredictedOldGammaModT:    autoOldGamma % plainMod,
		PredictedOldGammaInvModT: autoOldGammaInv % plainMod,
		OldGammaInvModT:          oldGammaInv % plainMod,
		OldGammaModT:             oldGamma,
		OldQ1ResidueModT:         params.Q()[1] % plainMod,
		OutputLevel:              outputLevel,
		ProductDroppedModT:       productDropped,
		FinalQPrime:              q[0],
		FinalQPrimeBits:          bits.Len64(q[0]),
	}
	return newLiteral, newLogQBits, info, nil
}

func findSpecialNTTPrimeCRT(logN int, minBits, maxBits int, plainMod uint64, residueModT uint64) (uint64, int, error) {
	if minBits <= 1 {
		return 0, 0, fmt.Errorf("invalid target bit-size %d", minBits)
	}
	if maxBits < minBits {
		return 0, 0, fmt.Errorf("maxBits=%d < minBits=%d", maxBits, minBits)
	}
	if logN < 1 || logN+1 >= 63 {
		return 0, 0, fmt.Errorf("unsupported logN=%d for special prime search", logN)
	}
	nttMod := uint64(1) << (logN + 1) // q == 1 mod 2N.
	residue, step, err := crtUint64(1%nttMod, nttMod, residueModT%plainMod, plainMod)
	if err != nil {
		return 0, 0, err
	}
	if residue == 0 {
		residue = step
	}
	for bitsTarget := minBits; bitsTarget <= maxBits; bitsTarget++ {
		if bitsTarget >= 63 {
			return 0, 0, fmt.Errorf("special prime search is limited to <63 bits, got %d", bitsTarget)
		}
		lo := uint64(1) << (bitsTarget - 1)
		hi := uint64(1) << bitsTarget
		k := uint64(0)
		if residue < lo {
			k = (lo - residue + step - 1) / step
		}
		for {
			candidate := residue + k*step
			if candidate >= hi || candidate < residue {
				break
			}
			if candidate >= lo && candidate%nttMod == 1%nttMod && candidate%plainMod == residueModT%plainMod && isPrimeUint64(candidate) {
				return candidate, bits.Len64(candidate), nil
			}
			k++
		}
	}
	return 0, 0, fmt.Errorf("no prime q found with q≡1 mod 2N, q≡%d mod T=%d, and bit-size in [%d,%d]", residueModT%plainMod, plainMod, minBits, maxBits)
}

func crtUint64(a, m, b, n uint64) (uint64, uint64, error) {
	g := tailGCDUint64(m, n)
	if a%g != b%g {
		return 0, 0, fmt.Errorf("CRT has no solution: %d mod %d is incompatible with %d mod %d", a, m, b, n)
	}
	m1 := m / g
	n1 := n / g
	delta := (b + n - (a % n)) % n
	delta /= g
	inv, err := tailInvModUint64(m1%n1, n1)
	if err != nil {
		return 0, 0, err
	}
	x := tailMulMod(delta%n1, inv, n1)
	lcmBig := new(big.Int).Mul(new(big.Int).SetUint64(m1), new(big.Int).SetUint64(n))
	if !lcmBig.IsUint64() {
		return 0, 0, fmt.Errorf("CRT modulus overflows uint64")
	}
	lcm := lcmBig.Uint64()
	resBig := new(big.Int).SetUint64(m)
	resBig.Mul(resBig, new(big.Int).SetUint64(x))
	resBig.Add(resBig, new(big.Int).SetUint64(a))
	resBig.Mod(resBig, new(big.Int).SetUint64(lcm))
	return resBig.Uint64(), lcm, nil
}

func isPrimeUint64(q uint64) bool {
	if q < 2 {
		return false
	}
	if q%2 == 0 {
		return q == 2
	}
	return new(big.Int).SetUint64(q).ProbablyPrime(32)
}
