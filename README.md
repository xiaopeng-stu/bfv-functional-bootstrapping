# BFV Functional Bootstrapping with Sparse Polynomial Evaluation

This repository contains a Go/Lattigo research prototype for BFV-based functional bootstrapping of LWE ciphertexts. It implements the sparse-packing polynomial-evaluation strategy used in the accompanying paper:

> **Functional Bootstrapping for a Single LWE Ciphertext with O~(1) Polynomial Multiplications**  
> Xiaopeng Zheng, Hongbo Li, and Dingkang Wang

The code supports arbitrary functions over the LWE plaintext space by interpolating a lookup-table polynomial and evaluating it homomorphically on sparsely packed BFV ciphertexts. The main target regime is single-ciphertext, small-batch, and moderate-batch functional bootstrapping over 9-, 12-, 14-, and 16-bit plaintexts.

This is a research prototype, not production cryptographic software.

## Repository layout

```text
.
├── main.go                         # implementation
├── go.mod                          # Go module file; pins Lattigo v6.2.0
├── README.md                       # installation, usage, and benchmark guide
├── LICENSE                         # MIT license
├── CITATION.cff                    # citation metadata for GitHub
├── data.txt                        # cleaned UTF-8 benchmark logs used for the table
├── summary.csv                     # parsed compact benchmark summary
├── scripts/
│   ├── run_quick.sh                # quick Linux/macOS smoke test
│   ├── run_quick.ps1               # quick Windows PowerShell smoke test
│   ├── run_paper_benchmarks.sh     # full Linux/macOS benchmark commands
│   ├── run_paper_benchmarks.ps1    # full Windows PowerShell benchmark commands
│   ├── run_all_8.ps1               # sequential Windows script with separate logs
│   ├── clean_powershell_logs.py    # clean mixed-encoding PowerShell logs
│   └── parse_summary.py            # parser from cleaned logs to summary.csv
└── docs/
    ├── algorithm_mapping.md        # mapping between paper algorithms and code
    ├── functional-bootstrapping-7-3.pdf
    └── raw/run_20260704_013451.zip # original raw PowerShell logs for data.txt
```

The Go module path is

```text
github.com/xiaopeng-stu/bfv-functional-bootstrapping
```

## What is implemented

The online functional bootstrapping path consists of three main stages.

1. **LWE to sparse BFV/RLWE packing.** The program generates LWE ciphertexts with phase `alpha*m + e`, homomorphically computes `b - <a,s>`, and packs the phases into BFV slots with repetition multiplicity `r = N/m`.
2. **Sparse polynomial evaluation.** The program evaluates the LUT polynomial using the sparse Algorithm-5 path: power generation, hoisted BSGS BatchLT, multiplication by grouped powers, rotate-and-sum, and the optional leading term for the `degree = 2^k` split-top case.
3. **BFV/RLWE back to LWE.** The program applies sparse SlotToCoeff when needed, rescales to the base Q-prime, performs the final Q-prime-only key switch, samples out LWE ciphertexts, and switches from Q-prime to the target LWE modulus `T`.

The benchmark configuration in `data.txt` uses a fixed sparse ternary LWE secret with Hamming weight `h = 512`, generates fresh LWE ciphertexts and fresh random functions in each run, and keeps the BFV parameters and evaluation keys fixed across the 100 runs of each setting.

## Requirements

Install:

- Git
- Go 1.25 or newer is recommended
- Lattigo is downloaded automatically by Go modules

The dependency is pinned in `go.mod`:

```text
require github.com/tuneinsight/lattigo/v6 v6.2.0
```

Recommended hardware for the full benchmark commands:

```text
RAM : 32 GB or more for the largest settings
CPU : modern desktop/server CPU
Disk: several GB free for Go module cache, build cache, and logs
```

For a quick smoke test, much less time is required.

## Install and run

### Linux / Ubuntu

```bash
git clone https://github.com/xiaopeng-stu/bfv-functional-bootstrapping.git
cd bfv-functional-bootstrapping
go mod tidy
go run . \
  -N 32768 \
  -m 1 \
  -degree 65536 \
  -T 65537 \
  -p 512 \
  -func random \
  -logq 36,34x18,30 \
  -logp 34,34,34,34 \
  -lwe-n 2048 \
  -lwe-h 512 \
  -run 1
```

You can also run the included smoke-test script:

```bash
bash scripts/run_quick.sh
```

### Windows PowerShell

```powershell
git clone https://github.com/xiaopeng-stu/bfv-functional-bootstrapping.git
cd bfv-functional-bootstrapping
go mod tidy
go run . `
  -N 32768 `
  -m 1 `
  -degree 65536 `
  -T 65537 `
  -p 512 `
  -func random `
  -logq 36,34x18,30 `
  -logp 34,34,34,34 `
  -lwe-n 2048 `
  -lwe-h 512 `
  -run 1
```

You can also run:

```powershell
.\scripts\run_quick.ps1
```

## Building once before long runs

For long experiments, build the executable once.

Linux / Ubuntu:

```bash
go build -o fb .
./fb -N 32768 -m 1 -degree 65536 -T 65537 -p 512 -func random -logq 36,34x18,30 -logp 34,34,34,34 -lwe-n 2048 -lwe-h 512 -run 1
```

Windows PowerShell:

```powershell
go build -o fb.exe .
.\fb.exe -N 32768 -m 1 -degree 65536 -T 65537 -p 512 -func random -logq 36,34x18,30 -logp 34,34,34,34 -lwe-n 2048 -lwe-h 512 -run 1
```

## Benchmark summary

The raw logs are stored in `data.txt`. The parsed table is stored in `summary.csv`. The current data were regenerated from the uploaded `run_20260704_013451.zip` logs and use `-lwe-h 512`.

| setting | N | d | m | p | logQ layout | logP | online wall (s) | Step 1 | Step 2 | BatchLT | Step 3 | noise σ | fail prob. |
|---|---:|---:|---:|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 9-bit (m=1) | 32768 | 2^16 | 1 | 2^9 | base 36, poly 34×18, StC 0, pack 30 | 34×4 | 2.061 | 0.693 | 1.284 | 0.098 | 0.081 | 6.4474 | ≤ 2^-68.11 |
| 9-bit (m=128) | 32768 | 2^16 | 128 | 2^9 | base 36, poly 34×18, StC 34, pack 30 | 34×4 | 3.041 | 0.838 | 1.763 | 0.425 | 0.381 | 6.5792 | ≤ 2^-68.11 |
| 12-bit (m=1) | 65536 | 2^20-1 | 1 | 2^12 | base 39, poly 38×22, StC 0, pack 38 | 38×5 | 6.158 | 1.835 | 4.141 | 0.296 | 0.172 | 5.8371 | ≤ 2^-154.51 |
| 12-bit (m=64) | 65536 | 2^20-1 | 64 | 2^12 | base 39, poly 38×22, StC 38, pack 38 | 38×5 | 9.655 | 1.831 | 6.810 | 2.557 | 0.554 | 6.5668 | ≤ 2^-154.51 |
| 14-bit (m=1) | 65536 | 2^22-1 | 1 | 2^14 | base 42, poly 40×24, StC 0, pack 40 | 40×5 | 7.484 | 2.240 | 5.030 | 0.411 | 0.184 | 6.6909 | ≤ 2^-118.06 |
| 14-bit (m=32) | 65536 | 2^22-1 | 32 | 2^14 | base 42, poly 40×24, StC 40, pack 40 | 40×5 | 13.360 | 2.309 | 9.711 | 4.431 | 0.421 | 6.5490 | ≤ 2^-118.06 |
| 16-bit (m=1) | 65536 | 2^23-1 | 1 | 2^16 | base 45, poly 43×25, StC 0, pack 40 | 40×6 | 8.022 | 2.148 | 5.612 | 0.598 | 0.205 | 6.1077 | ≤ 2^-65.97 |
| 16-bit (m=16) | 65536 | 2^23-1 | 16 | 2^16 | base 45, poly 45×25, StC 45, pack 40 | 40×6 | 13.112 | 2.275 | 9.570 | 3.983 | 0.348 | 6.4563 | ≤ 2^-65.97 |

`Step 2` is the full homomorphic polynomial-evaluation stage. `BatchLT` is listed separately because it is one of the main components of Step 2. The failure probability shown here is the secret-aware sparse bound using `||s||_2^2 + 1 = h + 1 = 513`.

## Reproducing the benchmark data

Run all paper-style benchmarks with:

Linux / Ubuntu:

```bash
bash scripts/run_paper_benchmarks.sh
```

Windows PowerShell:

```powershell
.\scripts\run_paper_benchmarks.ps1
```

For the sequential PowerShell workflow that creates a timestamped log directory, use:

```powershell
powershell -ExecutionPolicy Bypass -File .\scripts\run_all_8.ps1
```

If the PowerShell logs contain mixed encoding, clean them first and then parse:

```powershell
python scripts\clean_powershell_logs.py .\logs\run_YYYYMMDD_HHMMSS data-regenerated.txt
python scripts\parse_summary.py data-regenerated.txt summary-regenerated.csv
```

To parse an existing clean log file manually:

```bash
python3 scripts/parse_summary.py data.txt summary.csv
```

or on Windows:

```powershell
python scripts\parse_summary.py data.txt summary.csv
```

## Important command-line options

### Core parameters

- `-N`: BFV ring degree and number of slots.
- `-m`: number of logical sparse-packed LWE ciphertexts.
- `-degree`: polynomial degree. The program supports the `degree+1 = 2^k` case and the split-top `degree = 2^k` case.
- `-T`: BFV plaintext modulus and LWE ciphertext modulus.
- `-p`: LWE input/output message modulus.
- `-logq`: comma-separated Q-prime bit-size pattern. Repetition syntax such as `34x18` is supported.
- `-logp`: comma-separated special-P bit-size pattern.
- `-lwe-n`: LWE dimension.
- `-lwe-h`: sparse ternary secret Hamming weight. The current benchmark table uses `512`.

### Function and input generation

- `-func random`: random lookup table generated from `-func-seed`.
- `-func identity`, `-func square`, `-func cube`, `-func neg`, `-func affine:a,b`: deterministic functions over `Z_p`.
- `-func-table`: inline table.
- `-func-file`: table loaded from a file.
- `-input-seed`, `-func-seed`, `-phase-error-seed`, `-lwe-a-seed`: base seeds. In multi-run mode, run `i` uses base seed plus `i`.

### Online path and diagnostics

- `-run`: number of online runs. Keys and BFV parameters are generated once, while the LWE ciphertexts and function table can vary across runs.
- `-poly-precompute-pt=true`: precompute polynomial-evaluation plaintext masks.
- `-scheme-d=true`: use Scheme-D output scaling.
- `-extract-lwe=true`: run the BFV/RLWE-to-LWE tail after polynomial evaluation.
- `-qprime-ks-noise=true`: print Q-prime-domain noise before and after the final key switch.
- `-mul-trace`: print operation-level level/Q-bit/timing diagnostics.
- `-poly-noise-trace`: decrypt intermediate ciphertexts for detailed polynomial-evaluation noise tracing. This is slow and should only be used for debugging.

## Full benchmark commands

The eight commands used to generate `data.txt` are listed below.

```bash
# 9-bit (m=1)
go run . -N 32768 -m 1 -degree 65536 -T 65537 -p 512 -func random -logq 36,34x18,30 -logp 34,34,34,34 -lwe-n 2048 -lwe-h 512 -run 100

# 9-bit (m=128)
go run . -N 32768 -m 128 -degree 65536 -T 65537 -p 512 -func random -logq 36,34,34x18,30 -logp 34,34,34,34 -lwe-n 2048 -lwe-h 512 -run 100

# 12-bit (m=1)
go run . -N 65536 -m 1 -degree 1048575 -T 786433 -p 4096 -func random -logq 39,38x22,38 -logp 38,38,38,38,38 -lwe-n 2048 -lwe-h 512 -run 100

# 12-bit (m=64)
go run . -N 65536 -m 64 -degree 1048575 -T 786433 -p 4096 -func random -logq 39,38,38x22,38 -logp 38,38,38,38,38 -lwe-n 2048 -lwe-h 512 -run 100

# 14-bit (m=1)
go run . -N 65536 -m 1 -degree 4194303 -T 2752513 -p 16384 -func random -logq 42,40x24,40 -logp 40,40,40,40,40 -lwe-n 2048 -lwe-h 512 -run 100

# 14-bit (m=32)
go run . -N 65536 -m 32 -degree 4194303 -T 2752513 -p 16384 -func random -logq 42,40,40x24,40 -logp 40,40,40,40,40 -lwe-n 2048 -lwe-h 512 -run 100

# 16-bit (m=1)
go run . -N 65536 -m 1 -degree 8388607 -T 8257537 -p 65536 -func random -logq 45,43x25,40 -logp 40,40,40,40,40,40 -lwe-n 2048 -lwe-h 512 -run 100

# 16-bit (m=16)
go run . -N 65536 -m 16 -degree 8388607 -T 8257537 -p 65536 -func random -logq 45,45,45x25,40 -logp 40,40,40,40,40,40 -lwe-n 2048 -lwe-h 512 -run 100
```

## Uploading this package to GitHub

After unzipping the package:

```bash
cd bfv-functional-bootstrapping
git init
git branch -M main
git add .
git commit -m "Initial research prototype release"
git remote add origin https://github.com/xiaopeng-stu/bfv-functional-bootstrapping.git
git push -u origin main
```

If GitHub asks for a password when pushing over HTTPS, use a GitHub personal access token instead of the account password.

## Notes

- The comparison data in the paper is intended to show the single-ciphertext, small-batch, and moderate-batch regime. It is not a cycle-accurate apples-to-apples comparison with other libraries or machines.
- The single-ciphertext rows skip sparse SlotToCoeff by default because the output is already a constant replicated plaintext.
- The code uses Lattigo's BGV package as the unified integer-arithmetic backend for BFV-style plaintext arithmetic in Lattigo v6.
