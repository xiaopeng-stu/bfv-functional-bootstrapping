# BFV Functional Bootstrapping Prototype

This repository contains a Go/Lattigo research prototype for BFV-based functional bootstrapping of LWE ciphertexts. It supports arbitrary functions over the LWE plaintext space by evaluating a lookup-table polynomial homomorphically.

The default target function is a pseudorandom function table generated from a fixed seed. Other options include `-func identity`, `-func square`, `-func cube`, `-func neg`, `-func affine:a,b`, and `-func table`.

This is a research prototype, not production cryptographic software.

## Repository layout

```text
.
├── main.go      # implementation
├── go.mod       # Go module file; pins the Lattigo dependency
├── README.md    # installation, run commands, and parameter guide
├── data.txt     # raw benchmark logs used as supporting data
├── summary.csv  # compact parsed benchmark summary
└── LICENSE      # MIT license
```

GitHub repository path used by this package:

```text
https://github.com/xiaopeng-stu/bfv-functional-bootstrapping
```

The Go module path is already set to:

```text
github.com/xiaopeng-stu/bfv-functional-bootstrapping
```

The repository can be kept private first. After checking the README, license, and data files, you may change its visibility on GitHub. The MIT license currently uses `xiaopeng-stu` as the copyright holder; you can replace it with your full name later if desired.

## Upload this package to the private GitHub repository

If you have created the private repository `xiaopeng-stu/bfv-functional-bootstrapping` on GitHub, unzip this package and run the following commands from the repository folder.

Linux / Ubuntu:

```bash
cd bfv-functional-bootstrapping
git init
git branch -M main
git add .
git commit -m "Initial private release"
git remote add origin https://github.com/xiaopeng-stu/bfv-functional-bootstrapping.git
git push -u origin main
```

Windows PowerShell:

```powershell
cd .\bfv-functional-bootstrapping
git init
git branch -M main
git add .
git commit -m "Initial private release"
git remote add origin https://github.com/xiaopeng-stu/bfv-functional-bootstrapping.git
git push -u origin main
```

If GitHub asks for a password when pushing over HTTPS, use a GitHub personal access token instead of your GitHub login password.

## Requirements

For a completely fresh computer, you only need to install:

1. **Git**, to clone the repository.
2. **Go**, to compile and run the program.
3. **Lattigo**, which is installed automatically by Go modules from the dependency recorded in `go.mod`.

You do **not** need to clone or install Lattigo manually. In this repository, `go.mod` contains

```text
require github.com/tuneinsight/lattigo/v6 v6.2.0
```

After you run `go mod tidy` or `go mod download`, Go downloads Lattigo and its transitive dependencies into the Go module cache.

Recommended hardware for the largest 14-bit and 16-bit examples:

```text
RAM          : at least 16 GB; more is better on Windows or inside VMware
CPU          : modern multi-core CPU
Disk         : several GB free for Go module cache, build cache, and logs
Operating OS : Linux/Ubuntu or Windows 10/11 PowerShell
```

## Linux / Ubuntu setup from zero

The following commands assume Ubuntu 22.04/24.04 or a similar Debian-based Linux distribution.

### 1. Install basic tools

```bash
sudo apt update
sudo apt install -y git curl ca-certificates build-essential tar
```

### 2. Install Go

This installs the current official Linux AMD64 Go binary distribution under `/usr/local/go`.

```bash
GO_VERSION=$(curl -sSL https://go.dev/VERSION?m=text | head -n 1)
echo "Installing ${GO_VERSION}"
curl -LO "https://go.dev/dl/${GO_VERSION}.linux-amd64.tar.gz"
sudo rm -rf /usr/local/go
sudo tar -C /usr/local -xzf "${GO_VERSION}.linux-amd64.tar.gz"
echo 'export PATH=$PATH:/usr/local/go/bin' >> ~/.bashrc
source ~/.bashrc
```

Check that Go and Git are available:

```bash
go version
git --version
```

If `go version` is not found, close the terminal, open a new terminal, and run `go version` again.

### 3. Get this repository

If the repository has already been uploaded to GitHub:

```bash
git clone https://github.com/xiaopeng-stu/bfv-functional-bootstrapping.git
cd bfv-functional-bootstrapping
```

If you downloaded the source as a zip file from GitHub, unzip it and enter the folder instead:

```bash
unzip bfv-functional-bootstrapping-main.zip
cd bfv-functional-bootstrapping-main
```

### 4. Install Lattigo through Go modules

From the repository root, run:

```bash
go mod tidy
go mod download
```

Check that Lattigo was downloaded:

```bash
go list -m github.com/tuneinsight/lattigo/v6
```

You should see a line similar to:

```text
github.com/tuneinsight/lattigo/v6 v6.2.0
```

### 5. Run a quick test

A quick 9-bit single-ciphertext test is:

```bash
go run . -N 32768 -m 1 -n 2048 -d 65536 -T 65537 -p 512 -func random -logq "52,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,30" -logp "50,50" -run 1 -final-ks-level-p=-1 -final-ks-pow2-base=1
```

For longer experiments, it is usually better to build the binary once:

```bash
go build -o fb .
./fb -N 32768 -m 1 -n 2048 -d 65536 -T 65537 -p 512 -func random -logq "52,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,30" -logp "50,50" -run 1 -final-ks-level-p=-1 -final-ks-pow2-base=1
```

## Windows PowerShell setup from zero

The following commands assume Windows 10/11 with PowerShell.

### 1. Install Git and Go

Open PowerShell. You may use a normal PowerShell window; administrator mode is only needed if your Windows installation requires it.

```powershell
winget install --id Git.Git -e --source winget
winget install --id GoLang.Go -e --source winget
```

After installation, close PowerShell and open a new PowerShell window. Then check:

```powershell
git --version
go version
```

If `winget` is not available, install manually:

```text
Git for Windows : https://git-scm.com/download/win
Go              : https://go.dev/dl/
```

Use the default installer options. After installation, open a new PowerShell window and run `git --version` and `go version`.

### 2. Get this repository

If the repository has already been uploaded to GitHub:

```powershell
git clone https://github.com/xiaopeng-stu/bfv-functional-bootstrapping.git
cd bfv-functional-bootstrapping
```

If you downloaded GitHub's `Code -> Download ZIP`, unzip it, then enter the folder. For example:

```powershell
cd $env:USERPROFILE\Desktop\bfv-functional-bootstrapping-main
```

### 3. Install Lattigo through Go modules

From the repository root:

```powershell
go mod tidy
go mod download
go list -m github.com/tuneinsight/lattigo/v6
```

The last command should print a Lattigo v6 module line such as:

```text
github.com/tuneinsight/lattigo/v6 v6.2.0
```

### 4. Run a quick test

The same one-line command works in PowerShell:

```powershell
go run . -N 32768 -m 1 -n 2048 -d 65536 -T 65537 -p 512 -func random -logq "52,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,30" -logp "50,50" -run 1 -final-ks-level-p=-1 -final-ks-pow2-base=1
```

For repeated runs, build first:

```powershell
go build -o fb.exe .
.\fb.exe -N 32768 -m 1 -n 2048 -d 65536 -T 65537 -p 512 -func random -logq "52,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,30" -logp "50,50" -run 1 -final-ks-level-p=-1 -final-ks-pow2-base=1
```

## Recommended paper-parameter commands

The following commands use `-run 1` for quick testing. To reproduce the benchmark logs in `data.txt`, change `-run 1` to `-run 100`.

### Batched functional bootstrapping

#### 16-bit plaintext space, `m = 16`, `n = 2048`, `d = 8388607`

```bash
go run . -N 65536 -m 16 -n 2048 -d 8388607 -func random -logq "52,59,59,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,30" -logp "55,55,55,55,55" -T 8257537 -p 65536 -final-ks-level-p=-1 -final-ks-pow2-base=1 -run 1
```

#### 14-bit plaintext space, `m = 32`, `n = 2048`, `d = 4194303`

```bash
go run . -N 65536 -m 32 -n 2048 -d 4194303 -func random -logq "52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,30" -logp "55,55,55,55,55,55" -T 2752513 -p 16384 -final-ks-level-p=-1 -final-ks-pow2-base=1 -run 1
```

#### 12-bit plaintext space, `m = 64`, `n = 2048`, `d = 1048575`

```bash
go run . -N 65536 -m 64 -n 2048 -d 1048575 -func random -logq "52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,30" -logp "55,55,55,55,55,55" -T 786433 -p 4096 -final-ks-level-p=-1 -final-ks-pow2-base=1 -run 1
```

#### 9-bit plaintext space, `m = 128`, `n = 2048`, `d = 65536`

```bash
go run . -N 32768 -m 128 -n 2048 -d 65536 -T 65537 -p 512 -func random -logq "45,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,30" -logp "45,45" -lt-drop-level 3 -lt-post-level 2 -final-ks-level-p=-1 -final-ks-pow2-base=1 -run 1
```

### Single-ciphertext functional bootstrapping

#### 9-bit plaintext space, `m = 1`, `n = 2048`, `d = 65536`

```bash
go run . -N 32768 -m 1 -n 2048 -d 65536 -T 65537 -p 512 -func random -logq "52,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,30" -logp "50,50" -run 1 -final-ks-level-p=-1 -final-ks-pow2-base=1
```

#### 12-bit plaintext space, `m = 1`, `n = 2048`, `d = 1048575`

```bash
go run . -N 65536 -m 1 -n 2048 -d 1048575 -func random -logq "52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,30" -logp "55,55,55,55,55,55" -T 786433 -p 4096 -run 1 -final-ks-level-p=-1 -final-ks-pow2-base=1
```

#### 14-bit plaintext space, `m = 1`, `n = 2048`, `d = 4194303`

```bash
go run . -N 65536 -m 1 -n 2048 -d 4194303 -func random -logq "52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,30" -logp "55,55,55,55,55,55" -T 2752513 -p 16384 -run 1 -final-ks-level-p=-1 -final-ks-pow2-base=1
```

#### 16-bit plaintext space, `m = 1`, `n = 2048`, `d = 8388607`

```bash
go run . -N 65536 -m 1 -n 2048 -d 8388607 -func random -logq "53,59,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,30" -logp "55,55,55,55,55" -T 8257537 -p 65536 -run 1 -final-ks-level-p=-1 -final-ks-pow2-base=1
```

## What the parameters mean

| Flag | Meaning |
|---|---|
| `-N` | BFV ring degree. The BFV polynomial ring is usually `Z_Q[X]/(X^N+1)`. Larger `N` gives more slots and a larger security dimension, but also increases cost. |
| `-m` | Number of LWE ciphertexts packed and bootstrapped together. `m=1` is the single-ciphertext case. |
| `-n` | LWE dimension. The paper-parameter commands above use `n=2048`. |
| `-d` | Degree of the lookup-table polynomial for the target function. For large plaintext spaces, `d+1` is usually a power of two. |
| `-func` | Target function over `Z_p`. Useful choices include `random`, `identity`, `square`, `cube`, `neg`, `affine:a,b`, and `table`. |
| `-T` | BFV plaintext modulus. |
| `-p` | LWE plaintext/message modulus. The plaintext space has approximately `log2(p)` bits. |
| `-logq` | Bit sizes of the BFV `Q` modulus chain. The first entry is the lowest-level modulus prime. |
| `-logp` | Bit sizes of auxiliary `P` primes used by hybrid key switching. |
| `-lt-drop-level` | Optional level drop before the sparse linear transform. Used in the 9-bit batched parameter set. |
| `-lt-post-level` | Optional target level after the sparse linear transform. Used in the 9-bit batched parameter set. |
| `-final-ks-level-p=-1` | Use a Q-only final BFV key-switch key, with no `P` limbs. This avoids using a large `P` modulus for the final embedded LWE secret. |
| `-final-ks-pow2-base` | Base-2 decomposition width for the Q-only final key switch. `1` is conservative but slower and produces a larger final key. Larger values reduce key size and time but may increase noise. |
| `-run` | Number of independent benchmark repetitions. Use `1` for quick testing and `100` for paper-style data. |
| `-gc-every` | Optional manual garbage-collection interval. Default `0` leaves GC to Go. For memory-constrained machines, try `-gc-every=10` or `20`. |
| `-mem-progress` | Print Go heap and RSS diagnostics during long runs. |

## Benchmark data included

- `data.txt` contains the raw run logs used as supporting data.
- `summary.csv` contains a compact parsed summary, including average online time, noise statistics, and key sizes.

Summary of the included 100-run data:

| Case | m | p bits | d | Avg. online time | Max abs. noise | Correct |
|---|---:|---:|---:|---:|---:|:---:|
| batched 16-bit | 16 | 16 | 8388607 | 18.072756834s | 47 | true |
| batched 14-bit | 32 | 14 | 4194303 | 16.876113773s | 38 | true |
| batched 12-bit | 64 | 12 | 1048575 | 13.940105025s | 42 | true |
| batched 9-bit | 128 | 9 | 65536 | 3.773339770s | 41 | true |
| single 9-bit | 1 | 9 | 65536 | 3.149412944s | 32 | true |
| single 12-bit | 1 | 12 | 1048575 | 8.359151837s | 26 | true |
| single 14-bit | 1 | 14 | 4194303 | 9.345778149s | 29 | true |
| single 16-bit | 1 | 16 | 8388607 | 10.629197091s | 28 | true |

## Troubleshooting

### `go: command not found`

Go is not in your `PATH`. On Linux, run:

```bash
source ~/.bashrc
go version
```

If it still fails, add Go manually:

```bash
export PATH=$PATH:/usr/local/go/bin
```

On Windows, close PowerShell and open a new PowerShell window after installing Go.

### `git: command not found`

Install Git first. On Ubuntu:

```bash
sudo apt install -y git
```

On Windows:

```powershell
winget install --id Git.Git -e --source winget
```

### Lattigo download is slow or fails

Check the module proxy setting:

```bash
go env GOPROXY
```

The default usually works:

```bash
go env -w GOPROXY=https://proxy.golang.org,direct
```

Then rerun:

```bash
go mod tidy
```

### Windows or VMware becomes very slow

The largest parameter sets generate several GiB of rotation and evaluation keys. If a run suddenly becomes slow, check whether the system is swapping. On Windows or inside VMware, it is often better to build once and run the binary:

```powershell
go build -o fb.exe .
.\fb.exe <parameters>
```

Useful diagnostics:

```bash
go run . <parameters> -mem-progress=true
```

For long repeated runs on memory-constrained machines:

```bash
go run . <parameters> -run 100 -gc-every=10
```
