#!/usr/bin/env bash
set -euo pipefail

# Full paper-style benchmarks matching data.txt.
# Logs are written to ./logs and then parsed into summary-regenerated.csv.

mkdir -p logs
go build -o fb .

./fb -N 32768 -m 1 -degree 65536 -T 65537 -p 512 -func random -logq 36,34x18,30 -logp 34,34,34,34 -lwe-n 2048 -lwe-h 512 -run 100 | tee logs/9bit_m1.log
./fb -N 32768 -m 128 -degree 65536 -T 65537 -p 512 -func random -logq 36,34,34x18,30 -logp 34,34,34,34 -lwe-n 2048 -lwe-h 512 -run 100 | tee logs/9bit_m128.log

./fb -N 65536 -m 1 -degree 1048575 -T 786433 -p 4096 -func random -logq 39,38x22,38 -logp 38,38,38,38,38 -lwe-n 2048 -lwe-h 512 -run 100 | tee logs/12bit_m1.log
./fb -N 65536 -m 64 -degree 1048575 -T 786433 -p 4096 -func random -logq 39,38,38x22,38 -logp 38,38,38,38,38 -lwe-n 2048 -lwe-h 512 -run 100 | tee logs/12bit_m64.log

./fb -N 65536 -m 1 -degree 4194303 -T 2752513 -p 16384 -func random -logq 42,40x24,40 -logp 40,40,40,40,40 -lwe-n 2048 -lwe-h 512 -run 100 | tee logs/14bit_m1.log
./fb -N 65536 -m 32 -degree 4194303 -T 2752513 -p 16384 -func random -logq 42,40,40x24,40 -logp 40,40,40,40,40 -lwe-n 2048 -lwe-h 512 -run 100 | tee logs/14bit_m32.log

./fb -N 65536 -m 1 -degree 8388607 -T 8257537 -p 65536 -func random -logq 45,43x25,40 -logp 40,40,40,40,40,40 -lwe-n 2048 -lwe-h 512 -run 100 | tee logs/16bit_m1.log
./fb -N 65536 -m 16 -degree 8388607 -T 8257537 -p 65536 -func random -logq 45,45,45x25,40 -logp 40,40,40,40,40,40 -lwe-n 2048 -lwe-h 512 -run 100 | tee logs/16bit_m16.log

cat logs/*.log > data-regenerated.txt
python3 scripts/parse_summary.py data-regenerated.txt summary-regenerated.csv
