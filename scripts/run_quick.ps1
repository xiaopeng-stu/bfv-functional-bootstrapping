# Quick smoke test for the 9-bit single-ciphertext setting.
# It uses one online run and prints the standard correctness/noise summary.

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
