#!/usr/bin/env python3
r"""Clean mixed-encoding PowerShell benchmark logs into a UTF-8 data.txt file.

Usage:
    python3 scripts/clean_powershell_logs.py logs/run_20260704_013451 data.txt

This is useful for logs produced by a PowerShell script that writes a UTF-8
header/footer but appends Go program output with native PowerShell redirection.
The output is normalized into blocks beginning with
`PS C:\...> go run ...`, which can then be parsed by `parse_summary.py`.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path


def fix_mojibake(text: str) -> str:
    text = (
        text.replace("脳", "×")
        .replace("螖", "Δ")
        .replace("路", "·")
        .replace("碌", "µ")
        .replace("蟽", "σ")
        .replace("\u0a0d", "")
    )
    text = re.sub(r"鈮\?\s*2\^", "≤ 2^", text)
    text = re.sub(r"(paper-style analytic bound\s*:\s*)鈮\?", r"\1≤ ", text)
    text = re.sub(r"(secret-aware sparse bound\s*:\s*)鈮\?", r"\1≤ ", text)
    text = re.sub(
        r"(projected (?:T|max after Q'->T|max after Qprime->T)[^\n]*?)鈮\?\.(\d+)",
        lambda m: m.group(1) + "≈0." + m.group(2),
        text,
    )
    text = re.sub(r"(min Q' for projected max < radius\s*)鈮\?", r"\1≈", text)
    text = re.sub(r"(with \+2/\+4/\+8-bit margin\s*)鈮\?", r"\1≈", text)
    text = re.sub(
        r"(required Q'\s*)鈮\?(\d+) bits \(\+2=(\d+)",
        lambda m: f"{m.group(1)}≈{int(m.group(3)) - 2} bits (+2={m.group(3)}",
        text,
    )
    return text.replace("鈮?", "≈")


def clean_log(path: Path, prompt_dir: str) -> str:
    raw = path.read_bytes()
    split = raw.find(b"\r\n\r\n")
    sep_len = 4
    if split < 0:
        split = raw.find(b"\n\n")
        sep_len = 2
    if split >= 0:
        header_bytes = raw[: split + sep_len]
        rest = raw[split + sep_len :]
    else:
        header_bytes = b""
        rest = raw
    header = header_bytes.decode("utf-8-sig", errors="replace")
    m = re.search(r"^Command:\s*(.+)$", header, re.M)
    command = m.group(1).strip() if m else "go run ."

    footer_pat = b"============================================================\r\nEnd time:"
    idx = rest.rfind(footer_pat)
    if idx < 0:
        footer_pat = b"============================================================\nEnd time:"
        idx = rest.rfind(footer_pat)
    body_bytes = rest[:idx] if idx >= 0 else rest
    if len(body_bytes) % 2 == 1:
        body_bytes = body_bytes[:-1]
    body = body_bytes.decode("utf-16le", errors="replace").replace("\ufeff", "")
    body = fix_mojibake(body)
    return f"PS {prompt_dir}> {command}\n" + body.strip() + "\n"


def main() -> int:
    if len(sys.argv) not in (3, 4):
        print("Usage: clean_powershell_logs.py LOG_DIR data.txt [PROMPT_DIR]", file=sys.stderr)
        return 2
    log_dir = Path(sys.argv[1])
    out = Path(sys.argv[2])
    prompt_dir = sys.argv[3] if len(sys.argv) == 4 else r"C:\Users\zheng\Desktop\lattigo-v6.2.0\examples\singleparty\6-14\fb_final"
    logs = sorted(log_dir.glob("*.log"))
    if not logs:
        raise SystemExit(f"no .log files found in {log_dir}")
    text = "\n".join(clean_log(p, prompt_dir) for p in logs)
    out.write_text(text, encoding="utf-8")
    print(f"wrote {len(logs)} cleaned logs to {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
