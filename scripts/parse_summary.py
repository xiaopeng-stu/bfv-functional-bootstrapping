#!/usr/bin/env python3
r"""Parse paper-style benchmark summaries from data.txt into summary.csv.

Usage:
    python3 scripts/parse_summary.py data.txt summary.csv

The parser expects blocks beginning with a PowerShell prompt line of the form
`PS C:\...> go run ...`.  The helper `clean_powershell_logs.py` can convert the
mixed-encoding logs produced by some PowerShell redirection scripts into this
clean UTF-8 format.
"""
from __future__ import annotations

import csv
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional


def fix_mojibake(text: str) -> str:
    """Repair common PowerShell/OEM mojibake in copied benchmark logs."""
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


def read_text_auto(path: Path) -> str:
    data = path.read_bytes()
    for enc in ("utf-8-sig", "utf-16", "utf-16le"):
        try:
            text = data.decode(enc)
            # UTF-16LE wrongly decoded as UTF-8 usually contains many NULs.
            if text.count("\x00") < max(10, len(text) // 20):
                return fix_mojibake(text)
        except UnicodeDecodeError:
            pass
    return fix_mojibake(data.decode("utf-8", errors="replace").replace("\x00", ""))


def dur_to_seconds(s: str) -> Optional[float]:
    s = s.strip()
    if not s or s == "n/a":
        return None
    total = 0.0
    pat = re.compile(r"([0-9]+(?:\.[0-9]+)?)(ms|µs|us|ns|h|m|s)")
    pos = 0
    for m in pat.finditer(s):
        val = float(m.group(1))
        unit = m.group(2)
        if unit == "h":
            total += val * 3600
        elif unit == "m":
            total += val * 60
        elif unit == "s":
            total += val
        elif unit == "ms":
            total += val / 1_000
        elif unit in ("us", "µs"):
            total += val / 1_000_000
        elif unit == "ns":
            total += val / 1_000_000_000
        pos = m.end()
    if pos == 0:
        try:
            return float(s)
        except ValueError:
            return None
    return total


def get_duration(block: str, label: str) -> tuple[str, Optional[float]]:
    m = re.search(rf"^{re.escape(label)}\s*:\s*(.+)$", block, re.M)
    if not m:
        return "", None
    raw = m.group(1).strip()
    return raw, dur_to_seconds(raw.split()[0])


def get_value(block: str, label: str) -> str:
    m = re.search(rf"^{re.escape(label)}\s*:\s*(.+)$", block, re.M)
    return m.group(1).strip() if m else ""


def split_pipe_row(line: str) -> List[str]:
    return [x.strip() for x in line.strip().strip("|").split("|")]


def parse_first_matching_table_row(block: str, after_marker: str, contains: Optional[str] = None) -> List[str]:
    idx = block.find(after_marker)
    if idx < 0:
        return []
    lines = block[idx:].splitlines()
    for line in lines:
        if "|" not in line:
            continue
        if set(line.replace("+", "").replace("-", "").replace("|", "").strip()) == set():
            continue
        if contains and contains not in line:
            continue
        if re.search(r"\d", line) and not line.lstrip().startswith(("Parameter set", "m |", "--", "Runtime")):
            cells = split_pipe_row(line)
            if cells:
                return cells
    return []


def parse_flag(command: str, name: str) -> str:
    m = re.search(rf"(?:^|\s)-{re.escape(name)}\s+([^\s]+)", command)
    return m.group(1).strip('"') if m else ""


def parse_block(block: str, idx: int) -> Dict[str, str]:
    first = block.splitlines()[0]
    command = first.split(">", 1)[1].strip() if ">" in first else first.strip()

    row: Dict[str, str] = {
        "id": str(idx),
        "command": command,
        "N_flag": parse_flag(command, "N"),
        "m_flag": parse_flag(command, "m"),
        "degree_flag": parse_flag(command, "degree"),
        "T_flag": parse_flag(command, "T"),
        "p_flag": parse_flag(command, "p"),
        "func_flag": parse_flag(command, "func"),
        "logq_flag": parse_flag(command, "logq"),
        "logp_flag": parse_flag(command, "logp"),
        "lwe_n_flag": parse_flag(command, "lwe-n"),
        "lwe_h_flag": parse_flag(command, "lwe-h"),
        "runs_flag": parse_flag(command, "run"),
    }

    pset = parse_first_matching_table_row(block, "Parameter summary:", "-bit")
    if len(pset) >= 11:
        keys = [
            "parameter_set", "N", "logPQ", "d", "q", "p_symbolic",
            "logQ_packing", "logQ_polyeval", "logQ_stc", "logQ_buffer",
            "logQ_base", "logP",
        ]
        for k, v in zip(keys, pset):
            row[k] = v

    rt = parse_first_matching_table_row(block, "Runtime/noise summary:")
    if len(rt) >= 11:
        keys = [
            "m", "p", "bootstrap_key_gib_est", "step1_s", "step2_evalpower_s",
            "step2_batchlt_s", "step2_total_s", "step3_s", "online_subtotal_s",
            "online_wall_s", "noise_sigma_res", "per_lwe_fail_prob",
        ]
        for k, v in zip(keys, rt):
            row[k] = v

    duration_labels = {
        "average_dynamic_setup": "average dynamic setup",
        "average_run_wall_time": "average run wall time",
        "average_online_total": "average online total",
        "average_step1_lwe_to_rlwe": "  - LWE->RLWE Step1",
        "average_poly_eval_total": "  - poly eval total",
        "average_polyeval_build_basis": "    · build basis / P",
        "average_polyeval_square_xrhalf": "    · square x^(r/2)",
        "average_polyeval_build_grouped": "    · build grouped powers",
        "average_polyeval_parallel_lt": "    · ParallelLT",
        "average_polyeval_ptct_multiplies": "      · pt-ct multiplies",
        "average_polyeval_rotate_and_sum": "    · rotate-and-sum",
        "average_stc_rescale": "  - StC/rescale",
        "average_final_key_switch": "  - final key switch",
        "average_qprime_to_t": "  - Qprime -> T",
        "total_wall_time": "total wall time",
        "key_generation": "key generation",
    }
    for out, label in duration_labels.items():
        raw, sec = get_duration(block, label)
        row[out] = raw
        row[out + "_s"] = "" if sec is None else f"{sec:.9f}"

    for label, out in [
        ("runs", "runs"),
        ("all runs correct", "all_runs_correct"),
        ("output noise samples", "output_noise_samples"),
        ("output noise mean", "output_noise_mean"),
        ("output noise std dev", "output_noise_std_dev"),
        ("output noise max |e|", "output_noise_max_abs"),
    ]:
        row[out] = get_value(block, label)

    qps = re.search(r"Qprime sizing heuristic\s*:\s*(.+)$", block, re.M)
    row["qprime_sizing_heuristic"] = qps.group(1).strip() if qps else ""

    return row


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print("Usage: parse_summary.py data.txt [summary.csv]", file=sys.stderr)
        return 2
    src = Path(sys.argv[1])
    dst = Path(sys.argv[2]) if len(sys.argv) == 3 else src.with_name("summary.csv")
    text = read_text_auto(src)
    blocks = [b for b in re.split(r"(?=^PS C:)", text, flags=re.M) if b.strip()]
    rows = [parse_block(b, i) for i, b in enumerate(blocks, 1)]
    preferred = [
        "id", "parameter_set", "N", "m", "d", "q", "p", "p_symbolic",
        "logPQ", "logQ_packing", "logQ_polyeval", "logQ_stc", "logQ_buffer", "logQ_base", "logP",
        "bootstrap_key_gib_est", "step1_s", "step2_evalpower_s", "step2_batchlt_s", "step2_total_s",
        "step3_s", "online_subtotal_s", "online_wall_s", "noise_sigma_res", "per_lwe_fail_prob",
        "runs", "all_runs_correct", "output_noise_samples", "output_noise_mean", "output_noise_std_dev",
        "output_noise_max_abs", "average_dynamic_setup_s", "average_run_wall_time_s", "average_online_total_s",
        "total_wall_time", "total_wall_time_s", "qprime_sizing_heuristic", "command",
        "N_flag", "m_flag", "degree_flag", "T_flag", "p_flag", "func_flag", "logq_flag", "logp_flag",
        "lwe_n_flag", "lwe_h_flag", "runs_flag",
    ]
    all_keys = set().union(*(r.keys() for r in rows)) if rows else set()
    fields = [f for f in preferred if f in all_keys] + sorted(all_keys - set(preferred))
    with dst.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {len(rows)} rows to {dst}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
