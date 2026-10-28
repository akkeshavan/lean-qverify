#!/usr/bin/env python3
"""
Phase 2 stabilizer backend benchmark.

For GHZ(n) at n = 1, 2, 5, 10, 20, 50, 100, 200:
  - Writes a temporary Lean file containing a `native_decide` check for
    `verifyStabilizerProb (ghzCliffordCircuit (n-1)) 0 false (1/2) = true`.
  - Times the `lake env lean` call (wall-clock).
  - Records n, time, and whether the check passed.

Output: benchmarks/results/stab_bench_results.csv
"""

from __future__ import annotations
import csv
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = Path(__file__).resolve().parent / "results"
RESULTS_DIR.mkdir(exist_ok=True)

QUBIT_COUNTS = [1, 2, 5, 10, 20, 50, 100, 200]

LEAN_TEMPLATE = """\
import LeanQVerify.Stabilizer.Sound

open LeanQVerify

-- GHZ({n} qubits): native_decide tableau check
example : verifyStabilizerProb (ghzCliffordCircuit {nm1}) ⟨0, by omega⟩ false (1/2) = true :=
  by native_decide
"""


def run_lean(lean_src: str, timeout: int = 300) -> tuple[bool, float]:
    """Write src to a temp file, run lake env lean, return (success, wall_time)."""
    tmp = ROOT / "benchmarks" / "_stab_bench_tmp.lean"
    tmp.write_text(lean_src)
    start = time.perf_counter()
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            cwd=str(ROOT),
            capture_output=True,
            timeout=timeout,
        )
        elapsed = time.perf_counter() - start
        success = result.returncode == 0
    except subprocess.TimeoutExpired:
        elapsed = timeout
        success = False
    finally:
        tmp.unlink(missing_ok=True)
    return success, elapsed


def main() -> None:
    csv_path = RESULTS_DIR / "stab_bench_results.csv"
    rows: list[dict] = []

    print(f"{'n':>6}  {'time(s)':>8}  {'passed':>6}")
    print("-" * 26)

    for n in QUBIT_COUNTS:
        src = LEAN_TEMPLATE.format(n=n, nm1=n - 1)
        ok, t = run_lean(src)
        row = {"n_qubits": n, "time_s": f"{t:.2f}", "passed": ok}
        rows.append(row)
        status = "✓" if ok else "✗"
        print(f"{n:>6}  {t:>8.2f}  {status:>6}")

    with csv_path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["n_qubits", "time_s", "passed"])
        writer.writeheader()
        writer.writerows(rows)
    print(f"\nResults written to {csv_path}")


if __name__ == "__main__":
    main()
