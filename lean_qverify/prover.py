"""
End-to-end structural verification pipeline.

This module bridges the gap between QASM parsing and formal proof:
1. Calls lean-qverify-check --emit-lean to get a Lean circuit definition.
2. Wraps it in a theorem file with an automated proof strategy.
3. Calls `lean` to kernel-check the theorem.
4. Returns STRUCT_PROVED or FAILED.

Structural specs (gate count, depth, CNOT count) are proved by
  simp [countGates/depth, importedCircuit] + omega
which works for any circuit regardless of rotation angle values.
"""

from __future__ import annotations

import logging
import os
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Optional

logger = logging.getLogger(__name__)

_DEFAULT_BIN = "lean-qverify-check"


def _find_binary() -> Optional[Path]:
    import os as _os
    env_path = _os.environ.get("LEAN_QVERIFY_BIN")
    if env_path:
        p = Path(env_path)
        if p.is_file():
            return p
    found = shutil.which(_DEFAULT_BIN)
    return Path(found) if found else None


def _find_lean() -> Optional[Path]:
    found = shutil.which("lean")
    return Path(found) if found else None


def _find_project_root(check_bin: Path) -> Optional[Path]:
    """
    Infer the lean-qverify project root from the binary path.
    The binary is typically at <root>/.lake/build/bin/lean-qverify-check.
    """
    # Walk up from the binary looking for lakefile.lean
    p = check_bin.resolve()
    for _ in range(6):
        p = p.parent
        if (p / "lakefile.lean").exists():
            return p
    # Fallback: look in the LEAN_QVERIFY_ROOT env var
    env_root = os.environ.get("LEAN_QVERIFY_ROOT")
    if env_root:
        root = Path(env_root)
        if (root / "lakefile.lean").exists():
            return root
    return None


# ---------------------------------------------------------------------------
# Spec description
# ---------------------------------------------------------------------------

class StructSpecKind(Enum):
    GATE_COUNT   = "gate_count"    # countGates (fun _ => true) c = k
    CNOT_COUNT   = "cnot_count"    # countGates (.CNOT ..) c = k
    RZ_COUNT     = "rz_count"      # countGates (.RZ ..) c = k
    MAX_DEPTH    = "max_depth"     # depth c ≤ k


@dataclass
class StructuralSpec:
    kind:  StructSpecKind
    bound: int   # exact count (for *_COUNT) or upper bound (for MAX_DEPTH)

    @staticmethod
    def total_gates(k: int) -> "StructuralSpec":
        return StructuralSpec(StructSpecKind.GATE_COUNT, k)

    @staticmethod
    def cnot_count(k: int) -> "StructuralSpec":
        return StructuralSpec(StructSpecKind.CNOT_COUNT, k)

    @staticmethod
    def rz_count(k: int) -> "StructuralSpec":
        return StructuralSpec(StructSpecKind.RZ_COUNT, k)

    @staticmethod
    def max_depth(k: int) -> "StructuralSpec":
        return StructuralSpec(StructSpecKind.MAX_DEPTH, k)


# ---------------------------------------------------------------------------
# Theorem template
# ---------------------------------------------------------------------------

_GATE_PREDS = {
    StructSpecKind.GATE_COUNT: "(fun _ => true)",
    StructSpecKind.CNOT_COUNT: "(fun g => match g with | .CNOT .. => true | _ => false)",
    StructSpecKind.RZ_COUNT:   "(fun g => match g with | .RZ .. => true | _ => false)",
}

def _generate_theorem(circuit_lean: str, n_qubits: int, spec: StructuralSpec) -> str:
    """Generate a complete Lean 4 source file that states and proves a structural spec."""
    def_name = "importedCircuit"

    if spec.kind == StructSpecKind.MAX_DEPTH:
        stmt = (
            f"{def_name} ⊨ CircuitSpec.maxDepth {spec.bound}"
        )
        proof = (
            "by\n"
            "  simp [CircuitSpec.satisfies, CircuitSpec.depth,\n"
            "        CircuitSpec.scheduleDepth, CircuitSpec.gateQubits,\n"
            f"        {def_name}]\n"
        )
    else:
        pred = _GATE_PREDS[spec.kind]
        stmt = (
            f"CircuitSpec.countGates {pred} {def_name} = {spec.bound}"
        )
        # simp (with beta reduction) closes the Nat equality directly
        proof = (
            "by\n"
            f"  simp [CircuitSpec.countGates, {def_name}]\n"
        )

    return (
        "import LeanQVerify.Spec.CircuitSpec\n"
        "import LeanQVerify.QASM.Elaborator\n\n"
        "open LeanQVerify\n"
        "open LeanQVerify.QASM\n\n"
        + circuit_lean
        + "\n"
        f"theorem {def_name}_spec :\n    {stmt} :=\n{proof}"
    )


# ---------------------------------------------------------------------------
# Main API
# ---------------------------------------------------------------------------

def verify_structural_spec(
    qasm_source: str,
    spec: StructuralSpec,
    *,
    timeout: int = 120,
    lean_bin: Optional[Path] = None,
    check_bin: Optional[Path] = None,
) -> tuple[bool, str]:
    """
    Kernel-check a structural spec for a circuit given as QASM source.

    Returns (proved, log) where proved=True means Lean's kernel accepted the
    theorem.  log contains stdout+stderr from the lean invocation.
    """
    check_bin = check_bin or _find_binary()
    lean_bin  = lean_bin  or _find_lean()

    if check_bin is None:
        return False, "lean-qverify-check not found"
    if lean_bin is None:
        return False, "lean not found on PATH"

    # Step 1: get the Lean circuit definition
    with tempfile.NamedTemporaryFile(suffix=".qasm", mode="w", delete=False) as f:
        f.write(qasm_source)
        qasm_path = Path(f.name)

    try:
        proc = subprocess.run(
            [str(check_bin), "--emit-lean", str(qasm_path)],
            capture_output=True, text=True, timeout=30,
        )
    except subprocess.TimeoutExpired:
        qasm_path.unlink(missing_ok=True)
        return False, "lean-qverify-check --emit-lean timed out"
    finally:
        qasm_path.unlink(missing_ok=True)

    if proc.returncode != 0:
        return False, f"emit-lean failed:\n{proc.stderr}"

    circuit_lean = proc.stdout

    # Infer n_qubits from the def line: "QCircuit N"
    n_qubits = 0
    for line in circuit_lean.splitlines():
        if "QCircuit" in line:
            parts = line.split("QCircuit")
            if len(parts) > 1:
                tok = parts[1].strip().split()[0].rstrip(":")
                try:
                    n_qubits = int(tok)
                except ValueError:
                    pass
            break

    # Step 2: generate the theorem file
    theorem_src = _generate_theorem(circuit_lean, n_qubits, spec)

    # Step 3: find project root so we can use `lake env lean`
    project_root = _find_project_root(check_bin) if check_bin else None

    # Step 4: write theorem to a temp .lean file and kernel-check it
    # We write inside the project root so that Lean can find all imports via
    # the lake-managed LEAN_PATH.  `lake env lean <file>` sets up the path.
    with tempfile.NamedTemporaryFile(
        suffix=".lean", mode="w", delete=False, prefix="lqv_theorem_",
        dir=project_root,
    ) as f:
        f.write(theorem_src)
        lean_path = Path(f.name)

    try:
        if project_root:
            cmd = ["lake", "env", "lean", str(lean_path)]
            cwd = str(project_root)
        else:
            # Fallback: hope lean can find the packages on LEAN_PATH
            cmd = [str(lean_bin), str(lean_path)]
            cwd = None

        proc2 = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout, cwd=cwd,
        )
    except subprocess.TimeoutExpired:
        lean_path.unlink(missing_ok=True)
        return False, f"lean timed out after {timeout}s"
    except FileNotFoundError as e:
        lean_path.unlink(missing_ok=True)
        return False, f"command not found: {e}"
    finally:
        lean_path.unlink(missing_ok=True)

    log = proc2.stdout + proc2.stderr
    proved = proc2.returncode == 0 and "error:" not in log.lower()

    return proved, log
