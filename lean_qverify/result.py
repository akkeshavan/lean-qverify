"""
Verification result types returned by the lean-qverify bridge.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional
from enum import Enum


class Verdict(Enum):
    PROVED         = "proved"          # Lean kernel checked a theorem against a spec
    STRUCT_PROVED  = "struct_proved"   # Structural spec kernel-checked (gate count, depth, etc.)
    PARSED         = "parsed"          # Circuit parsed and elaborated; no spec checked
    FAILED         = "failed"          # Lean rejected (or counterexample found)
    WARNING        = "warning"         # Parsed, but unrecognised gates or unverified angles
    ERROR          = "error"           # Could not parse / elaborate / run Lean


@dataclass
class CounterExample:
    """A concrete input state and expected vs. actual output that witnesses a spec violation."""
    input_state: str          # human-readable description, e.g. "|00>"
    expected:    str
    actual:      str
    note:        str = ""


@dataclass
class VerifyResult:
    verdict:      Verdict
    n_qubits:     int                     = 0
    n_gates:      int                     = 0
    warnings:     list[str]               = field(default_factory=list)
    counterexample: Optional[CounterExample] = None
    lean_output:  str                     = ""   # raw stdout/stderr from lean-qverify-check
    error_msg:    str                     = ""

    @property
    def ok(self) -> bool:
        """True if the operation succeeded (no error or failure)."""
        return self.verdict in (
            Verdict.PROVED, Verdict.STRUCT_PROVED, Verdict.PARSED, Verdict.WARNING
        )

    @property
    def kernel_checked(self) -> bool:
        """True only when Lean's kernel has verified a theorem, not just parsed."""
        return self.verdict in (Verdict.PROVED, Verdict.STRUCT_PROVED)

    def __str__(self) -> str:
        lines = [f"Verdict: {self.verdict.value}"]
        if self.n_qubits:
            lines.append(f"  Qubits: {self.n_qubits}, Gates: {self.n_gates}")
        for w in self.warnings:
            lines.append(f"  Warning: {w}")
        if self.counterexample:
            ce = self.counterexample
            lines.append(f"  Counterexample: input={ce.input_state}, "
                         f"expected={ce.expected}, actual={ce.actual}")
            if ce.note:
                lines.append(f"    Note: {ce.note}")
        if self.error_msg:
            lines.append(f"  Error: {self.error_msg}")
        return "\n".join(lines)
