"""
GPU detection and capability checking for lean-qverify.

Detects whether a CUDA-capable GPU with qiskit-aer-gpu is available.
Falls back to CPU silently. GPU is only beneficial for circuits with
20+ qubits due to PCIe transfer overhead at smaller sizes.
"""

from __future__ import annotations

import subprocess
import importlib
import logging
from dataclasses import dataclass
from typing import Optional

logger = logging.getLogger(__name__)

GPU_QUBIT_THRESHOLD = 20  # below this, CPU is faster


@dataclass(frozen=True)
class GPUInfo:
    available: bool
    device_name: Optional[str] = None
    reason: Optional[str] = None   # why unavailable, if applicable


def _nvidia_smi_present() -> Optional[str]:
    """Return GPU name from nvidia-smi, or None if not present."""
    try:
        result = subprocess.run(
            ["nvidia-smi", "--query-gpu=name", "--format=csv,noheader"],
            capture_output=True, text=True, timeout=5
        )
        if result.returncode == 0:
            name = result.stdout.strip().splitlines()[0].strip()
            return name if name else None
    except (FileNotFoundError, subprocess.TimeoutExpired, IndexError):
        pass
    return None


def _aer_gpu_functional() -> bool:
    """Check that qiskit-aer-gpu is importable and AerSimulator works on GPU."""
    try:
        from qiskit_aer import AerSimulator  # type: ignore
        sim = AerSimulator(method="statevector", device="GPU")
        # Run a minimal 1-qubit circuit as a smoke test
        from qiskit import QuantumCircuit  # type: ignore
        qc = QuantumCircuit(1)
        qc.h(0)
        qc.measure_all()
        job = sim.run(qc, shots=1)
        job.result()
        return True
    except Exception as exc:
        logger.debug("GPU smoke test failed: %s", exc)
        return False


def detect_gpu() -> GPUInfo:
    """
    Probe for a usable CUDA GPU.

    Checks in order:
    1. nvidia-smi is present and reports a GPU.
    2. qiskit-aer-gpu is installed.
    3. AerSimulator can actually run a circuit on the GPU.

    Returns a GPUInfo indicating availability and device name.
    """
    device_name = _nvidia_smi_present()
    if device_name is None:
        return GPUInfo(available=False, reason="nvidia-smi not found or no GPU reported")

    if importlib.util.find_spec("qiskit_aer") is None:
        return GPUInfo(
            available=False,
            device_name=device_name,
            reason="qiskit-aer not installed",
        )

    # Check for GPU-enabled build of qiskit-aer
    try:
        from qiskit_aer import AerSimulator  # type: ignore
        available_methods = AerSimulator().available_devices()
        if "GPU" not in available_methods:
            return GPUInfo(
                available=False,
                device_name=device_name,
                reason="qiskit-aer installed but not the GPU build (qiskit-aer-gpu)",
            )
    except Exception as exc:
        return GPUInfo(
            available=False,
            device_name=device_name,
            reason=f"AerSimulator device check failed: {exc}",
        )

    if not _aer_gpu_functional():
        return GPUInfo(
            available=False,
            device_name=device_name,
            reason="GPU smoke test failed — check CUDA driver compatibility",
        )

    return GPUInfo(available=True, device_name=device_name)


def should_use_gpu(n_qubits: int, gpu_info: Optional[GPUInfo] = None) -> bool:
    """
    Return True if GPU should be used for a circuit of the given qubit count.

    Below GPU_QUBIT_THRESHOLD qubits, CPU is faster due to transfer overhead.
    """
    if gpu_info is None:
        gpu_info = detect_gpu()
    return gpu_info.available and n_qubits >= GPU_QUBIT_THRESHOLD
