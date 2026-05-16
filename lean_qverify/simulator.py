"""
GPU-aware simulator selector.

Picks the right AerSimulator backend based on circuit size and GPU availability.
All callers should obtain a simulator through `get_simulator()` rather than
constructing AerSimulator directly.
"""

from __future__ import annotations

import logging
from typing import Optional

from .gpu import GPUInfo, detect_gpu, should_use_gpu

logger = logging.getLogger(__name__)

_gpu_cache: Optional[GPUInfo] = None


def _cached_gpu_info() -> GPUInfo:
    global _gpu_cache
    if _gpu_cache is None:
        _gpu_cache = detect_gpu()
        if _gpu_cache.available:
            logger.info("GPU detected: %s", _gpu_cache.device_name)
        else:
            logger.debug("GPU not available (%s), using CPU", _gpu_cache.reason)
    return _gpu_cache


def get_simulator(n_qubits: int):
    """
    Return an AerSimulator configured for the given qubit count.

    - For n_qubits >= 20 and GPU available: statevector on GPU.
    - Otherwise: statevector on CPU.

    Returns an AerSimulator instance ready to run circuits.
    """
    from qiskit_aer import AerSimulator  # type: ignore

    gpu_info = _cached_gpu_info()
    if should_use_gpu(n_qubits, gpu_info):
        logger.debug("Using GPU simulator for %d-qubit circuit", n_qubits)
        return AerSimulator(method="statevector", device="GPU")
    else:
        logger.debug("Using CPU simulator for %d-qubit circuit", n_qubits)
        return AerSimulator(method="statevector", device="CPU")


def unitary_simulator():
    """Return an AerSimulator configured for unitary extraction (always CPU)."""
    from qiskit_aer import AerSimulator  # type: ignore
    return AerSimulator(method="unitary")
