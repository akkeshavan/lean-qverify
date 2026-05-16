"""
Tests for GPU detection and simulator selection.

These tests are designed to pass on CPU-only machines (including Mac).
GPU-specific tests are skipped automatically when no CUDA device is present.
"""

import pytest
from lean_qverify.gpu import detect_gpu, should_use_gpu, GPUInfo, GPU_QUBIT_THRESHOLD


def test_detect_gpu_returns_gpu_info():
    info = detect_gpu()
    assert isinstance(info, GPUInfo)
    assert isinstance(info.available, bool)


def test_detect_gpu_unavailable_has_reason():
    info = detect_gpu()
    if not info.available:
        assert info.reason is not None
        assert len(info.reason) > 0


def test_should_use_gpu_below_threshold_is_false():
    # Even with GPU available, small circuits should use CPU
    gpu_info = GPUInfo(available=True, device_name="Test GPU")
    assert should_use_gpu(GPU_QUBIT_THRESHOLD - 1, gpu_info) is False


def test_should_use_gpu_at_threshold_is_true():
    gpu_info = GPUInfo(available=True, device_name="Test GPU")
    assert should_use_gpu(GPU_QUBIT_THRESHOLD, gpu_info) is True


def test_should_use_gpu_no_gpu_always_false():
    gpu_info = GPUInfo(available=False, reason="no gpu")
    assert should_use_gpu(100, gpu_info) is False


def test_simulator_cpu_small_circuit():
    """get_simulator for a small circuit should return a CPU simulator."""
    pytest.importorskip("qiskit_aer")
    from lean_qverify.simulator import get_simulator
    sim = get_simulator(4)
    assert sim is not None


@pytest.mark.skipif(
    not detect_gpu().available,
    reason="No CUDA GPU available on this machine"
)
def test_simulator_gpu_large_circuit():
    """get_simulator for a large circuit should return a GPU simulator when available."""
    from lean_qverify.simulator import get_simulator
    sim = get_simulator(25)
    assert sim is not None
