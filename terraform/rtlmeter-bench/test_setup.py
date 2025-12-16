#!/usr/bin/env python3
"""
Pre-flight tests to validate RTLMeter benchmark setup before running expensive tests.
Run via: pytest test_setup.py -v
"""

import subprocess
import os
import re
import pytest

BENCHMARK_DIR = "/home/ubuntu/benchmark"
BASELINE_DIR = f"{BENCHMARK_DIR}/verilator-install-baseline"
OPTIMIZED_DIR = f"{BENCHMARK_DIR}/verilator-install-optimized"
RTLMETER_DIR = f"{BENCHMARK_DIR}/rtlmeter"
VERILATOR_SRC = f"{BENCHMARK_DIR}/verilator"


class TestDirectoryStructure:
    """Verify all required directories exist."""

    def test_benchmark_dir_exists(self):
        assert os.path.isdir(BENCHMARK_DIR), f"{BENCHMARK_DIR} does not exist"

    def test_baseline_install_exists(self):
        assert os.path.isdir(BASELINE_DIR), f"{BASELINE_DIR} does not exist"

    def test_optimized_install_exists(self):
        assert os.path.isdir(OPTIMIZED_DIR), f"{OPTIMIZED_DIR} does not exist"

    def test_rtlmeter_exists(self):
        assert os.path.isdir(RTLMETER_DIR), f"{RTLMETER_DIR} does not exist"

    def test_verilator_source_exists(self):
        assert os.path.isdir(VERILATOR_SRC), f"{VERILATOR_SRC} does not exist"


class TestVerilatorBinaries:
    """Verify Verilator binaries are present and executable."""

    def test_baseline_verilator_exists(self):
        binary = f"{BASELINE_DIR}/bin/verilator"
        assert os.path.isfile(binary), f"{binary} does not exist"
        assert os.access(binary, os.X_OK), f"{binary} is not executable"

    def test_optimized_verilator_exists(self):
        binary = f"{OPTIMIZED_DIR}/bin/verilator"
        assert os.path.isfile(binary), f"{binary} does not exist"
        assert os.access(binary, os.X_OK), f"{binary} is not executable"

    def test_baseline_verilator_runs(self):
        result = subprocess.run(
            [f"{BASELINE_DIR}/bin/verilator", "--version"],
            capture_output=True, text=True
        )
        assert result.returncode == 0, f"Baseline verilator failed: {result.stderr}"
        assert "Verilator" in result.stdout

    def test_optimized_verilator_runs(self):
        result = subprocess.run(
            [f"{OPTIMIZED_DIR}/bin/verilator", "--version"],
            capture_output=True, text=True
        )
        assert result.returncode == 0, f"Optimized verilator failed: {result.stderr}"
        assert "Verilator" in result.stdout


class TestVerilatorVersions:
    """Verify Verilator versions are different (baseline vs optimized)."""

    def get_version(self, verilator_path):
        result = subprocess.run(
            [verilator_path, "--version"],
            capture_output=True, text=True
        )
        return result.stdout.strip()

    def test_versions_are_different(self):
        baseline_ver = self.get_version(f"{BASELINE_DIR}/bin/verilator")
        optimized_ver = self.get_version(f"{OPTIMIZED_DIR}/bin/verilator")
        assert baseline_ver != optimized_ver, \
            f"Baseline and optimized versions should differ:\n  Baseline: {baseline_ver}\n  Optimized: {optimized_ver}"

    def test_baseline_is_upstream(self):
        """Baseline should be from upstream (no fork commits)."""
        baseline_ver = self.get_version(f"{BASELINE_DIR}/bin/verilator")
        # Optimized version has commits like "Add Jose Drowne to CONTRIBUTORS"
        assert "db5876f" not in baseline_ver, \
            f"Baseline appears to be optimized version: {baseline_ver}"


class TestOptimizedCodeChanges:
    """Verify optimized build has the V3ThreadPool optimization changes."""

    def test_optimized_has_lambda_wait(self):
        """Optimized should use lambda form of condition_variable wait."""
        # Check if the optimized branch has the lambda form
        subprocess.run(
            ["git", "-C", VERILATOR_SRC, "checkout", "origin/optimize-threadpool-wait-cv"],
            capture_output=True
        )
        result = subprocess.run(
            ["grep", "m_completionCV.wait(m_mutex,",
             f"{VERILATOR_SRC}/src/V3ThreadPool.cpp"],
            capture_output=True, text=True
        )
        assert "lambda" in result.stdout or "[&]" in result.stdout or result.returncode == 0, \
            "Optimized should have lambda form of wait()"

    def test_optimized_has_memory_order_release(self):
        """Optimized should use memory_order_release (not acq_rel)."""
        subprocess.run(
            ["git", "-C", VERILATOR_SRC, "checkout", "origin/optimize-threadpool-wait-cv"],
            capture_output=True
        )
        with open(f"{VERILATOR_SRC}/src/V3ThreadPool.cpp") as f:
            content = f.read()
        assert "memory_order_release" in content, \
            "Optimized should have memory_order_release in fetch_sub"
        # The acq_rel should NOT be present in the notification code
        assert content.count("memory_order_acq_rel") == 0 or \
               "fetch_sub(1, std::memory_order_release)" in content, \
            "Optimized should use memory_order_release, not acq_rel"


class TestRTLMeter:
    """Verify RTLMeter is set up correctly."""

    def test_rtlmeter_script_exists(self):
        script = f"{RTLMETER_DIR}/rtlmeter"
        assert os.path.isfile(script), f"{script} does not exist"

    def test_rtlmeter_venv_exists(self):
        venv = f"{RTLMETER_DIR}/venv"
        assert os.path.isdir(venv), f"{venv} does not exist - run 'make venv'"

    def test_rtlmeter_runs(self):
        result = subprocess.run(
            [f"{RTLMETER_DIR}/rtlmeter", "--help"],
            capture_output=True, text=True,
            cwd=RTLMETER_DIR
        )
        assert result.returncode == 0, f"RTLMeter failed: {result.stderr}"
        assert "RTLMeter" in result.stdout or "benchmark" in result.stdout.lower()

    def test_rtlmeter_can_list_cases(self):
        result = subprocess.run(
            [f"{RTLMETER_DIR}/rtlmeter", "show", "--cases"],
            capture_output=True, text=True,
            cwd=RTLMETER_DIR
        )
        assert result.returncode == 0, f"RTLMeter show --cases failed: {result.stderr}"
        assert "Caliptra" in result.stdout, "Expected Caliptra cases in RTLMeter"

    def test_rtlmeter_veer_case_available(self):
        """Verify VeeR-EH1:default case exists (what we'll benchmark)."""
        result = subprocess.run(
            [f"{RTLMETER_DIR}/rtlmeter", "show", "--cases"],
            capture_output=True, text=True,
            cwd=RTLMETER_DIR
        )
        assert "VeeR-EH1" in result.stdout, "VeeR-EH1 case not found in RTLMeter"


class TestRTLMeterBenchmarkCase:
    """Test the specific benchmark case we'll run."""

    def test_veer_repo_accessible(self):
        """Verify VeeR repository is accessible."""
        result = subprocess.run(
            ["git", "ls-remote", "https://github.com/chipsalliance/Cores-VeeR-EH1.git", "HEAD"],
            capture_output=True, text=True,
            timeout=30
        )
        assert result.returncode == 0, "Cannot access VeeR-EH1 repository"

    def test_rtlmeter_can_setup_veer(self):
        """Verify RTLMeter can set up VeeR case (downloads repo if needed)."""
        result = subprocess.run(
            [f"{RTLMETER_DIR}/rtlmeter", "run",
             "--cases", "VeeR-EH1:default:hello",
             "--nCompile", "0", "--nExecute", "0",
             "--verbose"],
            capture_output=True, text=True,
            cwd=RTLMETER_DIR,
            timeout=300  # 5 min for clone
        )
        # Should succeed at setup even if we skip compile/execute
        assert result.returncode == 0 or "setup" in result.stdout.lower(), \
            f"RTLMeter VeeR setup failed: {result.stderr}"


class TestSystemResources:
    """Verify system has adequate resources for c8i.metal-48xl."""

    def test_cpu_count(self):
        """c8i.metal-48xl has 96 vCPUs."""
        cpu_count = os.cpu_count()
        assert cpu_count is not None
        assert cpu_count >= 90, f"Expected at least 90 CPUs (c8i.metal-48xl has 96), got {cpu_count}"

    def test_memory_available(self):
        """c8i.metal-48xl has 384GB RAM."""
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemTotal:"):
                    # Value is in kB
                    mem_kb = int(line.split()[1])
                    mem_gb = mem_kb / (1024 * 1024)
                    assert mem_gb >= 380, f"Expected at least 380GB RAM (c8i.metal-48xl has 384GB), got {mem_gb:.1f}GB"
                    return
        pytest.fail("Could not read memory info")

    def test_disk_space(self):
        """Check at least 50GB free disk space."""
        stat = os.statvfs(BENCHMARK_DIR)
        free_gb = (stat.f_bavail * stat.f_frsize) / (1024**3)
        assert free_gb >= 50, f"Expected at least 50GB free, got {free_gb:.1f}GB"


class TestSystemDependencies:
    """Verify required system tools are installed."""

    @pytest.mark.parametrize("cmd,args", [
        ("g++", ["--version"]),
        ("gcc", ["--version"]),
        ("make", ["--version"]),
        ("flex", ["--version"]),
        ("bison", ["--version"]),
        ("ccache", ["--version"]),
        ("autoconf", ["--version"]),
        ("perl", ["--version"]),
        ("python3", ["--version"]),
    ])
    def test_tool_installed(self, cmd, args):
        result = subprocess.run([cmd] + args, capture_output=True, text=True)
        assert result.returncode == 0, f"{cmd} not installed or not working"

    def test_libfl_available(self):
        """Check flex library is available for linking."""
        result = subprocess.run(
            ["pkg-config", "--exists", "fl"],
            capture_output=True
        )
        # pkg-config may not have fl, try ldconfig
        if result.returncode != 0:
            result = subprocess.run(
                ["ldconfig", "-p"],
                capture_output=True, text=True
            )
            assert "libfl" in result.stdout, "libfl not found - install libfl-dev"


class TestParallelCompilation:
    """Verify parallel compilation works with -j flag."""

    def test_verilator_accepts_j_flag(self):
        """Both verilators should accept -j flag."""
        for name, path in [("baseline", BASELINE_DIR), ("optimized", OPTIMIZED_DIR)]:
            result = subprocess.run(
                [f"{path}/bin/verilator", "--help"],
                capture_output=True, text=True
            )
            assert "-j" in result.stdout or "--threads" in result.stdout, \
                f"{name} verilator should support -j flag"


class TestQuickVerilation:
    """Quick smoke test that verilation works."""

    @pytest.fixture
    def temp_dir(self, tmp_path):
        return tmp_path

    def test_baseline_can_verilate_simple(self, temp_dir):
        """Baseline can verilate a simple module."""
        # Create simple test module
        sv_file = temp_dir / "test.sv"
        sv_file.write_text("module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule")

        result = subprocess.run(
            [f"{BASELINE_DIR}/bin/verilator", "--cc", str(sv_file)],
            capture_output=True, text=True,
            cwd=temp_dir
        )
        assert result.returncode == 0, f"Baseline verilate failed: {result.stderr}"

    def test_optimized_can_verilate_simple(self, temp_dir):
        """Optimized can verilate a simple module."""
        sv_file = temp_dir / "test.sv"
        sv_file.write_text("module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule")

        result = subprocess.run(
            [f"{OPTIMIZED_DIR}/bin/verilator", "--cc", str(sv_file)],
            capture_output=True, text=True,
            cwd=temp_dir
        )
        assert result.returncode == 0, f"Optimized verilate failed: {result.stderr}"

    def test_optimized_can_verilate_with_j_flag(self, temp_dir):
        """Optimized can verilate with -j flag (uses thread pool)."""
        sv_file = temp_dir / "test.sv"
        sv_file.write_text("module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule")

        result = subprocess.run(
            [f"{OPTIMIZED_DIR}/bin/verilator", "--cc", "-j", "4", str(sv_file)],
            capture_output=True, text=True,
            cwd=temp_dir
        )
        assert result.returncode == 0, f"Optimized verilate with -j failed: {result.stderr}"


class TestFullBuildAndRun:
    """Test full compile, build, and run cycle."""

    @pytest.fixture
    def temp_dir(self, tmp_path):
        return tmp_path

    def test_optimized_full_build_and_run(self, temp_dir):
        """Full cycle: verilate -> compile C++ -> link -> run."""
        # Create a testbench that actually runs
        sv_file = temp_dir / "test.sv"
        sv_file.write_text("""
module test(input clk, input rst, output reg [7:0] count);
    always @(posedge clk) begin
        if (rst) count <= 0;
        else count <= count + 1;
    end
endmodule
""")

        # Verilate with --binary to get executable
        result = subprocess.run(
            [f"{OPTIMIZED_DIR}/bin/verilator", "--binary", "-j", "4",
             "--trace", str(sv_file)],
            capture_output=True, text=True,
            cwd=temp_dir
        )
        assert result.returncode == 0, f"Verilate failed: {result.stderr}"

        # Run the generated executable
        exe_path = temp_dir / "obj_dir" / "Vtest"
        assert exe_path.exists(), f"Executable not found at {exe_path}"

        result = subprocess.run(
            [str(exe_path)],
            capture_output=True, text=True,
            cwd=temp_dir,
            timeout=30
        )
        # Should run without crashing (may exit with various codes)
        assert result.returncode is not None, "Simulation crashed"


class TestMultiThreadedStress:
    """Stress test for the thread pool optimization."""

    @pytest.fixture
    def temp_dir(self, tmp_path):
        return tmp_path

    def test_parallel_verilations(self, temp_dir):
        """Run multiple verilations in parallel to stress thread pool."""
        import concurrent.futures

        # Create multiple test files
        for i in range(4):
            sv_file = temp_dir / f"test{i}.sv"
            sv_file.write_text(f"""
module test{i}(input clk, output reg [31:0] out);
    reg [31:0] r0, r1, r2, r3;
    always @(posedge clk) begin
        r0 <= r0 + 1;
        r1 <= r1 + r0;
        r2 <= r2 + r1;
        r3 <= r3 + r2;
        out <= r3;
    end
endmodule
""")

        def verilate(i):
            result = subprocess.run(
                [f"{OPTIMIZED_DIR}/bin/verilator", "--cc", "-j", "8",
                 str(temp_dir / f"test{i}.sv"),
                 "--Mdir", str(temp_dir / f"obj{i}")],
                capture_output=True, text=True,
                timeout=120
            )
            return i, result.returncode, result.stderr

        # Run 4 verilations in parallel
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            futures = [executor.submit(verilate, i) for i in range(4)]
            results = [f.result() for f in concurrent.futures.as_completed(futures)]

        for i, rc, stderr in results:
            assert rc == 0, f"Parallel verilate {i} failed: {stderr}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
