#!/usr/bin/env python3
"""
Post-deployment integration tests.

These tests verify that the deployed EC2 instance is set up correctly.
They run locally but execute commands on EC2 via SSM.

Requires: EC2 instance provisioned via terraform apply

Run with: pytest test_post_deploy_integration.py -v
"""

import pytest


@pytest.mark.remote
class TestDirectoryStructure:
    """Verify required directories exist on EC2."""

    def test_benchmark_dir_exists(self, require_ssm, benchmark_dir):
        """Main benchmark directory exists."""
        assert require_ssm.dir_exists(benchmark_dir), \
            f"Directory not found: {benchmark_dir}"

    def test_baseline_install_dir_exists(self, require_ssm, baseline_dir):
        """Baseline Verilator install directory exists."""
        assert require_ssm.dir_exists(baseline_dir), \
            f"Directory not found: {baseline_dir}"

    def test_optimized_install_dir_exists(self, require_ssm, optimized_dir):
        """Optimized Verilator install directory exists."""
        assert require_ssm.dir_exists(optimized_dir), \
            f"Directory not found: {optimized_dir}"

    def test_rtlmeter_dir_exists(self, require_ssm, rtlmeter_dir):
        """RTLMeter directory exists."""
        assert require_ssm.dir_exists(rtlmeter_dir), \
            f"Directory not found: {rtlmeter_dir}"

    def test_verilator_source_dir_exists(self, require_ssm, verilator_src):
        """Verilator source directory exists."""
        assert require_ssm.dir_exists(verilator_src), \
            f"Directory not found: {verilator_src}"


@pytest.mark.remote
class TestVerilatorBinaries:
    """Verify Verilator binaries are installed and executable."""

    def test_baseline_binary_exists(self, require_ssm, baseline_dir):
        """Baseline verilator binary exists."""
        assert require_ssm.file_exists(f"{baseline_dir}/bin/verilator"), \
            "Baseline verilator binary not found"

    def test_optimized_binary_exists(self, require_ssm, optimized_dir):
        """Optimized verilator binary exists."""
        assert require_ssm.file_exists(f"{optimized_dir}/bin/verilator"), \
            "Optimized verilator binary not found"

    def test_baseline_binary_executes(self, require_ssm, baseline_dir):
        """Baseline verilator binary executes successfully."""
        stdout, _ = require_ssm.run_check(f"{baseline_dir}/bin/verilator --version")
        assert "Verilator" in stdout, "Unexpected verilator output"

    def test_optimized_binary_executes(self, require_ssm, optimized_dir):
        """Optimized verilator binary executes successfully."""
        stdout, _ = require_ssm.run_check(f"{optimized_dir}/bin/verilator --version")
        assert "Verilator" in stdout, "Unexpected verilator output"


@pytest.mark.remote
class TestVerilatorVersions:
    """Verify baseline and optimized Verilator versions are different."""

    def test_versions_differ(self, require_ssm, baseline_dir, optimized_dir):
        """Baseline and optimized must have different versions."""
        baseline_out, _ = require_ssm.run_check(
            f"{baseline_dir}/bin/verilator --version"
        )
        optimized_out, _ = require_ssm.run_check(
            f"{optimized_dir}/bin/verilator --version"
        )

        baseline_ver = baseline_out.strip()
        optimized_ver = optimized_out.strip()

        assert baseline_ver != optimized_ver, \
            f"Versions should differ:\n  Baseline:  {baseline_ver}\n  Optimized: {optimized_ver}"

        print(f"\n  Baseline:  {baseline_ver}")
        print(f"  Optimized: {optimized_ver}")


@pytest.mark.remote
class TestRTLMeterSetup:
    """Verify RTLMeter is installed and configured."""

    def test_rtlmeter_script_exists(self, require_ssm, rtlmeter_dir):
        """RTLMeter script exists."""
        assert require_ssm.file_exists(f"{rtlmeter_dir}/rtlmeter"), \
            "RTLMeter script not found"

    def test_rtlmeter_venv_exists(self, require_ssm, rtlmeter_dir):
        """RTLMeter virtual environment exists."""
        assert require_ssm.dir_exists(f"{rtlmeter_dir}/venv"), \
            "RTLMeter venv not found - run 'make venv'"

    def test_rtlmeter_executes(self, require_ssm, rtlmeter_dir):
        """RTLMeter executes and shows help."""
        stdout, _ = require_ssm.run_check(f"cd {rtlmeter_dir} && ./rtlmeter --help")
        assert "rtlmeter" in stdout.lower() or "usage" in stdout.lower(), \
            "Unexpected RTLMeter output"

    def test_rtlmeter_can_list_cases(self, require_ssm, rtlmeter_dir):
        """RTLMeter can list benchmark cases."""
        stdout, _ = require_ssm.run_check(
            f"cd {rtlmeter_dir} && ./rtlmeter show --cases"
        )
        assert "VeeR" in stdout or "Caliptra" in stdout, \
            "Expected benchmark cases not found"


@pytest.mark.remote
class TestSystemResources:
    """Verify EC2 instance has expected resources."""

    def test_cpu_count(self, require_ssm):
        """c8i.metal-48xl should have 192 vCPUs."""
        stdout, _ = require_ssm.run_check("nproc")
        cpu_count = int(stdout.strip())
        assert cpu_count >= 190, \
            f"Expected ~192 vCPUs, got {cpu_count}"
        print(f"\n  CPU count: {cpu_count}")

    def test_memory_size(self, require_ssm):
        """c8i.metal-48xl should have ~384GB RAM."""
        stdout, _ = require_ssm.run_check(
            "grep MemTotal /proc/meminfo | awk '{print $2}'"
        )
        mem_kb = int(stdout.strip())
        mem_gb = mem_kb / (1024 * 1024)
        assert mem_gb >= 370, \
            f"Expected ~384GB RAM, got {mem_gb:.1f}GB"
        print(f"\n  Memory: {mem_gb:.1f}GB")

    def test_disk_space(self, require_ssm, benchmark_dir):
        """Sufficient disk space must be available."""
        stdout, _ = require_ssm.run_check(
            f"df -BG {benchmark_dir} | tail -1 | awk '{{print $4}}'"
        )
        free_gb = int(stdout.strip().rstrip('G'))
        assert free_gb >= 50, \
            f"Expected 50GB+ free, got {free_gb}GB"
        print(f"\n  Free disk: {free_gb}GB")


@pytest.mark.remote
class TestBuildDependencies:
    """Verify build dependencies are installed on EC2."""

    @pytest.mark.parametrize("cmd", [
        "g++ --version",
        "make --version",
        "flex --version",
        "bison --version",
        "ccache --version",
        "autoconf --version",
        "perl --version",
        "python3 --version",
    ])
    def test_tool_installed(self, require_ssm, cmd):
        """Build tool is installed and executable."""
        require_ssm.run_check(cmd)


@pytest.mark.remote
class TestVerilationSmoke:
    """Quick smoke tests to verify Verilator can verilate."""

    def test_baseline_verilates_simple_module(self, require_ssm, baseline_dir):
        """Baseline can verilate a simple module."""
        cmd = f"""
cd /tmp && rm -rf verilate_test && mkdir verilate_test && cd verilate_test &&
echo 'module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule' > test.sv &&
{baseline_dir}/bin/verilator --cc test.sv
"""
        require_ssm.run_check(cmd, timeout=60)

    def test_optimized_verilates_simple_module(self, require_ssm, optimized_dir):
        """Optimized can verilate a simple module."""
        cmd = f"""
cd /tmp && rm -rf verilate_test && mkdir verilate_test && cd verilate_test &&
echo 'module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule' > test.sv &&
{optimized_dir}/bin/verilator --cc test.sv
"""
        require_ssm.run_check(cmd, timeout=60)

    def test_optimized_verilates_with_threads(self, require_ssm, optimized_dir):
        """Optimized can verilate with threading enabled."""
        cmd = f"""
cd /tmp && rm -rf verilate_test && mkdir verilate_test && cd verilate_test &&
echo 'module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule' > test.sv &&
{optimized_dir}/bin/verilator --cc -j 4 test.sv
"""
        require_ssm.run_check(cmd, timeout=60)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
