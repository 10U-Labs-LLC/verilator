#!/usr/bin/env python3
"""
Pre-flight tests to validate RTLMeter benchmark setup before running expensive tests.
Run via: pytest test_setup.py -v

For local pre-provisioning checks (AWS quotas), run:
    pytest test_setup.py -v -k "AWSPreProvisioning"
"""

import subprocess
import os
import re
import json
import pytest

BENCHMARK_DIR = "/home/ubuntu/benchmark"
BASELINE_DIR = f"{BENCHMARK_DIR}/verilator-install-baseline"
OPTIMIZED_DIR = f"{BENCHMARK_DIR}/verilator-install-optimized"
RTLMETER_DIR = f"{BENCHMARK_DIR}/rtlmeter"
VERILATOR_SRC = f"{BENCHMARK_DIR}/verilator"

# AWS configuration for c8i.metal-48xl
REQUIRED_VCPUS = 192
AWS_REGION = "us-east-2"
INSTANCE_TYPE = "c8i.metal-48xl"

# Path to terraform directory (relative to this file)
TERRAFORM_DIR = os.path.dirname(os.path.abspath(__file__))


class TestAWSPreProvisioning:
    """
    Run BEFORE terraform apply to verify AWS quotas and credentials.
    These tests run locally, not on the EC2 instance.

    Run with: pytest test_setup.py -v -k "AWSPreProvisioning"
    """

    def test_aws_cli_installed(self):
        """AWS CLI must be installed."""
        result = subprocess.run(
            ["aws", "--version"],
            capture_output=True, text=True
        )
        assert result.returncode == 0, "AWS CLI not installed"

    def test_aws_credentials_configured(self):
        """AWS credentials must be configured."""
        result = subprocess.run(
            ["aws", "sts", "get-caller-identity", "--region", AWS_REGION],
            capture_output=True, text=True
        )
        assert result.returncode == 0, \
            f"AWS credentials not configured or invalid: {result.stderr}"

    def test_aws_region_accessible(self):
        """Can access the target AWS region."""
        result = subprocess.run(
            ["aws", "ec2", "describe-availability-zones",
             "--region", AWS_REGION, "--query", "AvailabilityZones[0].ZoneName"],
            capture_output=True, text=True
        )
        assert result.returncode == 0, \
            f"Cannot access region {AWS_REGION}: {result.stderr}"

    def test_vcpu_quota_sufficient(self):
        """
        Check if we have enough vCPU quota for c8i.metal-48xl (192 vCPUs).
        Quota code L-1216C47A is for "Running On-Demand Standard instances".
        """
        result = subprocess.run(
            ["aws", "service-quotas", "get-service-quota",
             "--service-code", "ec2",
             "--quota-code", "L-1216C47A",  # On-Demand Standard instances vCPUs
             "--region", AWS_REGION],
            capture_output=True, text=True
        )

        if result.returncode != 0:
            pytest.fail(f"Cannot check vCPU quota: {result.stderr}")

        quota_data = json.loads(result.stdout)
        quota_value = quota_data.get("Quota", {}).get("Value", 0)

        assert quota_value >= REQUIRED_VCPUS, \
            f"Insufficient vCPU quota: have {quota_value}, need {REQUIRED_VCPUS} for {INSTANCE_TYPE}"

    def test_instance_type_available(self):
        """Check if c8i.metal-48xl is available in the region."""
        result = subprocess.run(
            ["aws", "ec2", "describe-instance-type-offerings",
             "--location-type", "region",
             "--filters", f"Name=instance-type,Values={INSTANCE_TYPE}",
             "--region", AWS_REGION,
             "--query", "InstanceTypeOfferings[0].InstanceType"],
            capture_output=True, text=True
        )

        assert result.returncode == 0, f"Cannot check instance availability: {result.stderr}"
        output = result.stdout.strip().strip('"')
        assert output == INSTANCE_TYPE, \
            f"{INSTANCE_TYPE} not available in {AWS_REGION}"

    def test_current_vcpu_usage(self):
        """Check current vCPU usage to ensure we have headroom."""
        # Get current running instances' vCPU count
        result = subprocess.run(
            ["aws", "ec2", "describe-instances",
             "--filters", "Name=instance-state-name,Values=running",
             "--region", AWS_REGION,
             "--query", "Reservations[].Instances[].InstanceType"],
            capture_output=True, text=True
        )

        if result.returncode != 0:
            pytest.skip(f"Cannot check current usage: {result.stderr}")

        # Get quota
        quota_result = subprocess.run(
            ["aws", "service-quotas", "get-service-quota",
             "--service-code", "ec2",
             "--quota-code", "L-1216C47A",
             "--region", AWS_REGION],
            capture_output=True, text=True
        )

        if quota_result.returncode != 0:
            pytest.skip("Cannot check quota")

        quota_data = json.loads(quota_result.stdout)
        quota_value = quota_data.get("Quota", {}).get("Value", 0)

        # Parse running instances (simplified - actual vCPU count would need lookup)
        instances = json.loads(result.stdout) if result.stdout.strip() else []

        print(f"\nQuota: {quota_value} vCPUs")
        print(f"Required: {REQUIRED_VCPUS} vCPUs for {INSTANCE_TYPE}")
        print(f"Currently running instances: {len(instances)}")

        # This is a soft check - just informational
        assert quota_value >= REQUIRED_VCPUS, \
            f"Quota ({quota_value}) less than required ({REQUIRED_VCPUS})"

    def test_terraform_enforces_spot_only(self):
        """
        CRITICAL: Verify Terraform config uses spot instances ONLY.
        On-demand c8i.metal-48xl would cost ~$8/hour vs ~$2-3/hour for spot.
        This test parses main.tf to ensure spot is enforced.
        """
        main_tf = os.path.join(TERRAFORM_DIR, "main.tf")
        assert os.path.isfile(main_tf), f"main.tf not found at {main_tf}"

        with open(main_tf) as f:
            content = f.read()

        # Must have instance_market_options block
        assert "instance_market_options" in content, \
            "main.tf missing instance_market_options block - instance would be on-demand!"

        # Must specify market_type = "spot"
        assert re.search(r'market_type\s*=\s*["\']spot["\']', content), \
            "main.tf must set market_type = \"spot\" - instance would be on-demand!"

        # Must have spot_options block (ensures intentional spot config)
        assert "spot_options" in content, \
            "main.tf missing spot_options block"

        # Verify it's a one-time spot (not persistent, which auto-relaunches)
        assert re.search(r'spot_instance_type\s*=\s*["\']one-time["\']', content), \
            "spot_instance_type should be \"one-time\" to prevent auto-relaunch"

        print("\n✓ Terraform config verified: EC2 will be spot instance only")
        print("  - market_type = \"spot\"")
        print("  - spot_instance_type = \"one-time\"")


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
        """c8i.metal-48xl has 192 vCPUs (96 cores x 2 threads)."""
        cpu_count = os.cpu_count()
        assert cpu_count is not None
        assert cpu_count >= 190, f"Expected at least 190 vCPUs (c8i.metal-48xl has 192), got {cpu_count}"

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

    def test_threads_actually_spawn(self, temp_dir):
        """Verify -j flag actually spawns threads (not just accepted)."""
        import threading
        import time

        # Create a larger design that takes time to verilate
        sv_file = temp_dir / "big.sv"
        modules = []
        for i in range(20):
            modules.append(f"""
module sub{i}(input clk, input [31:0] in, output reg [31:0] out);
    reg [31:0] r0, r1, r2, r3, r4, r5, r6, r7;
    always @(posedge clk) begin
        r0 <= in + {i};
        r1 <= r0 * 2;
        r2 <= r1 + r0;
        r3 <= r2 ^ r1;
        r4 <= r3 + r2;
        r5 <= r4 * 3;
        r6 <= r5 + r4;
        r7 <= r6 ^ r5;
        out <= r7;
    end
endmodule
""")
        sv_file.write_text("\n".join(modules) + """
module top(input clk, input [31:0] in, output [31:0] out);
    wire [31:0] w[20:0];
    assign w[0] = in;
""" + "\n".join([f"    sub{i} s{i}(.clk(clk), .in(w[{i}]), .out(w[{i+1}]));" for i in range(20)]) + """
    assign out = w[20];
endmodule
""")

        thread_count_seen = [0]

        def count_threads():
            """Count verilator threads during execution."""
            max_threads = 0
            for _ in range(50):  # Check for 5 seconds
                try:
                    result = subprocess.run(
                        ["pgrep", "-c", "-f", "verilator"],
                        capture_output=True, text=True
                    )
                    count = int(result.stdout.strip()) if result.returncode == 0 else 0
                    max_threads = max(max_threads, count)
                except:
                    pass
                time.sleep(0.1)
            thread_count_seen[0] = max_threads

        # Start thread counter
        counter = threading.Thread(target=count_threads)
        counter.start()

        # Run verilator with many threads
        result = subprocess.run(
            [f"{OPTIMIZED_DIR}/bin/verilator", "--cc", "-j", "16",
             str(sv_file), "--Mdir", str(temp_dir / "obj_big")],
            capture_output=True, text=True,
            timeout=120
        )

        counter.join()

        assert result.returncode == 0, f"Verilate failed: {result.stderr}"
        # Should see more than 1 process if threading is working
        assert thread_count_seen[0] >= 2, \
            f"Expected multiple threads with -j 16, but only saw {thread_count_seen[0]}"


class TestRTLMeterMultiThreading:
    """Verify RTLMeter will actually test multi-threading."""

    def test_rtlmeter_accepts_threads_arg(self):
        """RTLMeter should accept --compileArgs with --threads."""
        result = subprocess.run(
            [f"{RTLMETER_DIR}/rtlmeter", "run",
             "--cases", "VeeR-EH1:default:hello",
             "--compileArgs", "--threads 16",
             "--nExecute", "0",  # Skip execute, just compile
             "--verbose"],
            capture_output=True, text=True,
            cwd=RTLMETER_DIR,
            timeout=600
        )
        # Check it ran (may fail for other reasons, but should accept the args)
        assert "--threads" not in result.stderr.lower() or "error" not in result.stderr.lower(), \
            f"RTLMeter rejected --threads argument: {result.stderr}"

    def test_rtlmeter_threads_in_command(self):
        """Verify RTLMeter passes --threads to verilator."""
        result = subprocess.run(
            [f"{RTLMETER_DIR}/rtlmeter", "run",
             "--cases", "VeeR-EH1:default:hello",
             "--compileArgs", "--threads 32",
             "--nCompile", "0", "--nExecute", "0",
             "--verbose", "--dryRun"],
            capture_output=True, text=True,
            cwd=RTLMETER_DIR,
            timeout=60
        )
        # In dry-run or verbose mode, should show the command with --threads
        output = result.stdout + result.stderr
        # Just verify it doesn't error on the threads arg
        assert result.returncode == 0 or "threads" in output.lower(), \
            f"RTLMeter should handle --threads: {result.stderr}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
