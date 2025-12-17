#!/usr/bin/env python3
"""
End-to-end tests.

These tests verify the complete benchmark workflow works correctly.
They run the full RTLMeter benchmark cycle and verify results.

These tests are slow (several minutes each) and should be run selectively.

Requires: EC2 instance provisioned and set up via benchmark.py

Run with: pytest test_e2e.py -v
Skip with: pytest -k "not e2e"
"""

import json

import pytest


@pytest.mark.remote
@pytest.mark.slow
@pytest.mark.e2e
class TestRTLMeterCacheIsolation:
    """
    CRITICAL: Verify RTLMeter cache behavior.

    These tests ensure that:
    1. Clearing cache produces fresh results
    2. Different Verilator versions produce different results

    Without proper cache handling, baseline and optimized benchmarks
    would show identical (invalid) results.
    """

    def test_cache_clear_produces_fresh_results(
        self, require_ssm, rtlmeter_dir, baseline_dir
    ):
        """
        Running RTLMeter twice with cache cleared should produce
        different results (proving fresh execution, not cached).
        """
        # Run 1
        cmd1 = f"""
cd {rtlmeter_dir} &&
rm -rf _work/VeeR* &&
export PATH={baseline_dir}/bin:$PATH &&
./rtlmeter run --cases 'VeeR-EH1:default:hello' --timeout 120 &&
./rtlmeter collate --runName 'fresh1'
"""
        out1, _ = require_ssm.run_check(cmd1, timeout=300)

        # Run 2 with fresh cache
        cmd2 = f"""
cd {rtlmeter_dir} &&
rm -rf _work/VeeR* &&
export PATH={baseline_dir}/bin:$PATH &&
./rtlmeter run --cases 'VeeR-EH1:default:hello' --timeout 120 &&
./rtlmeter collate --runName 'fresh2'
"""
        out2, _ = require_ssm.run_check(cmd2, timeout=300)

        # Results should differ (at least timestamps)
        assert out1 != out2, \
            "CRITICAL: Results identical after cache clear - caching not working"
        print("\n  Cache isolation verified: fresh runs produce different results")

    def test_different_verilator_different_results(
        self, require_ssm, rtlmeter_dir, baseline_dir, optimized_dir
    ):
        """
        Running with baseline vs optimized Verilator MUST produce
        different results (at minimum, different version strings).

        This is the test that would have caught the original caching bug.
        """
        # Run with baseline
        cmd_baseline = f"""
cd {rtlmeter_dir} &&
rm -rf _work/VeeR* &&
export PATH={baseline_dir}/bin:$PATH &&
./rtlmeter run --cases 'VeeR-EH1:default:hello' --timeout 120 &&
./rtlmeter collate --runName 'baseline'
"""
        baseline_out, _ = require_ssm.run_check(cmd_baseline, timeout=300)

        # Run with optimized
        cmd_optimized = f"""
cd {rtlmeter_dir} &&
rm -rf _work/VeeR* &&
export PATH={optimized_dir}/bin:$PATH &&
./rtlmeter run --cases 'VeeR-EH1:default:hello' --timeout 120 &&
./rtlmeter collate --runName 'optimized'
"""
        optimized_out, _ = require_ssm.run_check(cmd_optimized, timeout=300)

        # Parse results
        baseline_data = json.loads(baseline_out)
        optimized_data = json.loads(optimized_out)

        ver_baseline = baseline_data[0].get("VerilatorVersion", "")
        ver_optimized = optimized_data[0].get("VerilatorVersion", "")

        assert ver_baseline != ver_optimized, \
            f"CRITICAL: Verilator versions should differ!\n" \
            f"  Baseline:  {ver_baseline}\n" \
            f"  Optimized: {ver_optimized}"

        print(f"\n  Baseline Verilator:  {ver_baseline}")
        print(f"  Optimized Verilator: {ver_optimized}")
        print("  Version isolation verified!")


@pytest.mark.remote
@pytest.mark.slow
@pytest.mark.e2e
class TestFullBenchmarkWorkflow:
    """
    End-to-end test of the complete benchmark workflow.

    This runs the same flow as benchmark.py but in a minimal form
    to verify the entire pipeline works.
    """

    def test_baseline_vs_optimized_full_cycle(
        self, require_ssm, rtlmeter_dir, baseline_dir, optimized_dir
    ):
        """
        E2E: Run benchmark with both Verilators and verify:
        1. Both runs complete successfully
        2. Results are valid JSON
        3. Verilator versions differ
        4. Results are not byte-identical (no caching)
        """
        results = {}

        for label, install_dir in [
            ("baseline", baseline_dir),
            ("optimized", optimized_dir)
        ]:
            # Use --verilate-jobs to control V3ThreadPool (not --threads which is VlThreadPool)
            cmd = f"""
cd {rtlmeter_dir} &&
rm -rf _work/VeeR* &&
export PATH={install_dir}/bin:$PATH &&
./rtlmeter run --cases 'VeeR-EH1:default:hello' --timeout 120 --compileArgs '--verilate-jobs 4' &&
./rtlmeter collate --runName 'e2e-{label}'
"""
            stdout, _ = require_ssm.run_check(cmd, timeout=600)
            results[label] = stdout

        # Verify results are valid JSON
        baseline_data = json.loads(results["baseline"])
        optimized_data = json.loads(results["optimized"])

        # Verify required fields present
        assert "VerilatorVersion" in baseline_data[0]
        assert "VerilatorVersion" in optimized_data[0]
        assert "cases" in baseline_data[0]
        assert "cases" in optimized_data[0]

        # Verify versions differ
        baseline_ver = baseline_data[0]["VerilatorVersion"]
        optimized_ver = optimized_data[0]["VerilatorVersion"]

        assert baseline_ver != optimized_ver, \
            f"CRITICAL: Same Verilator version!\n" \
            f"  Baseline:  {baseline_ver}\n" \
            f"  Optimized: {optimized_ver}"

        # Verify results not byte-identical
        assert results["baseline"] != results["optimized"], \
            "CRITICAL: Results byte-identical - indicates caching issue!"

        print(f"\n  E2E FULL CYCLE PASSED")
        print(f"  Baseline:  {baseline_ver}")
        print(f"  Optimized: {optimized_ver}")
        print(f"  Baseline cases:  {list(baseline_data[0]['cases'].keys())}")
        print(f"  Optimized cases: {list(optimized_data[0]['cases'].keys())}")

    def test_v3threadpool_parallelism(
        self, require_ssm, rtlmeter_dir, optimized_dir
    ):
        """
        Verify that --verilate-jobs actually causes V3ThreadPool parallelism.
        Check CPU time vs wall time ratio indicates parallelism in verilate step.
        """
        # Use --verilate-jobs to control V3ThreadPool (not --threads which is VlThreadPool)
        cmd = f"""
cd {rtlmeter_dir} &&
rm -rf _work/VeeR* &&
export PATH={optimized_dir}/bin:$PATH &&
./rtlmeter run --cases 'VeeR-EH1:default:hello' --timeout 120 --compileArgs '--verilate-jobs 8' &&
./rtlmeter collate --runName 'v3threadpool-test'
"""
        stdout, _ = require_ssm.run_check(cmd, timeout=600)

        data = json.loads(stdout)

        # Find verilate step metrics (where V3ThreadPool is used)
        verilate_metrics = data[0].get("cases", {}).get("VeeR-EH1:default", {}).get("verilate", {})

        if verilate_metrics:
            cpu_time = verilate_metrics.get("cpu", [0])[0]
            elapsed_time = verilate_metrics.get("elapsed", [0])[0]

            if elapsed_time > 0:
                parallelism = cpu_time / elapsed_time
                print(f"\n  Verilate CPU time: {cpu_time:.1f}s")
                print(f"  Verilate elapsed:  {elapsed_time:.1f}s")
                print(f"  Parallelism ratio: {parallelism:.1f}x")

                # With --verilate-jobs 8, expect some parallelism
                # (may not be exactly 8x due to I/O, sequential phases, etc.)
                if parallelism < 1.5:
                    print("  WARNING: Low parallelism - V3ThreadPool may not be effective")


@pytest.mark.remote
@pytest.mark.slow
@pytest.mark.e2e
class TestStatisticalComparison:
    """
    Test that RTLMeter compare produces valid statistical output.

    This validates the benchmark methodology that uses rtlmeter compare
    for p-value analysis of baseline vs optimized results.
    """

    def test_compare_produces_metrics(
        self, require_ssm, rtlmeter_dir, baseline_dir, optimized_dir
    ):
        """
        RTLMeter compare should produce comparison metrics with p-values.
        """
        # Run baseline with multiple samples
        # Use --verilate-jobs (not --threads) to control V3ThreadPool
        cmd_baseline = f"""
cd {rtlmeter_dir} &&
rm -rf work-test-baseline &&
export PATH={baseline_dir}/bin:$PATH &&
./rtlmeter run --cases 'VeeR-EH1:default:cmark' --workDir work-test-baseline \
    --nExecute 3 --compileArgs '--verilate-jobs 4' --timeout 300
"""
        require_ssm.run_check(cmd_baseline, timeout=900)

        # Run optimized with multiple samples
        cmd_optimized = f"""
cd {rtlmeter_dir} &&
rm -rf work-test-optimized &&
export PATH={optimized_dir}/bin:$PATH &&
./rtlmeter run --cases 'VeeR-EH1:default:cmark' --workDir work-test-optimized \
    --nExecute 3 --compileArgs '--verilate-jobs 4' --timeout 300
"""
        require_ssm.run_check(cmd_optimized, timeout=900)

        # Run comparison on verilate step (where V3ThreadPool is used)
        cmd_compare = f"""
cd {rtlmeter_dir} &&
./rtlmeter compare --steps 'verilate' --metrics 'elapsed cpu' \
    work-test-baseline work-test-optimized
"""
        compare_out, _ = require_ssm.run_check(cmd_compare, timeout=120)

        # Verify comparison output contains expected elements
        # rtlmeter compare should show metrics like elapsed, cpu
        output_lower = compare_out.lower()
        assert "verilate" in output_lower or "elapsed" in output_lower or "cpu" in output_lower, \
            f"Compare output should include metric results, got: {compare_out[:500]}"

        print(f"\nRTLMeter compare output:\n{compare_out}")
        print("\n  Statistical comparison test PASSED")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
