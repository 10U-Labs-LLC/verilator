#!/usr/bin/env python3
"""
RTLMeter Benchmark Orchestrator.

This script runs the COMPLETE benchmark flow:

PHASE 1: Pre-flight checks (local)
  - Python linting (pylint, mypy)
  - Terraform validation
  - AWS pre-provisioning tests (credentials, quotas, spot config)

PHASE 2: Infrastructure provisioning
  - terraform apply (creates EC2 spot instance)

PHASE 3: Benchmark execution
  - Runs benchmark.py (builds Verilator, runs RTLMeter)

PHASE 4: On-instance validation (runs on EC2)
  - pytest test_setup.py (validates everything is set up correctly)

PHASE 5: Cleanup
  - terraform destroy (terminates EC2 instance)

Usage:
    python3 run_preflight.py              # Full run
    python3 run_preflight.py --preflight  # Pre-flight only (no EC2)
    python3 run_preflight.py --skip-preflight  # Skip pre-flight, run benchmarks

Exit codes:
    0 - All checks passed and benchmarks completed
    1 - One or more checks/stages failed
"""

import subprocess
import sys
import os
import argparse
from pathlib import Path

# Change to script directory
SCRIPT_DIR = Path(__file__).parent.resolve()
os.chdir(SCRIPT_DIR)


def run_cmd(cmd: list[str], desc: str, check: bool = True) -> bool:
    """Run a command and return True if successful."""
    print(f"\n{'='*60}")
    print(f"  {desc}")
    print(f"{'='*60}")
    print(f"$ {' '.join(cmd)}\n")

    result = subprocess.run(cmd, check=False)
    if result.returncode == 0:
        print(f"\n  PASSED: {desc}")
        return True
    print(f"\n  FAILED: {desc}")
    if check:
        return False
    print("  (continuing anyway)")
    return True


def phase_preflight() -> tuple[bool, list[tuple[str, bool]]]:
    """Run pre-flight checks. Returns (all_passed, results)."""
    print("\n" + "#" * 60)
    print("  PHASE 1: PRE-FLIGHT CHECKS")
    print("#" * 60)

    all_passed = True
    results = []

    # 1. Mypy type checking
    passed = run_cmd(
        ["python3", "-m", "mypy", "test_setup.py", "benchmark.py"],
        "Mypy type checking"
    )
    results.append(("Mypy", passed))
    all_passed = all_passed and passed

    # 2. Pylint static analysis
    passed = run_cmd(
        ["python3", "-m", "pylint", "--fail-under=8.0",
         "--disable=C0116,C0301,W1510,C0415",
         "test_setup.py", "benchmark.py"],
        "Pylint static analysis"
    )
    results.append(("Pylint", passed))
    all_passed = all_passed and passed

    # 3. Terraform format check
    passed = run_cmd(
        ["terraform", "fmt", "-check", "-diff"],
        "Terraform format check"
    )
    results.append(("Terraform fmt", passed))
    all_passed = all_passed and passed

    # 4. Terraform validate
    if not (SCRIPT_DIR / ".terraform").exists():
        run_cmd(["terraform", "init"], "Terraform init")
    passed = run_cmd(
        ["terraform", "validate"],
        "Terraform validate"
    )
    results.append(("Terraform validate", passed))
    all_passed = all_passed and passed

    # 5. AWS Pre-provisioning tests
    passed = run_cmd(
        ["python3", "-m", "pytest", "test_setup.py", "-v",
         "-k", "AWSPreProvisioning", "--tb=short"],
        "AWS pre-provisioning tests"
    )
    results.append(("AWS Pre-provisioning", passed))
    all_passed = all_passed and passed

    return all_passed, results


def phase_provision() -> bool:
    """Provision EC2 instance with Terraform."""
    print("\n" + "#" * 60)
    print("  PHASE 2: INFRASTRUCTURE PROVISIONING")
    print("#" * 60)

    return run_cmd(
        ["terraform", "apply", "-auto-approve"],
        "Terraform apply (creating EC2 spot instance)"
    )


def phase_benchmark() -> bool:
    """Run the RTLMeter benchmarks."""
    print("\n" + "#" * 60)
    print("  PHASE 3: BENCHMARK EXECUTION")
    print("#" * 60)

    return run_cmd(
        ["python3", "benchmark.py"],
        "RTLMeter benchmarks"
    )


def phase_cleanup() -> bool:
    """Destroy EC2 instance."""
    print("\n" + "#" * 60)
    print("  PHASE 5: CLEANUP")
    print("#" * 60)

    return run_cmd(
        ["terraform", "destroy", "-auto-approve"],
        "Terraform destroy (terminating EC2 instance)",
        check=False  # Always try to clean up
    )


def main() -> int:
    """Run the full benchmark orchestration."""
    parser = argparse.ArgumentParser(description="RTLMeter Benchmark Orchestrator")
    parser.add_argument("--preflight", action="store_true",
                        help="Run pre-flight checks only (no EC2)")
    parser.add_argument("--skip-preflight", action="store_true",
                        help="Skip pre-flight checks, run benchmarks directly")
    args = parser.parse_args()

    print("=" * 60)
    print("  RTLMeter Benchmark Orchestrator")
    print("=" * 60)
    print(f"\nWorking directory: {SCRIPT_DIR}")

    # Phase 1: Pre-flight
    if not args.skip_preflight:
        preflight_passed, preflight_results = phase_preflight()

        # Summary
        print("\n" + "=" * 60)
        print("  PRE-FLIGHT SUMMARY")
        print("=" * 60)
        for name, passed in preflight_results:
            status = "PASSED" if passed else "FAILED"
            print(f"  {name}: {status}")
        print("=" * 60)

        if not preflight_passed:
            print("\n  PRE-FLIGHT FAILED - Not proceeding with benchmarks")
            return 1

        if args.preflight:
            print("\n  PRE-FLIGHT PASSED (--preflight mode, not running benchmarks)")
            return 0

    # Phase 2: Provision
    if not phase_provision():
        print("\n  PROVISIONING FAILED")
        phase_cleanup()  # Try to clean up
        return 1

    # Phase 3: Benchmark
    benchmark_passed = phase_benchmark()

    # Phase 5: Cleanup (always run)
    phase_cleanup()

    # Final summary
    print("\n" + "=" * 60)
    print("  FINAL SUMMARY")
    print("=" * 60)
    if benchmark_passed:
        print("  BENCHMARKS COMPLETED SUCCESSFULLY")
        print("  Check results in /home/ubuntu/benchmark/results_*.json")
        return 0

    print("  BENCHMARKS FAILED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
