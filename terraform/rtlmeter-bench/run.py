#!/usr/bin/env python3
"""
RTLMeter Benchmark Orchestrator.

This script runs the COMPLETE benchmark flow:

PHASE 1: Pre-flight checks (local)
  - Python linting (pylint, mypy)
  - Terraform validation
  - Unit tests (test_unit.py)
  - Pre-deployment integration tests (test_pre_deploy_integration.py)

PHASE 2: Infrastructure provisioning
  - terraform apply (creates EC2 spot instance)

PHASE 3: Benchmark execution
  - Runs benchmark.py (builds Verilator, runs RTLMeter)

PHASE 4: Post-deployment validation (via SSM)
  - Runs pytest locally, commands execute on EC2 via SSM
  - Post-deployment integration tests (test_post_deploy_integration.py)

PHASE 5: Results retrieval
  - Uploads results to S3 (backup)
  - Fetches results JSON files from EC2 to local machine

PHASE 6: Cleanup
  - ALWAYS terminates EC2 instance
  - terraform destroy (unless --keep-infra)

Test Pyramid:
  - test_unit.py: Unit tests with mocked dependencies
  - test_pre_deploy_integration.py: AWS, Terraform, code pattern checks
  - test_post_deploy_integration.py: Remote tests via SSM
  - test_e2e.py: Full workflow tests (run with --e2e flag)

Usage:
    python3 run.py --region us-east-2  # Full run in us-east-2
    python3 run.py --region us-east-2 --preflight  # Pre-flight only
    python3 run.py --region us-east-2 --skip-preflight  # Skip pre-flight
    python3 run.py --region us-east-2 --keep-infra  # Keep IAM/S3 after run
    python3 run.py --region us-east-2 --e2e  # Include E2E tests (slow)

Exit codes:
    0 - All checks passed and benchmarks completed
    1 - One or more checks/stages failed
"""

import subprocess
import sys
import os
import argparse
import signal
import time
from pathlib import Path
from datetime import datetime

import boto3

# Change to script directory
SCRIPT_DIR = Path(__file__).parent.resolve()
os.chdir(SCRIPT_DIR)

# Global state (set in main after parsing args)
_aws_region: str = ""
_keep_infra_flag = False
_ssm = None  # boto3 SSM client, initialized in init_aws_clients
_ec2 = None  # boto3 EC2 client, initialized in init_aws_clients
_s3 = None   # boto3 S3 client, initialized in init_aws_clients


def init_aws_clients(region: str) -> None:
    """Initialize boto3 clients with specified region."""
    global _aws_region, _ssm, _ec2, _s3
    _aws_region = region
    _ssm = boto3.client("ssm", region_name=region)
    _ec2 = boto3.client("ec2", region_name=region)
    _s3 = boto3.client("s3", region_name=region)
    # Also set environment variable for benchmark.py
    os.environ["AWS_REGION"] = region


def _signal_handler(signum, frame):
    """Handle Ctrl+C by cleaning up EC2 before exit."""
    print("\n\n" + "!" * 60)
    print("  INTERRUPTED - Cleaning up to avoid orphaned EC2 costs...")
    print("!" * 60)

    # Always terminate EC2
    instance_id = get_instance_id()
    if instance_id:
        terminate_ec2_instance(instance_id)

    if not _keep_infra_flag:
        subprocess.run(
            ["terraform", "destroy", "-auto-approve", f"-var=aws_region={_aws_region}"],
            capture_output=True, check=False
        )
        print("  Terraform resources destroyed.")
    else:
        print("  EC2 terminated. Run 'terraform destroy' to clean up remaining resources.")

    sys.exit(130)  # Standard exit code for Ctrl+C


# Register signal handler
signal.signal(signal.SIGINT, _signal_handler)
signal.signal(signal.SIGTERM, _signal_handler)


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


def ssm_send_command(instance_id: str, commands: list[str],
                     timeout: int = 120) -> tuple[str, str] | None:
    """Send SSM command and wait for result. Returns (stdout, stderr) or None."""
    try:
        response = _ssm.send_command(  # type: ignore[union-attr]
            InstanceIds=[instance_id],
            DocumentName="AWS-RunShellScript",
            Parameters={"commands": commands},
            TimeoutSeconds=timeout
        )
        command_id = response["Command"]["CommandId"]

        # Wait for result
        for _ in range(timeout // 2):
            time.sleep(2)
            try:
                invocation = _ssm.get_command_invocation(  # type: ignore[union-attr]
                    CommandId=command_id,
                    InstanceId=instance_id
                )
                if invocation["Status"] == "Success":
                    return (
                        invocation.get("StandardOutputContent", ""),
                        invocation.get("StandardErrorContent", "")
                    )
                if invocation["Status"] in ("Failed", "Cancelled", "TimedOut"):
                    return None
            except Exception:
                pass
    except Exception:
        pass
    return None


def phase_preflight() -> tuple[bool, list[tuple[str, bool]]]:
    """Run pre-flight checks. Returns (all_passed, results)."""
    print("\n" + "#" * 60)
    print("  PHASE 1: PRE-FLIGHT CHECKS")
    print("#" * 60)

    all_passed = True
    results = []

    # Test files to check
    test_files = [
        "test_unit.py",
        "test_pre_deploy_integration.py",
        "test_post_deploy_integration.py",
        "test_e2e.py",
        "conftest.py",
    ]
    script_files = ["benchmark.py", "run.py"]

    # 1. Mypy type checking
    passed = run_cmd(
        ["python3", "-m", "mypy"] + test_files + script_files,
        "Mypy type checking"
    )
    results.append(("Mypy", passed))
    all_passed = all_passed and passed

    # 2. Pylint static analysis
    passed = run_cmd(
        ["python3", "-m", "pylint", "--fail-under=8.0",
         "--disable=C0116,C0301,W1510,C0415"] + test_files + script_files,
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

    # 5. Unit tests (fast, mocked dependencies)
    passed = run_cmd(
        ["python3", "-m", "pytest", "test_unit.py", "-v", "--tb=short"],
        "Unit tests"
    )
    results.append(("Unit tests", passed))
    all_passed = all_passed and passed

    # 6. Pre-deployment integration tests (AWS, Terraform, code patterns)
    passed = run_cmd(
        ["python3", "-m", "pytest", "test_pre_deploy_integration.py", "-v", "--tb=short"],
        "Pre-deployment integration tests"
    )
    results.append(("Pre-deploy integration", passed))
    all_passed = all_passed and passed

    return all_passed, results


def phase_provision() -> bool:
    """Provision EC2 instance with Terraform."""
    print("\n" + "#" * 60)
    print("  PHASE 2: INFRASTRUCTURE PROVISIONING")
    print("#" * 60)

    success = run_cmd(
        ["terraform", "apply", "-auto-approve", f"-var=aws_region={_aws_region}"],
        f"Terraform apply (creating EC2 spot instance in {_aws_region})"
    )

    if success:
        # Print dashboard URL for monitoring
        result = subprocess.run(
            ["terraform", "output", "-raw", "dashboard_url"],
            capture_output=True, text=True, check=False
        )
        if result.returncode == 0 and result.stdout.strip():
            print("\n" + "=" * 60)
            print("  CLOUDWATCH DASHBOARD (open in browser for live monitoring):")
            print(f"  {result.stdout.strip()}")
            print("=" * 60)

    return success


def phase_benchmark() -> bool:
    """Run the RTLMeter benchmarks."""
    print("\n" + "#" * 60)
    print("  PHASE 3: BENCHMARK EXECUTION")
    print("#" * 60)

    return run_cmd(
        ["python3", "benchmark.py"],
        "RTLMeter benchmarks"
    )


def get_instance_id() -> str | None:
    """Get the EC2 instance ID from Terraform output."""
    result = subprocess.run(
        ["terraform", "output", "-raw", "instance_id"],
        capture_output=True, text=True, check=False
    )
    if result.returncode == 0 and result.stdout.strip():
        return result.stdout.strip()
    return None


def get_s3_bucket() -> str | None:
    """Get the S3 bucket name from Terraform output."""
    result = subprocess.run(
        ["terraform", "output", "-raw", "s3_bucket"],
        capture_output=True, text=True, check=False
    )
    if result.returncode == 0 and result.stdout.strip():
        return result.stdout.strip()
    return None


def terminate_ec2_instance(instance_id: str) -> bool:
    """Terminate EC2 instance via boto3."""
    print(f"\n  Terminating EC2 instance {instance_id}...")
    try:
        _ec2.terminate_instances(InstanceIds=[instance_id])  # type: ignore[union-attr]
        print(f"  EC2 instance {instance_id} terminated")
        return True
    except Exception as e:
        print(f"  Failed to terminate: {e}")
        return False


def phase_retrieve_results() -> bool:
    """Fetch results from EC2 before destroying it."""
    print("\n" + "#" * 60)
    print("  PHASE 5: RESULTS RETRIEVAL")
    print("#" * 60)

    instance_id = get_instance_id()
    if not instance_id:
        print("  No instance ID found, skipping results retrieval")
        return False

    s3_bucket = get_s3_bucket()

    # Create results directory with timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    results_dir = SCRIPT_DIR / "results" / timestamp
    results_dir.mkdir(parents=True, exist_ok=True)
    print(f"\n  Saving results to: {results_dir}")

    # Get list of result files on EC2
    print("\n  Fetching result files from EC2...")
    result = ssm_send_command(
        instance_id,
        ["ls -1 /home/ubuntu/benchmark/results_*.json "
         "/home/ubuntu/benchmark/comparison_summary.txt 2>/dev/null || echo 'NO_RESULTS'"],
        timeout=60
    )

    if not result:
        print("  Failed to list results")
        return False

    file_list, _ = result
    if "NO_RESULTS" in file_list or not file_list.strip():
        print("  No result files found on EC2")
        return False

    result_files = file_list.strip().split("\n")
    print(f"  Found {len(result_files)} result files")

    # Fetch each file
    for remote_path in result_files:
        filename = os.path.basename(remote_path)
        print(f"  Fetching {filename}...")

        result = ssm_send_command(
            instance_id,
            [f"cat {remote_path}"],
            timeout=60
        )

        if result:
            content, _ = result
            local_path = results_dir / filename
            local_path.write_text(content)
            print(f"    Saved to {local_path}")
        else:
            print(f"    Failed to fetch {filename}")

    # Also fetch the RTLMeter verilate step report (where V3ThreadPool is used)
    print("\n  Fetching RTLMeter verilate step report...")
    result = ssm_send_command(
        instance_id,
        ["cd /home/ubuntu/benchmark/rtlmeter && "
         "for f in /home/ubuntu/benchmark/results_*.json; do "
         "echo '=== '$(basename $f)' ===' && "
         "./rtlmeter report --steps 'verilate' --metrics 'elapsed cpu' $f; "
         "done"],
        timeout=300
    )

    if result:
        report, _ = result
        report_path = results_dir / "verilate_step_report.txt"
        report_path.write_text(report)
        print(f"  Saved verilate step report to {report_path}")

    print(f"\n  Results saved to: {results_dir}")

    # Upload to S3 directly from EC2 (more efficient than downloading then uploading)
    if s3_bucket:
        print(f"\n  Uploading results to S3 from EC2...")
        result = ssm_send_command(
            instance_id,
            [f"export PATH=$HOME/.local/bin:$PATH && "
             f"aws s3 cp /home/ubuntu/benchmark/ s3://{s3_bucket}/{timestamp}/ "
             "--recursive --exclude '*' "
             f"--include 'results_*.json' --include 'comparison_summary.txt' "
             f"--region {_aws_region}"],
            timeout=120
        )
        if result:
            print(f"  Results backed up to s3://{s3_bucket}/{timestamp}/")
            (results_dir / "s3_backup_path.txt").write_text(
                f"s3://{s3_bucket}/{timestamp}/\n"
            )
        else:
            print("  S3 upload failed")

    return True


def phase_validate_on_instance(run_e2e: bool = False) -> bool:
    """Run post-deployment tests via SSM (tests run locally, commands on EC2)."""
    print("\n" + "#" * 60)
    print("  PHASE 4: POST-DEPLOYMENT VALIDATION (via SSM)")
    print("#" * 60)

    instance_id = get_instance_id()
    if not instance_id:
        print("  No instance ID found, skipping validation")
        return False

    print("\n  Running post-deployment tests locally (commands execute on EC2 via SSM)...")
    print("  This validates the EC2 setup without copying test files to the instance.")

    all_passed = True

    # Post-deployment integration tests (directory structure, binaries, versions)
    passed = run_cmd(
        ["python3", "-m", "pytest", "test_post_deploy_integration.py", "-v", "--tb=short"],
        "Post-deployment integration tests (via SSM)"
    )
    all_passed = all_passed and passed

    # E2E tests (optional - slow but thorough)
    if run_e2e:
        print("\n  Running E2E tests (cache isolation, full workflow)...")
        passed = run_cmd(
            ["python3", "-m", "pytest", "test_e2e.py", "-v", "--tb=short"],
            "E2E tests (cache isolation, full workflow)"
        )
        all_passed = all_passed and passed
    else:
        print("\n  Skipping E2E tests (use --e2e to enable)")

    return all_passed


def phase_cleanup(keep_infra: bool = False) -> bool:
    """Terminate EC2 and optionally destroy all infrastructure."""
    print("\n" + "#" * 60)
    print("  PHASE 6: CLEANUP")
    print("#" * 60)

    # ALWAYS terminate EC2 instance first (even with --keep-infra)
    instance_id = get_instance_id()
    if instance_id:
        terminate_ec2_instance(instance_id)
    else:
        print("  No instance ID found, skipping EC2 termination")

    if keep_infra:
        print("\n  --keep-infra: Keeping IAM roles, S3 bucket, etc.")
        print("  Run 'terraform destroy' manually to clean up remaining resources.")
        return True

    # Full terraform destroy
    return run_cmd(
        ["terraform", "destroy", "-auto-approve", f"-var=aws_region={_aws_region}"],
        "Terraform destroy (cleaning up all resources)",
        check=False  # Always try to clean up
    )


def main() -> int:
    """Run the full benchmark orchestration."""
    parser = argparse.ArgumentParser(description="RTLMeter Benchmark Orchestrator")
    parser.add_argument("--region", required=True,
                        help="AWS region (e.g., us-east-2)")
    parser.add_argument("--preflight", action="store_true",
                        help="Run pre-flight checks only (no EC2)")
    parser.add_argument("--skip-preflight", action="store_true",
                        help="Skip pre-flight checks, run benchmarks directly")
    parser.add_argument("--keep-infra", action="store_true",
                        help="Keep IAM/S3 after run (EC2 always terminated)")
    parser.add_argument("--e2e", action="store_true",
                        help="Run E2E tests (slow but thorough cache/workflow tests)")
    args = parser.parse_args()

    # Initialize AWS clients with specified region
    init_aws_clients(args.region)

    # Set global flag for signal handler
    global _keep_infra_flag
    _keep_infra_flag = args.keep_infra

    print("=" * 60)
    print("  RTLMeter Benchmark Orchestrator")
    print("=" * 60)
    print(f"\nWorking directory: {SCRIPT_DIR}")
    print(f"AWS Region: {_aws_region}")

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
        phase_cleanup(args.keep_infra)  # Try to clean up
        return 1

    # Phase 3: Benchmark
    benchmark_passed = phase_benchmark()

    # Phase 4: Post-deployment validation
    validation_passed = phase_validate_on_instance(run_e2e=args.e2e)

    # Phase 5: Retrieve results (always try, even if benchmark/validation failed)
    results_retrieved = phase_retrieve_results()

    # Phase 6: Cleanup (always run - EC2 ALWAYS terminated)
    phase_cleanup(args.keep_infra)

    # Final summary
    print("\n" + "=" * 60)
    print("  FINAL SUMMARY")
    print("=" * 60)

    if benchmark_passed and validation_passed and results_retrieved:
        print("  ALL PHASES COMPLETED SUCCESSFULLY")
        print(f"  Results saved to: {SCRIPT_DIR}/results/")
        return 0

    issues = []
    if not benchmark_passed:
        issues.append("Benchmarks failed")
    if not validation_passed:
        issues.append("Post-deployment validation failed")
    if not results_retrieved:
        issues.append("Results retrieval failed")

    print(f"  ISSUES: {', '.join(issues)}")
    if results_retrieved:
        print(f"  Results saved to: {SCRIPT_DIR}/results/")
    return 1


if __name__ == "__main__":
    sys.exit(main())
