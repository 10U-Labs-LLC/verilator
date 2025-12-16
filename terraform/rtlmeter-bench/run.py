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

PHASE 4: On-instance validation
  - Runs pytest test_setup.py on EC2 to validate setup

PHASE 5: Results retrieval
  - Uploads results to S3 (backup)
  - Fetches results JSON files from EC2 to local machine

PHASE 6: Cleanup
  - ALWAYS terminates EC2 instance
  - terraform destroy (unless --keep-infra)

Usage:
    python3 run.py              # Full run
    python3 run.py --preflight  # Pre-flight only (no EC2)
    python3 run.py --skip-preflight  # Skip pre-flight, run benchmarks
    python3 run.py --keep-infra # Keep IAM/S3 after run (for subsequent runs)

Exit codes:
    0 - All checks passed and benchmarks completed
    1 - One or more checks/stages failed
"""

import subprocess
import sys
import os
import json
import argparse
from pathlib import Path
from datetime import datetime

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
    """Terminate EC2 instance directly via AWS CLI."""
    print(f"\n  Terminating EC2 instance {instance_id}...")
    result = subprocess.run(
        ["aws", "ec2", "terminate-instances",
         "--instance-ids", instance_id,
         "--region", "us-east-2"],
        capture_output=True, text=True, check=False
    )
    if result.returncode == 0:
        print(f"  EC2 instance {instance_id} terminated")
        return True
    print(f"  Failed to terminate: {result.stderr}")
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

    import time

    # First, upload results to S3 from EC2 (backup)
    if s3_bucket:
        print(f"\n  Uploading results to S3 bucket: {s3_bucket}")
        s3_upload_cmd = subprocess.run(
            ["aws", "ssm", "send-command",
             "--instance-ids", instance_id,
             "--document-name", "AWS-RunShellScript",
             "--parameters", json.dumps({
                 "commands": [
                     f"aws s3 cp /home/ubuntu/benchmark/ s3://{s3_bucket}/{timestamp}/ "
                     "--recursive --exclude '*' "
                     "--include 'results_*.json' --include 'comparison_summary.txt' "
                     "--region us-east-2"
                 ]
             }),
             "--output", "json"],
            capture_output=True, text=True, check=False
        )

        if s3_upload_cmd.returncode == 0:
            cmd_data = json.loads(s3_upload_cmd.stdout)
            command_id = cmd_data["Command"]["CommandId"]
            for _ in range(30):
                time.sleep(2)
                result = subprocess.run(
                    ["aws", "ssm", "get-command-invocation",
                     "--command-id", command_id,
                     "--instance-id", instance_id,
                     "--output", "json"],
                    capture_output=True, text=True, check=False
                )
                if result.returncode == 0:
                    invocation = json.loads(result.stdout)
                    if invocation["Status"] == "Success":
                        print(f"  Results backed up to s3://{s3_bucket}/{timestamp}/")
                        # Save S3 path to local file
                        (results_dir / "s3_backup_path.txt").write_text(
                            f"s3://{s3_bucket}/{timestamp}/\n"
                        )
                        break
                    if invocation["Status"] in ("Failed", "Cancelled", "TimedOut"):
                        print(f"  S3 upload failed: {invocation['Status']}")
                        break
    else:
        print("  No S3 bucket found, skipping S3 backup")

    # Get list of result files on EC2
    print("\n  Fetching result files from EC2...")
    list_cmd = subprocess.run(
        ["aws", "ssm", "send-command",
         "--instance-ids", instance_id,
         "--document-name", "AWS-RunShellScript",
         "--parameters", json.dumps({
             "commands": [
                 "ls -1 /home/ubuntu/benchmark/results_*.json "
                 "/home/ubuntu/benchmark/comparison_summary.txt 2>/dev/null || echo 'NO_RESULTS'"
             ]
         }),
         "--output", "json"],
        capture_output=True, text=True, check=False
    )

    if list_cmd.returncode != 0:
        print(f"  Failed to list results: {list_cmd.stderr}")
        return False

    cmd_data = json.loads(list_cmd.stdout)
    command_id = cmd_data["Command"]["CommandId"]

    # Wait for command to complete
    import time
    for _ in range(30):
        time.sleep(2)
        result = subprocess.run(
            ["aws", "ssm", "get-command-invocation",
             "--command-id", command_id,
             "--instance-id", instance_id,
             "--output", "json"],
            capture_output=True, text=True, check=False
        )
        if result.returncode == 0:
            invocation = json.loads(result.stdout)
            if invocation["Status"] == "Success":
                file_list = invocation.get("StandardOutputContent", "").strip()
                break
            if invocation["Status"] in ("Failed", "Cancelled", "TimedOut"):
                print(f"  Command failed: {invocation['Status']}")
                return False
    else:
        print("  Timeout waiting for file list")
        return False

    if "NO_RESULTS" in file_list or not file_list:
        print("  No result files found on EC2")
        return False

    result_files = file_list.strip().split("\n")
    print(f"  Found {len(result_files)} result files")

    # Fetch each file
    for remote_path in result_files:
        filename = os.path.basename(remote_path)
        print(f"  Fetching {filename}...")

        # Use SSM to cat the file content
        cat_cmd = subprocess.run(
            ["aws", "ssm", "send-command",
             "--instance-ids", instance_id,
             "--document-name", "AWS-RunShellScript",
             "--parameters", json.dumps({
                 "commands": [f"cat {remote_path}"]
             }),
             "--output", "json"],
            capture_output=True, text=True, check=False
        )

        if cat_cmd.returncode != 0:
            print(f"    Failed to fetch {filename}")
            continue

        cmd_data = json.loads(cat_cmd.stdout)
        command_id = cmd_data["Command"]["CommandId"]

        # Wait for content
        for _ in range(30):
            time.sleep(2)
            result = subprocess.run(
                ["aws", "ssm", "get-command-invocation",
                 "--command-id", command_id,
                 "--instance-id", instance_id,
                 "--output", "json"],
                capture_output=True, text=True, check=False
            )
            if result.returncode == 0:
                invocation = json.loads(result.stdout)
                if invocation["Status"] == "Success":
                    content = invocation.get("StandardOutputContent", "")
                    local_path = results_dir / filename
                    local_path.write_text(content)
                    print(f"    Saved to {local_path}")
                    break
                if invocation["Status"] in ("Failed", "Cancelled", "TimedOut"):
                    print(f"    Failed: {invocation['Status']}")
                    break

    # Also fetch the RTLMeter reports (stdout from benchmark runs)
    print("\n  Fetching RTLMeter summary report...")
    report_cmd = subprocess.run(
        ["aws", "ssm", "send-command",
         "--instance-ids", instance_id,
         "--document-name", "AWS-RunShellScript",
         "--parameters", json.dumps({
             "commands": [
                 "cd /home/ubuntu/benchmark/rtlmeter && "
                 "for f in /home/ubuntu/benchmark/results_*.json; do "
                 "echo '=== '$(basename $f)' ===' && "
                 "./rtlmeter report --steps '*' --metrics '*' $f; "
                 "done"
             ]
         }),
         "--output", "json"],
        capture_output=True, text=True, check=False
    )

    if report_cmd.returncode == 0:
        cmd_data = json.loads(report_cmd.stdout)
        command_id = cmd_data["Command"]["CommandId"]

        for _ in range(60):
            time.sleep(2)
            result = subprocess.run(
                ["aws", "ssm", "get-command-invocation",
                 "--command-id", command_id,
                 "--instance-id", instance_id,
                 "--output", "json"],
                capture_output=True, text=True, check=False
            )
            if result.returncode == 0:
                invocation = json.loads(result.stdout)
                if invocation["Status"] == "Success":
                    report = invocation.get("StandardOutputContent", "")
                    report_path = results_dir / "summary_report.txt"
                    report_path.write_text(report)
                    print(f"  Saved summary report to {report_path}")
                    break
                if invocation["Status"] in ("Failed", "Cancelled", "TimedOut"):
                    break

    print(f"\n  Results saved to: {results_dir}")
    return True


def phase_validate_on_instance() -> bool:
    """Run validation tests on EC2 instance."""
    print("\n" + "#" * 60)
    print("  PHASE 4: ON-INSTANCE VALIDATION")
    print("#" * 60)

    instance_id = get_instance_id()
    if not instance_id:
        print("  No instance ID found, skipping validation")
        return False

    import time

    # Copy test_setup.py to EC2 and run it
    print("\n  Running pytest on EC2 instance...")
    print("  (excluding AWSPreProvisioning tests - those are local only)")

    # First, copy test_setup.py to the instance
    test_file = SCRIPT_DIR / "test_setup.py"
    test_content = test_file.read_text()

    # Upload and run tests via SSM
    validate_cmd = subprocess.run(
        ["aws", "ssm", "send-command",
         "--instance-ids", instance_id,
         "--document-name", "AWS-RunShellScript",
         "--parameters", json.dumps({
             "commands": [
                 # Install pytest if not present
                 "pip3 install --user pytest",
                 # Create test file
                 f"cat > /home/ubuntu/benchmark/test_setup.py << 'TESTEOF'\n{test_content}\nTESTEOF",
                 # Run tests excluding AWSPreProvisioning (those are local)
                 "cd /home/ubuntu/benchmark && "
                 "python3 -m pytest test_setup.py -v "
                 "--ignore-glob='*AWSPreProvisioning*' "
                 "-k 'not AWSPreProvisioning' "
                 "--tb=short 2>&1 || true"
             ]
         }),
         "--timeout-seconds", "600",
         "--output", "json"],
        capture_output=True, text=True, check=False
    )

    if validate_cmd.returncode != 0:
        print(f"  Failed to run validation: {validate_cmd.stderr}")
        return False

    cmd_data = json.loads(validate_cmd.stdout)
    command_id = cmd_data["Command"]["CommandId"]

    # Wait for validation to complete
    for _ in range(120):  # 4 minutes max
        time.sleep(2)
        result = subprocess.run(
            ["aws", "ssm", "get-command-invocation",
             "--command-id", command_id,
             "--instance-id", instance_id,
             "--output", "json"],
            capture_output=True, text=True, check=False
        )
        if result.returncode == 0:
            invocation = json.loads(result.stdout)
            status = invocation["Status"]
            if status == "Success":
                output = invocation.get("StandardOutputContent", "")
                print(output)
                # Check if tests passed
                if "failed" in output.lower() and "0 failed" not in output.lower():
                    print("\n  VALIDATION FAILED - Some tests did not pass")
                    return False
                print("\n  VALIDATION PASSED")
                return True
            if status in ("Failed", "Cancelled", "TimedOut"):
                print(f"  Validation command {status}")
                print(invocation.get("StandardOutputContent", ""))
                print(invocation.get("StandardErrorContent", ""))
                return False
        print(".", end="", flush=True)

    print("\n  Timeout waiting for validation")
    return False


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
        ["terraform", "destroy", "-auto-approve"],
        "Terraform destroy (cleaning up all resources)",
        check=False  # Always try to clean up
    )


def main() -> int:
    """Run the full benchmark orchestration."""
    parser = argparse.ArgumentParser(description="RTLMeter Benchmark Orchestrator")
    parser.add_argument("--preflight", action="store_true",
                        help="Run pre-flight checks only (no EC2)")
    parser.add_argument("--skip-preflight", action="store_true",
                        help="Skip pre-flight checks, run benchmarks directly")
    parser.add_argument("--keep-infra", action="store_true",
                        help="Keep IAM/S3 after run (EC2 always terminated)")
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
        phase_cleanup(args.keep_infra)  # Try to clean up
        return 1

    # Phase 3: Benchmark
    benchmark_passed = phase_benchmark()

    # Phase 4: On-instance validation
    validation_passed = phase_validate_on_instance()

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
        issues.append("On-instance validation failed")
    if not results_retrieved:
        issues.append("Results retrieval failed")

    print(f"  ISSUES: {', '.join(issues)}")
    if results_retrieved:
        print(f"  Results saved to: {SCRIPT_DIR}/results/")
    return 1


if __name__ == "__main__":
    sys.exit(main())
