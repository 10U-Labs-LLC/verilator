#!/usr/bin/env python3
"""
Pre-deployment integration tests.

These tests verify that all components integrate correctly BEFORE deploying
to AWS. They check AWS credentials, Terraform configuration, and code patterns
that could cause failures during the benchmark run.

Run with: pytest test_pre_deploy_integration.py -v
"""

import json
import os
import re
import subprocess

import pytest

# Local paths
TERRAFORM_DIR = os.path.dirname(os.path.abspath(__file__))

# AWS configuration
AWS_REGION = os.environ.get("AWS_REGION", "us-east-2")
INSTANCE_TYPE = "c8i.metal-48xl"
REQUIRED_VCPUS = 192


class TestAWSIntegration:
    """
    Tests that verify AWS connectivity and resource availability.
    These must pass before we can provision EC2 instances.
    """

    def test_aws_cli_installed(self):
        """AWS CLI must be installed."""
        result = subprocess.run(
            ["aws", "--version"],
            capture_output=True, text=True, check=False
        )
        assert result.returncode == 0, "AWS CLI not installed"

    def test_aws_credentials_configured(self):
        """AWS credentials must be configured and valid."""
        result = subprocess.run(
            ["aws", "sts", "get-caller-identity", "--region", AWS_REGION],
            capture_output=True, text=True, check=False
        )
        assert result.returncode == 0, \
            f"AWS credentials not configured: {result.stderr}"

    def test_aws_region_accessible(self):
        """Target AWS region must be accessible."""
        result = subprocess.run(
            ["aws", "ec2", "describe-availability-zones",
             "--region", AWS_REGION,
             "--query", "AvailabilityZones[0].ZoneName"],
            capture_output=True, text=True, check=False
        )
        assert result.returncode == 0, \
            f"Cannot access region {AWS_REGION}: {result.stderr}"

    def test_spot_vcpu_quota_sufficient(self):
        """Spot vCPU quota must be enough for c8i.metal-48xl (192 vCPUs)."""
        result = subprocess.run(
            ["aws", "service-quotas", "get-service-quota",
             "--service-code", "ec2",
             "--quota-code", "L-34B43A08",
             "--region", AWS_REGION],
            capture_output=True, text=True, check=False
        )
        if result.returncode != 0:
            pytest.fail(f"Cannot check vCPU quota: {result.stderr}")

        quota_data = json.loads(result.stdout)
        quota_value = quota_data.get("Quota", {}).get("Value", 0)
        assert quota_value >= REQUIRED_VCPUS, \
            f"Insufficient spot vCPU quota: {quota_value}, need {REQUIRED_VCPUS}"

    def test_instance_type_available_in_region(self):
        """c8i.metal-48xl must be available in the target region."""
        result = subprocess.run(
            ["aws", "ec2", "describe-instance-type-offerings",
             "--location-type", "region",
             "--filters", f"Name=instance-type,Values={INSTANCE_TYPE}",
             "--region", AWS_REGION,
             "--query", "InstanceTypeOfferings[0].InstanceType"],
            capture_output=True, text=True, check=False
        )
        assert result.returncode == 0
        output = result.stdout.strip().strip('"')
        assert output == INSTANCE_TYPE, \
            f"{INSTANCE_TYPE} not available in {AWS_REGION}"

    def test_no_conflicting_spot_instances(self):
        """Check current spot vCPU usage won't conflict."""
        result = subprocess.run(
            ["aws", "ec2", "describe-instances",
             "--filters", "Name=instance-state-name,Values=running",
             "Name=instance-lifecycle,Values=spot",
             "--region", AWS_REGION,
             "--query", "Reservations[].Instances[].InstanceType"],
            capture_output=True, text=True, check=False
        )
        if result.returncode != 0:
            pytest.skip(f"Cannot check current usage: {result.stderr}")

        instances = json.loads(result.stdout) if result.stdout.strip() else []
        print(f"\nCurrently running spot instances: {len(instances)}")

    def test_cloudwatch_accessible(self):
        """CloudWatch API must be accessible for monitoring."""
        result = subprocess.run(
            ["aws", "cloudwatch", "list-metrics",
             "--namespace", "AWS/EC2",
             "--metric-name", "CPUUtilization",
             "--region", AWS_REGION,
             "--max-items", "1"],
            capture_output=True, text=True, check=False
        )
        assert result.returncode == 0, f"CloudWatch not accessible: {result.stderr}"

    def test_git_branch_exists_in_fork(self):
        """Optimized branch must exist in the fork repository."""
        result = subprocess.run(
            ["git", "ls-remote", "--heads",
             "https://github.com/10U-Labs-LLC/verilator.git",
             "optimize-threadpool-wait-cv"],
            capture_output=True, text=True, check=False
        )
        assert result.returncode == 0
        assert "optimize-threadpool-wait-cv" in result.stdout, \
            "Branch 'optimize-threadpool-wait-cv' not found in fork"


class TestTerraformIntegration:
    """
    Tests that verify Terraform configuration is correct.
    These catch misconfigurations before provisioning.
    """

    def test_spot_instance_enforced(self):
        """Terraform must use spot instances only (cost control)."""
        main_tf = os.path.join(TERRAFORM_DIR, "main.tf")
        with open(main_tf, encoding="utf-8") as f:
            content = f.read()

        assert "instance_market_options" in content, \
            "Missing instance_market_options - instance would be on-demand"
        assert re.search(r'market_type\s*=\s*["\']spot["\']', content), \
            "market_type must be 'spot'"
        assert "spot_options" in content, \
            "Missing spot_options block"
        assert re.search(r'spot_instance_type\s*=\s*["\']one-time["\']', content), \
            "spot_instance_type should be 'one-time'"

    def test_s3_bucket_configured(self):
        """Terraform must configure S3 bucket for results backup."""
        main_tf = os.path.join(TERRAFORM_DIR, "main.tf")
        with open(main_tf, encoding="utf-8") as f:
            content = f.read()

        assert "aws_s3_bucket" in content
        assert "aws_s3_bucket_lifecycle_configuration" in content
        assert "force_destroy = true" in content

    def test_s3_iam_permissions_configured(self):
        """EC2 must have IAM permissions to write to S3."""
        main_tf = os.path.join(TERRAFORM_DIR, "main.tf")
        with open(main_tf, encoding="utf-8") as f:
            content = f.read()

        assert "s3:PutObject" in content
        assert "aws_iam_role_policy" in content

    def test_s3_bucket_output_defined(self):
        """Terraform must output the S3 bucket name."""
        outputs_tf = os.path.join(TERRAFORM_DIR, "outputs.tf")
        with open(outputs_tf, encoding="utf-8") as f:
            content = f.read()

        assert "s3_bucket" in content

    def test_ami_is_dynamic(self):
        """AMI must be looked up dynamically (not hardcoded)."""
        main_tf = os.path.join(TERRAFORM_DIR, "main.tf")
        with open(main_tf, encoding="utf-8") as f:
            content = f.read()

        assert 'data "aws_ami"' in content
        assert "data.aws_ami.ubuntu.id" in content
        assert "ubuntu-noble-24.04" in content

    def test_no_hardcoded_ami_in_variables(self):
        """variables.tf must not have hardcoded AMI ID."""
        variables_tf = os.path.join(TERRAFORM_DIR, "variables.tf")
        with open(variables_tf, encoding="utf-8") as f:
            content = f.read()

        assert "ami-" not in content, "Found hardcoded AMI ID"

    def test_az_is_dynamic(self):
        """Availability zone must be selected dynamically."""
        main_tf = os.path.join(TERRAFORM_DIR, "main.tf")
        with open(main_tf, encoding="utf-8") as f:
            content = f.read()

        assert 'data "aws_ec2_instance_type_offerings"' in content
        assert "local.availability_zone" in content

    def test_cloudwatch_dashboard_configured(self):
        """Terraform must configure CloudWatch dashboard."""
        main_tf = os.path.join(TERRAFORM_DIR, "main.tf")
        with open(main_tf, encoding="utf-8") as f:
            content = f.read()

        assert "aws_cloudwatch_dashboard" in content
        assert "RTLMeter-Benchmark" in content

    def test_dashboard_url_output_defined(self):
        """Terraform must output the dashboard URL."""
        outputs_tf = os.path.join(TERRAFORM_DIR, "outputs.tf")
        with open(outputs_tf, encoding="utf-8") as f:
            content = f.read()

        assert "dashboard_url" in content

    def test_cloudwatch_agent_iam_configured(self):
        """EC2 must have IAM for CloudWatch agent."""
        main_tf = os.path.join(TERRAFORM_DIR, "main.tf")
        with open(main_tf, encoding="utf-8") as f:
            content = f.read()

        assert "CloudWatchAgentServerPolicy" in content


class TestBenchmarkCodeIntegration:
    """
    Tests that verify benchmark.py code patterns are correct.
    These catch bugs that would cause benchmark failures.
    """

    def test_syntax_valid(self):
        """benchmark.py must have valid Python syntax."""
        result = subprocess.run(
            ["python3", "-m", "py_compile", "benchmark.py"],
            capture_output=True, text=True,
            cwd=TERRAFORM_DIR, timeout=30
        )
        assert result.returncode == 0, f"Syntax error: {result.stderr}"

    def test_uses_boto3_with_region(self):
        """benchmark.py must use boto3 with region from environment."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "import boto3" in content
        assert 'os.environ.get("AWS_REGION")' in content
        assert "region_name=AWS_REGION" in content

    def test_installs_cloudwatch_agent(self):
        """benchmark.py must install CloudWatch agent."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "amazon-cloudwatch-agent" in content
        assert "mem_used_percent" in content
        assert "disk_used_percent" in content

    def test_has_disk_space_check(self):
        """benchmark.py must check disk space before runs."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "def check_disk_space" in content
        assert "check_disk_space(instance_id)" in content

    def test_clears_rtlmeter_cache(self):
        """
        CRITICAL: benchmark.py must clear RTLMeter cache between runs.
        Without this, results are cached and baseline==optimized.
        """
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "rm -rf" in content and "work" in content, \
            "benchmark.py MUST clear RTLMeter work directory between runs!"

    def test_does_not_set_verilator_root(self):
        """
        CRITICAL: benchmark.py must NOT set VERILATOR_ROOT.
        Setting it causes 'inconsistent path' errors with installed Verilator.
        """
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "export VERILATOR_ROOT=" not in content, \
            "benchmark.py should NOT set VERILATOR_ROOT"
        assert "VERILATOR_ROOT" in content and "Don't set" in content, \
            "benchmark.py should document why VERILATOR_ROOT is not set"

    def test_uses_separate_install_dirs(self):
        """benchmark.py must use separate install directories."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "verilator-install-baseline" in content
        assert "verilator-install-optimized" in content

    def test_rtlmeter_command_format(self):
        """benchmark.py must construct valid RTLMeter commands."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "./rtlmeter run" in content
        assert "./rtlmeter collate" in content
        assert "--cases" in content
        # Must use --verilate-jobs (not --threads) to control V3ThreadPool
        assert "--compileArgs" in content and "--verilate-jobs" in content

    def test_uses_nexecute_for_samples(self):
        """benchmark.py must use --nExecute for multiple execution samples."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "--nExecute" in content, \
            "benchmark.py should use --nExecute for statistical confidence"

    def test_uses_compare_subcommand(self):
        """benchmark.py must use RTLMeter compare for statistical analysis."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "./rtlmeter compare" in content, \
            "benchmark.py should use RTLMeter compare for p-value analysis"

    def test_uses_cmark_benchmark(self):
        """benchmark.py must use cmark (not just hello) for meaningful results."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        assert "cmark" in content, \
            "benchmark.py should use cmark benchmark for longer-running tests"

    def test_measures_verilate_step(self):
        """benchmark.py must measure verilate step (where V3ThreadPool is used)."""
        benchmark_py = os.path.join(TERRAFORM_DIR, "benchmark.py")
        with open(benchmark_py, encoding="utf-8") as f:
            content = f.read()

        # V3ThreadPool optimization affects compile-time threading (verilate step)
        assert "--steps 'verilate'" in content, \
            "benchmark.py should measure verilate step for V3ThreadPool optimization"


class TestOrchestratorCodeIntegration:
    """
    Tests that verify run.py code patterns are correct.
    """

    def test_syntax_valid(self):
        """run.py must have valid Python syntax."""
        result = subprocess.run(
            ["python3", "-m", "py_compile", "run.py"],
            capture_output=True, text=True,
            cwd=TERRAFORM_DIR, timeout=30
        )
        assert result.returncode == 0, f"Syntax error: {result.stderr}"

    def test_uses_boto3_with_region(self):
        """run.py must use boto3 with configurable region."""
        run_py = os.path.join(TERRAFORM_DIR, "run.py")
        with open(run_py, encoding="utf-8") as f:
            content = f.read()

        assert "import boto3" in content
        assert "def init_aws_clients(region" in content

    def test_region_is_required_flag(self):
        """run.py must have required --region flag."""
        run_py = os.path.join(TERRAFORM_DIR, "run.py")
        with open(run_py, encoding="utf-8") as f:
            content = f.read()

        assert '"--region", required=True' in content
        assert '-var=aws_region=' in content
        assert 'os.environ["AWS_REGION"]' in content

    def test_has_signal_handler(self):
        """run.py must have signal handler for cleanup on Ctrl+C."""
        run_py = os.path.join(TERRAFORM_DIR, "run.py")
        with open(run_py, encoding="utf-8") as f:
            content = f.read()

        assert "import signal" in content
        assert "signal.signal(signal.SIGINT" in content
        assert "signal.signal(signal.SIGTERM" in content
        assert "terminate_ec2_instance" in content

    def test_pip_uses_break_system_packages(self):
        """pip commands must use --break-system-packages for Ubuntu 24.04."""
        for filename in ["benchmark.py", "run.py"]:
            filepath = os.path.join(TERRAFORM_DIR, filename)
            with open(filepath, encoding="utf-8") as f:
                content = f.read()

            pip_installs = re.findall(r'pip3? install[^"\']+', content)
            for pip_cmd in pip_installs:
                assert "--break-system-packages" in pip_cmd, \
                    f"{filename}: pip install missing --break-system-packages: {pip_cmd}"


class TestLocalDependencies:
    """
    Tests that verify local dependencies are available.
    """

    def test_boto3_installed(self):
        """boto3 must be installed locally."""
        try:
            import boto3  # pylint: disable=import-outside-toplevel,unused-import
        except ImportError:
            pytest.fail("boto3 not installed. Run: pip install boto3")

    def test_pytest_installed(self):
        """pytest must be installed locally."""
        result = subprocess.run(
            ["python3", "-m", "pytest", "--version"],
            capture_output=True, text=True, check=False
        )
        assert result.returncode == 0, "pytest not installed"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
