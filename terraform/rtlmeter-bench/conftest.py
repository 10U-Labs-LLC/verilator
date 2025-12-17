"""
Pytest configuration and fixtures for RTLMeter benchmark tests.

Provides SSM-based remote execution for tests that need to run commands on EC2.
"""

import os
import subprocess
import time
from typing import Generator

import pytest
import boto3


# Test categories
def pytest_configure(config):
    """Register custom markers."""
    config.addinivalue_line(
        "markers",
        "remote: mark test as requiring EC2 instance (runs commands via SSM)"
    )
    config.addinivalue_line(
        "markers",
        "slow: mark test as slow-running"
    )


# ---------------------------------------------------------------------------
# SSM Remote Execution Infrastructure
# ---------------------------------------------------------------------------

class SSMRunner:
    """Execute commands on EC2 via SSM."""

    def __init__(self, instance_id: str, region: str):
        self.instance_id = instance_id
        self.region = region
        self.ssm = boto3.client("ssm", region_name=region)

    def run(self, command: str, timeout: int = 120) -> tuple[int, str, str]:
        """
        Run a command on EC2 via SSM.

        Returns: (return_code, stdout, stderr)
        """
        try:
            response = self.ssm.send_command(
                InstanceIds=[self.instance_id],
                DocumentName="AWS-RunShellScript",
                Parameters={"commands": [command]},
                TimeoutSeconds=timeout
            )
            command_id = response["Command"]["CommandId"]

            # Poll for completion
            for _ in range(timeout // 2):
                time.sleep(2)
                try:
                    invocation = self.ssm.get_command_invocation(
                        CommandId=command_id,
                        InstanceId=self.instance_id
                    )
                    status = invocation["Status"]

                    if status == "Success":
                        return (
                            0,
                            invocation.get("StandardOutputContent", ""),
                            invocation.get("StandardErrorContent", "")
                        )
                    if status in ("Failed", "Cancelled", "TimedOut"):
                        return (
                            1,
                            invocation.get("StandardOutputContent", ""),
                            invocation.get("StandardErrorContent", "")
                        )
                except self.ssm.exceptions.InvocationDoesNotExist:
                    pass
                except Exception:
                    pass

            return (1, "", "SSM command timed out")

        except Exception as e:
            return (1, "", f"SSM error: {e}")

    def run_check(self, command: str, timeout: int = 120) -> tuple[str, str]:
        """
        Run a command on EC2 via SSM, raising on failure.

        Returns: (stdout, stderr)
        Raises: AssertionError if command fails
        """
        rc, stdout, stderr = self.run(command, timeout)
        assert rc == 0, f"Command failed: {command}\nSTDERR: {stderr}\nSTDOUT: {stdout}"
        return stdout, stderr

    def file_exists(self, path: str) -> bool:
        """Check if a file exists on EC2."""
        rc, _, _ = self.run(f"test -f {path}")
        return rc == 0

    def dir_exists(self, path: str) -> bool:
        """Check if a directory exists on EC2."""
        rc, _, _ = self.run(f"test -d {path}")
        return rc == 0

    def read_file(self, path: str) -> str:
        """Read a file from EC2."""
        stdout, _ = self.run_check(f"cat {path}")
        return stdout


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

def get_instance_id() -> str | None:
    """Get instance ID from Terraform output."""
    result = subprocess.run(
        ["terraform", "output", "-raw", "instance_id"],
        capture_output=True, text=True, check=False
    )
    if result.returncode == 0 and result.stdout.strip():
        return result.stdout.strip()
    return None


def get_aws_region() -> str:
    """Get AWS region from environment or default."""
    return os.environ.get("AWS_REGION", "us-east-2")


@pytest.fixture(scope="session")
def aws_region() -> str:
    """AWS region for tests."""
    return get_aws_region()


@pytest.fixture(scope="session")
def instance_id() -> str | None:
    """EC2 instance ID from Terraform output."""
    return get_instance_id()


@pytest.fixture(scope="session")
def ssm(instance_id: str | None, aws_region: str) -> SSMRunner | None:
    """SSM runner for remote command execution."""
    if not instance_id:
        return None
    return SSMRunner(instance_id, aws_region)


@pytest.fixture
def require_instance(instance_id: str | None) -> str:
    """Skip test if no EC2 instance is available."""
    if not instance_id:
        pytest.skip("No EC2 instance available (run terraform apply first)")
    return instance_id


@pytest.fixture
def require_ssm(ssm: SSMRunner | None, require_instance: str) -> SSMRunner:
    """Skip test if SSM is not available."""
    if not ssm:
        pytest.skip("SSM not available")
    return ssm


# ---------------------------------------------------------------------------
# Remote Path Constants (available as fixtures)
# ---------------------------------------------------------------------------

@pytest.fixture(scope="session")
def benchmark_dir() -> str:
    """Benchmark directory on EC2."""
    return "/home/ubuntu/benchmark"


@pytest.fixture(scope="session")
def baseline_dir(benchmark_dir: str) -> str:
    """Baseline Verilator install directory on EC2."""
    return f"{benchmark_dir}/verilator-install-baseline"


@pytest.fixture(scope="session")
def optimized_dir(benchmark_dir: str) -> str:
    """Optimized Verilator install directory on EC2."""
    return f"{benchmark_dir}/verilator-install-optimized"


@pytest.fixture(scope="session")
def rtlmeter_dir(benchmark_dir: str) -> str:
    """RTLMeter directory on EC2."""
    return f"{benchmark_dir}/rtlmeter"


@pytest.fixture(scope="session")
def verilator_src(benchmark_dir: str) -> str:
    """Verilator source directory on EC2."""
    return f"{benchmark_dir}/verilator"
