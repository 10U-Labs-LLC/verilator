#!/usr/bin/env python3
"""
Unit tests for benchmark scripts.

These tests verify individual functions work correctly with mocked dependencies.
Run with: pytest test_unit.py -v
"""

import json
import os
import subprocess
from unittest.mock import MagicMock, patch, call

import pytest

# Set AWS_REGION for benchmark.py import (required at module level)
os.environ.setdefault("AWS_REGION", "us-east-2")


# ===========================================================================
# Tests for benchmark.py functions
# ===========================================================================

class TestBenchmarkRunCmd:
    """Unit tests for benchmark.run_cmd()."""

    def test_run_cmd_success(self):
        """run_cmd returns result on success."""
        from benchmark import run_cmd

        with patch("benchmark.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout="output",
                stderr=""
            )
            result = run_cmd(["echo", "test"])

            assert result.returncode == 0
            assert result.stdout == "output"

    def test_run_cmd_failure_raises(self):
        """run_cmd raises on failure when check=True."""
        from benchmark import run_cmd

        with patch("benchmark.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=1,
                stdout="",
                stderr="error"
            )

            with pytest.raises(RuntimeError, match="Command failed"):
                run_cmd(["false"], check=True)

    def test_run_cmd_failure_no_raise(self):
        """run_cmd returns result on failure when check=False."""
        from benchmark import run_cmd

        with patch("benchmark.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=1,
                stdout="",
                stderr="error"
            )
            result = run_cmd(["false"], check=False)

            assert result.returncode == 1


class TestBenchmarkGetMetric:
    """Unit tests for benchmark.get_metric()."""

    def test_get_metric_returns_value(self):
        """get_metric returns metric value from CloudWatch."""
        # Mock the cloudwatch client
        mock_cloudwatch = MagicMock()
        mock_cloudwatch.get_metric_statistics.return_value = {
            "Datapoints": [
                {"Timestamp": "2024-01-01T00:00:00Z", "Average": 42.5},
                {"Timestamp": "2024-01-01T00:01:00Z", "Average": 43.0},
            ]
        }

        with patch("benchmark.cloudwatch", mock_cloudwatch):
            from benchmark import get_metric

            result = get_metric("AWS/EC2", "CPUUtilization", "i-123456")

            assert result == 43.0  # Latest timestamp

    def test_get_metric_returns_none_on_no_data(self):
        """get_metric returns None when no datapoints."""
        mock_cloudwatch = MagicMock()
        mock_cloudwatch.get_metric_statistics.return_value = {
            "Datapoints": []
        }

        with patch("benchmark.cloudwatch", mock_cloudwatch):
            from benchmark import get_metric

            result = get_metric("AWS/EC2", "CPUUtilization", "i-123456")

            assert result is None

    def test_get_metric_returns_none_on_exception(self):
        """get_metric returns None on CloudWatch exception."""
        mock_cloudwatch = MagicMock()
        mock_cloudwatch.get_metric_statistics.side_effect = Exception("API error")

        with patch("benchmark.cloudwatch", mock_cloudwatch):
            from benchmark import get_metric

            result = get_metric("AWS/EC2", "CPUUtilization", "i-123456")

            assert result is None


class TestBenchmarkGetInstanceMetrics:
    """Unit tests for benchmark.get_instance_metrics()."""

    def test_formats_metrics_correctly(self):
        """get_instance_metrics formats values with units."""
        with patch("benchmark.get_metric") as mock_get:
            # Return different values for different metrics
            def metric_side_effect(namespace, metric_name, instance_id, **kwargs):
                if metric_name == "CPUUtilization":
                    return 75.5
                if metric_name == "NetworkIn":
                    return 2 * 1024 * 1024  # 2MB
                if metric_name == "NetworkOut":
                    return 512 * 1024  # 512KB
                if metric_name == "mem_used_percent":
                    return 60.2
                if metric_name == "disk_used_percent":
                    return 45.8
                return None

            mock_get.side_effect = metric_side_effect

            from benchmark import get_instance_metrics

            metrics = get_instance_metrics("i-123456")

            assert metrics["cpu"] == "75.5%"
            assert metrics["net_in"] == "2.0MB"
            assert metrics["net_out"] == "512.0KB"
            assert metrics["mem"] == "60.2%"
            assert metrics["disk"] == "45.8%"

    def test_handles_missing_metrics(self):
        """get_instance_metrics returns '...' for missing metrics."""
        with patch("benchmark.get_metric", return_value=None):
            from benchmark import get_instance_metrics

            metrics = get_instance_metrics("i-123456")

            assert metrics["cpu"] == "..."
            assert metrics["mem"] == "..."


class TestBenchmarkWaitForSSM:
    """Unit tests for benchmark.wait_for_ssm()."""

    def test_wait_for_ssm_success(self):
        """wait_for_ssm returns when agent is online."""
        mock_ssm = MagicMock()
        mock_ssm.describe_instance_information.return_value = {
            "InstanceInformationList": [{"PingStatus": "Online"}]
        }

        with patch("benchmark.ssm", mock_ssm), \
             patch("benchmark.time.sleep"):
            from benchmark import wait_for_ssm

            # Should not raise
            wait_for_ssm("i-123456", timeout=10)

    def test_wait_for_ssm_timeout(self):
        """wait_for_ssm raises on timeout."""
        mock_ssm = MagicMock()
        mock_ssm.describe_instance_information.return_value = {
            "InstanceInformationList": []
        }

        with patch("benchmark.ssm", mock_ssm), \
             patch("benchmark.time.sleep"), \
             patch("benchmark.time.time") as mock_time:
            # Simulate timeout
            mock_time.side_effect = [0, 100, 200, 300, 400]

            from benchmark import wait_for_ssm

            with pytest.raises(TimeoutError):
                wait_for_ssm("i-123456", timeout=10)


# ===========================================================================
# Tests for run.py functions
# ===========================================================================

class TestRunPyRunCmd:
    """Unit tests for run.run_cmd()."""

    def test_run_cmd_returns_true_on_success(self):
        """run_cmd returns True when command succeeds."""
        with patch("run.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=0)

            # Import after patching
            import run
            result = run.run_cmd(["echo", "test"], "Test command")

            assert result is True

    def test_run_cmd_returns_false_on_failure(self):
        """run_cmd returns False when command fails."""
        with patch("run.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=1)

            import run
            result = run.run_cmd(["false"], "Failing command")

            assert result is False


class TestRunPyGetInstanceId:
    """Unit tests for run.get_instance_id()."""

    def test_get_instance_id_returns_id(self):
        """get_instance_id returns instance ID from terraform output."""
        with patch("run.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout="i-1234567890abcdef0"
            )

            import run
            result = run.get_instance_id()

            assert result == "i-1234567890abcdef0"

    def test_get_instance_id_returns_none_on_failure(self):
        """get_instance_id returns None when terraform fails."""
        with patch("run.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=1,
                stdout=""
            )

            import run
            result = run.get_instance_id()

            assert result is None

    def test_get_instance_id_returns_none_on_empty(self):
        """get_instance_id returns None when output is empty."""
        with patch("run.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout="   "
            )

            import run
            result = run.get_instance_id()

            assert result is None


class TestRunPySSMSendCommand:
    """Unit tests for run.ssm_send_command()."""

    def test_ssm_send_command_success(self):
        """ssm_send_command returns output on success."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Success",
            "StandardOutputContent": "output",
            "StandardErrorContent": ""
        }

        with patch("run._ssm", mock_ssm), \
             patch("run.time.sleep"):
            import run
            result = run.ssm_send_command("i-123", ["echo test"])

            assert result == ("output", "")

    def test_ssm_send_command_failure(self):
        """ssm_send_command returns None on failure."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Failed",
            "StandardOutputContent": "",
            "StandardErrorContent": "error"
        }

        with patch("run._ssm", mock_ssm), \
             patch("run.time.sleep"):
            import run
            result = run.ssm_send_command("i-123", ["false"])

            assert result is None


class TestRunPyTerminateEC2:
    """Unit tests for run.terminate_ec2_instance()."""

    def test_terminate_ec2_success(self):
        """terminate_ec2_instance returns True on success."""
        mock_ec2 = MagicMock()

        with patch("run._ec2", mock_ec2):
            import run
            result = run.terminate_ec2_instance("i-123456")

            assert result is True
            mock_ec2.terminate_instances.assert_called_once_with(
                InstanceIds=["i-123456"]
            )

    def test_terminate_ec2_failure(self):
        """terminate_ec2_instance returns False on exception."""
        mock_ec2 = MagicMock()
        mock_ec2.terminate_instances.side_effect = Exception("API error")

        with patch("run._ec2", mock_ec2):
            import run
            result = run.terminate_ec2_instance("i-123456")

            assert result is False


# ===========================================================================
# Tests for conftest.py SSMRunner
# ===========================================================================

class TestSSMRunner:
    """Unit tests for conftest.SSMRunner."""

    def test_run_success(self):
        """SSMRunner.run returns (0, stdout, stderr) on success."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Success",
            "StandardOutputContent": "output",
            "StandardErrorContent": "warning"
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")
            rc, stdout, stderr = runner.run("echo test")

            assert rc == 0
            assert stdout == "output"
            assert stderr == "warning"

    def test_run_failure(self):
        """SSMRunner.run returns (1, stdout, stderr) on failure."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Failed",
            "StandardOutputContent": "",
            "StandardErrorContent": "error"
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")
            rc, stdout, stderr = runner.run("false")

            assert rc == 1

    def test_run_check_raises_on_failure(self):
        """SSMRunner.run_check raises AssertionError on failure."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Failed",
            "StandardOutputContent": "",
            "StandardErrorContent": "error"
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")

            with pytest.raises(AssertionError, match="Command failed"):
                runner.run_check("false")

    def test_file_exists_true(self):
        """SSMRunner.file_exists returns True when file exists."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Success",
            "StandardOutputContent": "",
            "StandardErrorContent": ""
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")
            result = runner.file_exists("/path/to/file")

            assert result is True

    def test_file_exists_false(self):
        """SSMRunner.file_exists returns False when file doesn't exist."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Failed",
            "StandardOutputContent": "",
            "StandardErrorContent": ""
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")
            result = runner.file_exists("/nonexistent")

            assert result is False

    def test_dir_exists_true(self):
        """SSMRunner.dir_exists returns True when directory exists."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Success",
            "StandardOutputContent": "",
            "StandardErrorContent": ""
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")
            result = runner.dir_exists("/home/ubuntu")

            assert result is True

    def test_dir_exists_false(self):
        """SSMRunner.dir_exists returns False when directory doesn't exist."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Failed",
            "StandardOutputContent": "",
            "StandardErrorContent": ""
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")
            result = runner.dir_exists("/nonexistent")

            assert result is False

    def test_read_file_success(self):
        """SSMRunner.read_file returns file contents."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Success",
            "StandardOutputContent": "file contents here",
            "StandardErrorContent": ""
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")
            result = runner.read_file("/path/to/file")

            assert result == "file contents here"

    def test_read_file_failure_raises(self):
        """SSMRunner.read_file raises on failure."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Failed",
            "StandardOutputContent": "",
            "StandardErrorContent": "No such file"
        }

        with patch("conftest.boto3.client", return_value=mock_ssm), \
             patch("conftest.time.sleep"):
            from conftest import SSMRunner

            runner = SSMRunner("i-123", "us-east-2")

            with pytest.raises(AssertionError, match="Command failed"):
                runner.read_file("/nonexistent")


# ===========================================================================
# Tests for run.py additional functions
# ===========================================================================

class TestRunPyGetS3Bucket:
    """Unit tests for run.get_s3_bucket()."""

    def test_get_s3_bucket_returns_bucket(self):
        """get_s3_bucket returns bucket name from terraform output."""
        with patch("run.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout="rtlmeter-results-12345"
            )

            import run
            result = run.get_s3_bucket()

            assert result == "rtlmeter-results-12345"

    def test_get_s3_bucket_returns_none_on_failure(self):
        """get_s3_bucket returns None when terraform fails."""
        with patch("run.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=1,
                stdout=""
            )

            import run
            result = run.get_s3_bucket()

            assert result is None

    def test_get_s3_bucket_returns_none_on_empty(self):
        """get_s3_bucket returns None when output is empty."""
        with patch("run.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout="   "
            )

            import run
            result = run.get_s3_bucket()

            assert result is None


# ===========================================================================
# Tests for benchmark.py additional functions
# ===========================================================================

class TestBenchmarkCheckDiskSpace:
    """Unit tests for benchmark.check_disk_space()."""

    def test_check_disk_space_below_threshold(self):
        """check_disk_space prints usage when below threshold."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Success",
            "StandardOutputContent": "45",
            "StandardErrorContent": ""
        }

        with patch("benchmark.ssm", mock_ssm), \
             patch("benchmark.time.sleep"), \
             patch("builtins.print") as mock_print:
            from benchmark import check_disk_space

            check_disk_space("i-123456", warn_threshold=80)

            # Should print usage without warning
            mock_print.assert_called_with("[Disk: 45% used]")

    def test_check_disk_space_above_threshold(self):
        """check_disk_space prints warning when above threshold."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.return_value = {
            "Command": {"CommandId": "cmd-123"}
        }
        mock_ssm.get_command_invocation.return_value = {
            "Status": "Success",
            "StandardOutputContent": "85",
            "StandardErrorContent": ""
        }

        with patch("benchmark.ssm", mock_ssm), \
             patch("benchmark.time.sleep"), \
             patch("builtins.print") as mock_print:
            from benchmark import check_disk_space

            check_disk_space("i-123456", warn_threshold=80)

            # Should print warning
            calls = [str(c) for c in mock_print.call_args_list]
            assert any("WARNING" in c for c in calls)

    def test_check_disk_space_handles_failure(self):
        """check_disk_space handles SSM failure gracefully."""
        mock_ssm = MagicMock()
        mock_ssm.send_command.side_effect = Exception("SSM error")

        with patch("benchmark.ssm", mock_ssm), \
             patch("benchmark.time.sleep"):
            from benchmark import check_disk_space

            # Should not raise
            check_disk_space("i-123456")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
