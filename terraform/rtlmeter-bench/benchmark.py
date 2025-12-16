#!/usr/bin/env python3
"""
RTLMeter benchmark runner using AWS SSM.
Compares baseline (upstream master) vs optimized (current branch) for V3ThreadPool wait().
"""

import subprocess
import json
import time
import sys
from pathlib import Path

# Repository URLs
UPSTREAM_REPO = "https://github.com/verilator/verilator.git"
FORK_REPO = "https://github.com/10U-Labs-LLC/verilator.git"

# Current branch with optimization
OPTIMIZED_BRANCH = "optimize-threadpool-wait-cv"


def run_cmd(cmd: list[str], check: bool = True) -> subprocess.CompletedProcess:
    """Run a local command and return result."""
    print(f"$ {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True)
    if check and result.returncode != 0:
        print(f"STDERR: {result.stderr}")
        raise RuntimeError(f"Command failed: {' '.join(cmd)}")
    return result


def wait_for_ssm(instance_id: str, timeout: int = 300) -> None:
    """Wait for SSM agent to be ready on the instance."""
    print(f"Waiting for SSM agent on {instance_id}...")
    start = time.time()
    while time.time() - start < timeout:
        result = run_cmd([
            "aws", "ssm", "describe-instance-information",
            "--filters", f"Key=InstanceIds,Values={instance_id}",
            "--query", "InstanceInformationList[0].PingStatus",
            "--output", "text"
        ], check=False)
        if result.stdout.strip() == "Online":
            print("SSM agent is online!")
            return
        print(".", end="", flush=True)
        time.sleep(10)
    raise TimeoutError("SSM agent did not come online in time")


def get_instance_metrics(instance_id: str) -> dict:
    """Get current CloudWatch metrics for the instance."""
    from datetime import datetime, timedelta

    end_time = datetime.utcnow()
    start_time = end_time - timedelta(minutes=5)

    metrics = {}

    # Get CPU utilization (AWS/EC2 namespace)
    result = run_cmd([
        "aws", "cloudwatch", "get-metric-statistics",
        "--namespace", "AWS/EC2",
        "--metric-name", "CPUUtilization",
        "--dimensions", f"Name=InstanceId,Value={instance_id}",
        "--start-time", start_time.isoformat() + "Z",
        "--end-time", end_time.isoformat() + "Z",
        "--period", "60",
        "--statistics", "Average",
        "--output", "json"
    ], check=False)

    if result.returncode == 0:
        data = json.loads(result.stdout)
        datapoints = data.get("Datapoints", [])
        if datapoints:
            latest = max(datapoints, key=lambda x: x["Timestamp"])
            metrics["cpu"] = f"{latest['Average']:.1f}%"
        else:
            metrics["cpu"] = "..."

    # Get network in/out (AWS/EC2 namespace)
    for metric_name, key in [("NetworkIn", "net_in"), ("NetworkOut", "net_out")]:
        result = run_cmd([
            "aws", "cloudwatch", "get-metric-statistics",
            "--namespace", "AWS/EC2",
            "--metric-name", metric_name,
            "--dimensions", f"Name=InstanceId,Value={instance_id}",
            "--start-time", start_time.isoformat() + "Z",
            "--end-time", end_time.isoformat() + "Z",
            "--period", "60",
            "--statistics", "Sum",
            "--output", "json"
        ], check=False)

        if result.returncode == 0:
            data = json.loads(result.stdout)
            datapoints = data.get("Datapoints", [])
            if datapoints:
                latest = max(datapoints, key=lambda x: x["Timestamp"])
                bytes_val = latest["Sum"]
                if bytes_val > 1024*1024:
                    metrics[key] = f"{bytes_val/1024/1024:.1f}MB"
                else:
                    metrics[key] = f"{bytes_val/1024:.1f}KB"
            else:
                metrics[key] = "..."

    # Get memory used percent (RTLMeter namespace - from CloudWatch agent)
    result = run_cmd([
        "aws", "cloudwatch", "get-metric-statistics",
        "--namespace", "RTLMeter",
        "--metric-name", "mem_used_percent",
        "--dimensions", f"Name=InstanceId,Value={instance_id}",
        "--start-time", start_time.isoformat() + "Z",
        "--end-time", end_time.isoformat() + "Z",
        "--period", "60",
        "--statistics", "Average",
        "--output", "json"
    ], check=False)

    if result.returncode == 0:
        data = json.loads(result.stdout)
        datapoints = data.get("Datapoints", [])
        if datapoints:
            latest = max(datapoints, key=lambda x: x["Timestamp"])
            metrics["mem"] = f"{latest['Average']:.1f}%"
        else:
            metrics["mem"] = "..."

    # Get disk used percent (RTLMeter namespace - from CloudWatch agent)
    result = run_cmd([
        "aws", "cloudwatch", "get-metric-statistics",
        "--namespace", "RTLMeter",
        "--metric-name", "disk_used_percent",
        "--dimensions", f"Name=InstanceId,Value={instance_id}",
        "Name=path,Value=/", "Name=fstype,Value=ext4",
        "--start-time", start_time.isoformat() + "Z",
        "--end-time", end_time.isoformat() + "Z",
        "--period", "60",
        "--statistics", "Average",
        "--output", "json"
    ], check=False)

    if result.returncode == 0:
        data = json.loads(result.stdout)
        datapoints = data.get("Datapoints", [])
        if datapoints:
            latest = max(datapoints, key=lambda x: x["Timestamp"])
            metrics["disk"] = f"{latest['Average']:.1f}%"
        else:
            metrics["disk"] = "..."

    return metrics


def print_instance_status(instance_id: str) -> None:
    """Print current instance status and metrics."""
    metrics = get_instance_metrics(instance_id)
    status_line = (
        f"[EC2] CPU: {metrics.get('cpu', '...')} | "
        f"RAM: {metrics.get('mem', '...')} | "
        f"Disk: {metrics.get('disk', '...')} | "
        f"Net: {metrics.get('net_in', '...')}/{metrics.get('net_out', '...')}"
    )
    print(f"\r{status_line}", end="", flush=True)


def ssm_run(instance_id: str, commands: list[str], timeout: int = 3600) -> str:
    """Run commands on instance via SSM and return output with live streaming."""
    command_str = " && ".join(commands)

    result = run_cmd([
        "aws", "ssm", "send-command",
        "--instance-ids", instance_id,
        "--document-name", "AWS-RunShellScript",
        "--parameters", json.dumps({"commands": [command_str]}),
        "--timeout-seconds", str(timeout),
        "--cloud-watch-output-config",
        json.dumps({"CloudWatchOutputEnabled": False}),
        "--output", "json"
    ])

    cmd_data = json.loads(result.stdout)
    command_id = cmd_data["Command"]["CommandId"]
    print(f"SSM command {command_id} sent, streaming output...")
    print("-" * 60)

    last_stdout_len = 0
    last_stderr_len = 0
    poll_count = 0

    while True:
        time.sleep(10)
        poll_count += 1

        result = run_cmd([
            "aws", "ssm", "get-command-invocation",
            "--command-id", command_id,
            "--instance-id", instance_id,
            "--output", "json"
        ], check=False)

        if result.returncode != 0:
            continue

        invocation = json.loads(result.stdout)
        status = invocation["Status"]

        # Stream new output as it arrives
        stdout = invocation.get("StandardOutputContent", "")
        stderr = invocation.get("StandardErrorContent", "")

        if len(stdout) > last_stdout_len:
            new_output = stdout[last_stdout_len:]
            print(new_output, end="", flush=True)
            last_stdout_len = len(stdout)

        if len(stderr) > last_stderr_len:
            new_err = stderr[last_stderr_len:]
            print(f"[STDERR] {new_err}", end="", flush=True)
            last_stderr_len = len(stderr)

        # Print EC2 metrics every 30 seconds (every 3 polls)
        if poll_count % 3 == 0 and status == "InProgress":
            print()  # Newline before status
            print_instance_status(instance_id)
            print()  # Newline after status

        if status == "Success":
            print("\n" + "-" * 60)
            print("Command completed successfully")
            return stdout
        elif status in ("Failed", "Cancelled", "TimedOut"):
            print("\n" + "-" * 60)
            print(f"Command {status}")
            if stderr:
                print(f"STDERR: {stderr}")
            raise RuntimeError(f"SSM command {status}")


def setup_instance(instance_id: str) -> None:
    """Install dependencies and clone repositories."""
    print("\n=== Setting up instance ===")

    setup_commands = [
        "sudo apt-get update",
        "sudo DEBIAN_FRONTEND=noninteractive apt-get upgrade -y",
        "sudo DEBIAN_FRONTEND=noninteractive apt-get install -y "
        "git perl python3 python3-pip make autoconf g++ flex bison ccache "
        "libgoogle-perftools-dev numactl perl-doc libfl2 libfl-dev zlib1g zlib1g-dev "
        "help2man awscli",
        # Install CloudWatch agent for memory/disk metrics
        "wget -q https://s3.amazonaws.com/amazoncloudwatch-agent/ubuntu/amd64/latest/amazon-cloudwatch-agent.deb",
        "sudo dpkg -i amazon-cloudwatch-agent.deb",
        # Configure CloudWatch agent for memory and disk metrics
        """sudo tee /opt/aws/amazon-cloudwatch-agent/etc/amazon-cloudwatch-agent.json << 'CWCONFIG'
{
  "metrics": {
    "namespace": "RTLMeter",
    "metrics_collected": {
      "mem": {
        "measurement": ["mem_used_percent", "mem_available"],
        "metrics_collection_interval": 60
      },
      "disk": {
        "measurement": ["disk_used_percent", "disk_free"],
        "resources": ["/"],
        "metrics_collection_interval": 60
      },
      "diskio": {
        "measurement": ["read_bytes", "write_bytes", "reads", "writes"],
        "resources": ["*"],
        "metrics_collection_interval": 60
      }
    }
  }
}
CWCONFIG""",
        "sudo /opt/aws/amazon-cloudwatch-agent/bin/amazon-cloudwatch-agent-ctl -a fetch-config -m ec2 -s -c file:/opt/aws/amazon-cloudwatch-agent/etc/amazon-cloudwatch-agent.json",
        "pip3 install --user pyyaml tabulate scipy",
        "mkdir -p /home/ubuntu/benchmark",
        # Clone from fork (has both upstream tracking and our branch)
        f"cd /home/ubuntu/benchmark && git clone {FORK_REPO} verilator",
        # Add upstream remote for baseline builds
        f"cd /home/ubuntu/benchmark/verilator && git remote add upstream {UPSTREAM_REPO}",
        "cd /home/ubuntu/benchmark/verilator && git fetch upstream",
        # Clone RTLMeter
        "cd /home/ubuntu/benchmark && git clone https://github.com/verilator/rtlmeter.git",
        "cd /home/ubuntu/benchmark/rtlmeter && make venv",
    ]

    ssm_run(instance_id, setup_commands, timeout=1800)
    print("Instance setup complete!")


def build_verilator(instance_id: str, label: str, git_ref: str,
                    install_dir: str) -> None:
    """Build Verilator at specified git ref into install_dir."""
    print(f"\n=== Building Verilator ({label}) at {git_ref} ===")

    build_commands = [
        "cd /home/ubuntu/benchmark/verilator",
        f"git checkout {git_ref}",
        "git clean -fdx",
        "autoconf",
        f"./configure --prefix={install_dir}",
        "make -j$(nproc)",
        "make install",
    ]

    ssm_run(instance_id, build_commands, timeout=1800)
    print(f"Verilator ({label}) built successfully!")


def run_rtlmeter(instance_id: str, label: str, install_dir: str,
                 threads: int) -> str:
    """Run RTLMeter benchmarks and return results."""
    print(f"\n=== Running RTLMeter ({label}, threads={threads}) ===")

    benchmark_commands = [
        "cd /home/ubuntu/benchmark/rtlmeter",
        f"export PATH={install_dir}/bin:$PATH",
        f"export VERILATOR_ROOT={install_dir}",
        f"./rtlmeter run --timeout 120 --verbose "
        f"--cases 'VeeR-EH1:default:*' "
        f"--compileArgs '--threads {threads}'",
        f"./rtlmeter collate --runName '{label}-t{threads}' > /home/ubuntu/benchmark/results_{label}_t{threads}.json",
        f"./rtlmeter report --steps '*' --metrics '*' /home/ubuntu/benchmark/results_{label}_t{threads}.json",
    ]

    output = ssm_run(instance_id, benchmark_commands, timeout=3600)
    return output


def main():
    tf_dir = Path(__file__).parent
    import os
    os.chdir(tf_dir)

    print("=== RTLMeter Benchmark Runner ===\n")

    result = run_cmd(["terraform", "output", "-raw", "instance_id"], check=False)
    if result.returncode != 0 or not result.stdout.strip():
        print("No instance found. Run 'terraform apply' first.")
        sys.exit(1)

    instance_id = result.stdout.strip()
    print(f"Using instance: {instance_id}")

    wait_for_ssm(instance_id)
    setup_instance(instance_id)

    # Thread counts to test - higher counts stress the thread pool more
    # c8i.metal-48xl has 192 vCPUs (96 physical cores x 2 threads)
    thread_counts = [16, 32, 64, 96]

    # Build baseline (upstream master)
    build_verilator(
        instance_id,
        label="baseline",
        git_ref="upstream/master",
        install_dir="/home/ubuntu/benchmark/verilator-install-baseline"
    )

    # Build optimized (current branch)
    build_verilator(
        instance_id,
        label="optimized",
        git_ref=f"origin/{OPTIMIZED_BRANCH}",
        install_dir="/home/ubuntu/benchmark/verilator-install-optimized"
    )

    # Run benchmarks at each thread count
    results = {}
    for threads in thread_counts:
        print(f"\n{'='*60}")
        print(f"Testing with {threads} threads")
        print('='*60)

        results[f"baseline-t{threads}"] = run_rtlmeter(
            instance_id,
            label="baseline",
            install_dir="/home/ubuntu/benchmark/verilator-install-baseline",
            threads=threads
        )

        results[f"optimized-t{threads}"] = run_rtlmeter(
            instance_id,
            label="optimized",
            install_dir="/home/ubuntu/benchmark/verilator-install-optimized",
            threads=threads
        )

    # Generate comparison summary
    print("\n" + "="*60)
    print("=== COMPARISON SUMMARY ===")
    print("="*60)

    summary_lines = [
        "RTLMeter Benchmark Results: V3ThreadPool wait() Optimization",
        "=" * 60,
        f"Instance: c8i.metal-48xl (192 vCPUs, 384GB RAM)",
        f"Thread counts tested: {thread_counts}",
        "",
        "Optimization: Replace busy-wait with condition variable in V3ThreadPool::wait()",
        "  Before: while (m_pendingJobs > 0) std::this_thread::yield();",
        "  After:  m_completionCV.wait() with notify on job completion",
        "",
        "=" * 60,
        "Results by thread count:",
        ""
    ]

    for threads in thread_counts:
        summary_lines.append(f"--- {threads} threads ---")
        summary_lines.append(f"Baseline output length: {len(results.get(f'baseline-t{threads}', ''))} chars")
        summary_lines.append(f"Optimized output length: {len(results.get(f'optimized-t{threads}', ''))} chars")
        summary_lines.append("")

    summary_lines.extend([
        "=" * 60,
        "Full RTLMeter reports are in /home/ubuntu/benchmark/results_*.json",
        "These will be retrieved by run.py before instance termination.",
        "=" * 60
    ])

    summary = "\n".join(summary_lines)
    print(summary)

    # Save summary to file on EC2
    save_summary_cmd = f'''cat > /home/ubuntu/benchmark/comparison_summary.txt << 'SUMMARYEOF'
{summary}
SUMMARYEOF'''

    ssm_run(instance_id, [save_summary_cmd], timeout=60)
    print("\nSummary saved to /home/ubuntu/benchmark/comparison_summary.txt")


if __name__ == "__main__":
    main()
