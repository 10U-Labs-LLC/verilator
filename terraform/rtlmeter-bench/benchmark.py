#!/usr/bin/env python3
"""
RTLMeter benchmark runner using AWS SSM.
Compares baseline (upstream master) vs optimized (current branch) for V3ThreadPool wait().

AWS region is read from AWS_REGION environment variable (set by run.py).
"""

import os
import subprocess
import time
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import boto3

# AWS region from environment (set by run.py)
AWS_REGION = os.environ.get("AWS_REGION")
if not AWS_REGION:
    print("ERROR: AWS_REGION environment variable not set.")
    print("This script should be run via run.py which sets the region.")
    sys.exit(1)

# Repository URLs
UPSTREAM_REPO = "https://github.com/verilator/verilator.git"
FORK_REPO = "https://github.com/10U-Labs-LLC/verilator.git"

# Current branch with optimization
OPTIMIZED_BRANCH = "optimize-threadpool-wait-cv"

# Create boto3 clients with region from environment
ssm = boto3.client("ssm", region_name=AWS_REGION)
cloudwatch = boto3.client("cloudwatch", region_name=AWS_REGION)


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
        try:
            response = ssm.describe_instance_information(
                Filters=[{"Key": "InstanceIds", "Values": [instance_id]}]
            )
            instances = response.get("InstanceInformationList", [])
            if instances and instances[0].get("PingStatus") == "Online":
                print("\nSSM agent is online!")
                return
        except Exception:
            pass
        print(".", end="", flush=True)
        time.sleep(10)
    raise TimeoutError("SSM agent did not come online in time")


def get_metric(namespace: str, metric_name: str, instance_id: str,
               statistic: str = "Average", extra_dimensions: list | None = None) -> float | None:
    """Get a single CloudWatch metric value."""
    end_time = datetime.now(timezone.utc)
    start_time = end_time - timedelta(minutes=5)

    dimensions = [{"Name": "InstanceId", "Value": instance_id}]
    if extra_dimensions:
        dimensions.extend(extra_dimensions)

    try:
        response = cloudwatch.get_metric_statistics(
            Namespace=namespace,
            MetricName=metric_name,
            Dimensions=dimensions,
            StartTime=start_time,
            EndTime=end_time,
            Period=60,
            Statistics=[statistic]
        )
        datapoints = response.get("Datapoints", [])
        if datapoints:
            latest = max(datapoints, key=lambda x: x["Timestamp"])
            return latest.get(statistic)
    except Exception:
        pass
    return None


def get_instance_metrics(instance_id: str) -> dict:
    """Get current CloudWatch metrics for the instance."""
    metrics = {}

    # CPU utilization
    cpu = get_metric("AWS/EC2", "CPUUtilization", instance_id)
    metrics["cpu"] = f"{cpu:.1f}%" if cpu is not None else "..."

    # Network I/O
    for metric_name, key in [("NetworkIn", "net_in"), ("NetworkOut", "net_out")]:
        val = get_metric("AWS/EC2", metric_name, instance_id, statistic="Sum")
        if val is not None:
            if val > 1024 * 1024:
                metrics[key] = f"{val / 1024 / 1024:.1f}MB"
            else:
                metrics[key] = f"{val / 1024:.1f}KB"
        else:
            metrics[key] = "..."

    # Memory (from CloudWatch agent)
    mem = get_metric("RTLMeter", "mem_used_percent", instance_id)
    metrics["mem"] = f"{mem:.1f}%" if mem is not None else "..."

    # Disk (from CloudWatch agent)
    disk = get_metric("RTLMeter", "disk_used_percent", instance_id,
                      extra_dimensions=[
                          {"Name": "path", "Value": "/"},
                          {"Name": "fstype", "Value": "ext4"}
                      ])
    metrics["disk"] = f"{disk:.1f}%" if disk is not None else "..."

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

    response = ssm.send_command(
        InstanceIds=[instance_id],
        DocumentName="AWS-RunShellScript",
        Parameters={"commands": [command_str]},
        TimeoutSeconds=timeout,
        CloudWatchOutputConfig={"CloudWatchOutputEnabled": False}
    )

    command_id = response["Command"]["CommandId"]
    print(f"SSM command {command_id} sent, streaming output...")
    print("-" * 60)

    last_stdout_len = 0
    last_stderr_len = 0
    poll_count = 0

    while True:
        time.sleep(10)
        poll_count += 1

        try:
            invocation = ssm.get_command_invocation(
                CommandId=command_id,
                InstanceId=instance_id
            )
        except ssm.exceptions.InvocationDoesNotExist:
            continue
        except Exception:
            continue

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
        if status in ("Failed", "Cancelled", "TimedOut"):
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
        "git perl python3 python3-pip python3-venv make autoconf g++ flex bison ccache "
        "libgoogle-perftools-dev numactl perl-doc libfl2 libfl-dev zlib1g zlib1g-dev "
        "help2man",
        # Install AWS CLI via pip (not available via apt on Ubuntu 24.04)
        # --break-system-packages needed for Ubuntu 24.04 (PEP 668)
        "pip3 install --user --break-system-packages awscli",
        "export PATH=$HOME/.local/bin:$PATH",
        # Install CloudWatch agent for memory/disk metrics
        "wget -q https://s3.amazonaws.com/amazoncloudwatch-agent/ubuntu/amd64/latest/amazon-cloudwatch-agent.deb",
        "sudo dpkg -i amazon-cloudwatch-agent.deb",
        # Configure CloudWatch agent for memory and disk metrics (JSON on single line to avoid heredoc issues)
        '''echo '{"metrics":{"namespace":"RTLMeter","metrics_collected":{"mem":{"measurement":["mem_used_percent","mem_available"],"metrics_collection_interval":60},"disk":{"measurement":["disk_used_percent","disk_free"],"resources":["/"],"metrics_collection_interval":60},"diskio":{"measurement":["read_bytes","write_bytes","reads","writes"],"resources":["*"],"metrics_collection_interval":60}}}}' | sudo tee /opt/aws/amazon-cloudwatch-agent/etc/amazon-cloudwatch-agent.json''',
        "sudo /opt/aws/amazon-cloudwatch-agent/bin/amazon-cloudwatch-agent-ctl -a fetch-config -m ec2 -s -c file:/opt/aws/amazon-cloudwatch-agent/etc/amazon-cloudwatch-agent.json",
        "pip3 install --user --break-system-packages pyyaml tabulate scipy",
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


def check_disk_space(instance_id: str, warn_threshold: int = 80) -> None:
    """Check disk space on EC2 and warn if usage exceeds threshold."""
    try:
        response = ssm.send_command(
            InstanceIds=[instance_id],
            DocumentName="AWS-RunShellScript",
            Parameters={"commands": ["df -h / | tail -1 | awk '{print $5}' | tr -d '%'"]}
        )
        command_id = response["Command"]["CommandId"]

        # Wait for result
        for _ in range(10):
            time.sleep(2)
            try:
                invocation = ssm.get_command_invocation(
                    CommandId=command_id,
                    InstanceId=instance_id
                )
                if invocation["Status"] == "Success":
                    usage = int(invocation.get("StandardOutputContent", "0").strip())
                    if usage >= warn_threshold:
                        print(f"\n{'!'*60}")
                        print(f"  WARNING: Disk usage at {usage}% (threshold: {warn_threshold}%)")
                        print(f"{'!'*60}\n")
                    else:
                        print(f"[Disk: {usage}% used]")
                    return
                if invocation["Status"] in ("Failed", "Cancelled", "TimedOut"):
                    return
            except Exception:
                pass
    except Exception:
        pass  # Skip check if it fails


def run_rtlmeter(instance_id: str, label: str, install_dir: str,
                 threads: int) -> str:
    """Run RTLMeter benchmarks and return results."""
    print(f"\n=== Running RTLMeter ({label}, threads={threads}) ===")

    # Check disk space before each benchmark run
    check_disk_space(instance_id)

    # Use separate work directory per label/thread combo to enable rtlmeter compare
    work_dir = f"work-{label}-t{threads}"

    benchmark_commands = [
        "cd /home/ubuntu/benchmark/rtlmeter",
        # Clear work directory for fresh results
        f"rm -rf {work_dir}",
        f"export PATH={install_dir}/bin:$PATH",
        # Note: Don't set VERILATOR_ROOT - Verilator finds its files via the
        # compiled-in prefix when installed via 'make install'
        #
        # Key changes for proper V3ThreadPool measurement:
        # - Use 'cmark' case (longer-running benchmark, not short 'hello')
        # - Use --nExecute 3 for multiple samples (statistical confidence)
        # - Use --workRoot to specify work directory for rtlmeter compare
        # - Use --verilate-jobs N to control V3ThreadPool thread count
        #   (NOT --threads, which controls runtime VlThreadPool)
        # - Timeout 300s for longer cmark test
        f"./rtlmeter run --timeout 300 --verbose "
        f"--cases 'VeeR-EH1:default:cmark' "
        f"--workRoot '{work_dir}' "
        f"--nExecute 3 "
        f"--compileArgs '--verilate-jobs {threads}'",
        # Collate results (work_dir is positional argument)
        f"./rtlmeter collate '{work_dir}' --runName '{label}-t{threads}' "
        f"> /home/ubuntu/benchmark/results_{label}_t{threads}.json",
        # Report verilate step (work_dir is positional argument)
        f"./rtlmeter report --steps 'verilate' --metrics 'elapsed cpu' '{work_dir}'",
    ]

    output = ssm_run(instance_id, benchmark_commands, timeout=3600)
    return output


def compare_results(instance_id: str, threads: int) -> str:
    """Run RTLMeter compare for baseline vs optimized at given thread count.

    Returns the comparison output including:
    - Mean values with confidence intervals
    - Gain ratios (optimized/baseline, >1 means optimized is faster)
    - P-values for statistical significance
    """
    print(f"\n=== Comparing baseline vs optimized (threads={threads}) ===")

    compare_commands = [
        "cd /home/ubuntu/benchmark/rtlmeter",
        # Compare verilate step (V3ThreadPool optimization affects compile-time threading)
        # Output shows: metric, baseline mean, optimized mean, gain (B/A), p-value
        f"./rtlmeter compare "
        f"--steps 'verilate' "
        f"--metrics 'elapsed cpu' "
        f"work-baseline-t{threads} work-optimized-t{threads}",
    ]

    output = ssm_run(instance_id, compare_commands, timeout=300)
    return output


def main():
    tf_dir = Path(__file__).parent
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
    comparisons = {}

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

        # Run statistical comparison for this thread count
        comparisons[threads] = compare_results(instance_id, threads)

    # Generate comparison summary with statistical results
    print("\n" + "="*70)
    print("=== STATISTICAL COMPARISON RESULTS ===")
    print("="*70)

    summary_lines = [
        "RTLMeter Benchmark Results: V3ThreadPool wait() Optimization",
        "=" * 70,
        "Instance: c8i.metal-48xl (192 vCPUs, 384GB RAM)",
        f"Thread counts tested: {thread_counts}",
        "",
        "Optimization: Replace busy-wait with condition variable in V3ThreadPool::wait()",
        "  Before: while (m_pendingJobs > 0) std::this_thread::yield();",
        "  After:  m_completionCV.wait() with notify on job completion",
        "",
        "Benchmark: VeeR-EH1:default:cmark (3 samples per configuration)",
        "Focus: verilate step (compile-time threading where V3ThreadPool is used)",
        "",
        "=" * 70,
        "STATISTICAL COMPARISON (verilate step):",
        "",
        "Interpretation:",
        "  - Gain > 1.0 means optimized is FASTER than baseline",
        "  - P-value < 0.05 indicates statistically significant difference",
        "",
    ]

    for threads in thread_counts:
        summary_lines.append(f"--- {threads} threads ---")
        summary_lines.append(comparisons[threads])
        summary_lines.append("")

    summary_lines.extend([
        "=" * 70,
        "Full RTLMeter reports are in /home/ubuntu/benchmark/results_*.json",
        "Comparison data in /home/ubuntu/benchmark/rtlmeter/work-*/",
        "These will be retrieved by run.py before instance termination.",
        "=" * 70
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
