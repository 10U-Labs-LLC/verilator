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


def ssm_run(instance_id: str, commands: list[str], timeout: int = 3600) -> str:
    """Run commands on instance via SSM and return output."""
    command_str = " && ".join(commands)

    result = run_cmd([
        "aws", "ssm", "send-command",
        "--instance-ids", instance_id,
        "--document-name", "AWS-RunShellScript",
        "--parameters", json.dumps({"commands": [command_str]}),
        "--timeout-seconds", str(timeout),
        "--output", "json"
    ])

    cmd_data = json.loads(result.stdout)
    command_id = cmd_data["Command"]["CommandId"]
    print(f"SSM command {command_id} sent, waiting for completion...")

    while True:
        time.sleep(5)
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

        if status == "Success":
            print("Command completed successfully")
            return invocation.get("StandardOutputContent", "")
        elif status in ("Failed", "Cancelled", "TimedOut"):
            print(f"Command {status}")
            print(f"STDOUT: {invocation.get('StandardOutputContent', '')}")
            print(f"STDERR: {invocation.get('StandardErrorContent', '')}")
            raise RuntimeError(f"SSM command {status}")

        print(f"Status: {status}...")


def setup_instance(instance_id: str) -> None:
    """Install dependencies and clone repositories."""
    print("\n=== Setting up instance ===")

    setup_commands = [
        "sudo apt-get update",
        "sudo DEBIAN_FRONTEND=noninteractive apt-get upgrade -y",
        "sudo DEBIAN_FRONTEND=noninteractive apt-get install -y "
        "git perl python3 python3-pip make autoconf g++ flex bison ccache "
        "libgoogle-perftools-dev numactl perl-doc libfl2 libfl-dev zlib1g zlib1g-dev "
        "help2man",
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
    # c8i.metal-48xl has 96 vCPUs (48 physical cores)
    thread_counts = [8, 16, 32, 48]

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

    print("\n" + "="*60)
    print("=== Benchmark Complete ===")
    print("="*60)
    print(f"\nThread counts tested: {thread_counts}")
    print("Results saved to /home/ubuntu/benchmark/results_*.json")
    print("\nTo compare results:")
    for threads in thread_counts:
        print(f"  - baseline vs optimized at {threads} threads")
    print("\nRun 'terraform destroy' to clean up the instance.")


if __name__ == "__main__":
    main()
