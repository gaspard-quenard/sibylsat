import argparse
import logging
import os
import re
import shlex
import subprocess
import time
from pathlib import Path

from confirm_ok import PATH_BENCHMARKS, TIMEOUT_S


CLAUSE_PATTERN = re.compile(r"Total amount of clauses encoded:\s*(\d+)")
PROBLEM_PROCESSING_FILES = (
    "problem.parsed",
    "problem.parsed.log",
    "problem.sas",
    "problem.solution",
    "problem.stderr.statistics",
    "problem.stdout.statistics",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare total clause counts between ./sibylsat_main and the current ./sibylsat."
    )
    parser.add_argument(
        "--main-binary",
        default="./sibylsat_main",
        help="Path to the reference binary. Default: ./sibylsat_main",
    )
    parser.add_argument(
        "--current-binary",
        default="./sibylsat",
        help="Path to the current binary. Default: ./sibylsat",
    )
    parser.add_argument(
        "--benchmark-filter",
        default="",
        help="Only run benchmarks whose name contains this substring.",
    )
    return parser.parse_args()


def select_benchmarks(benchmark_filter: str):
    benchmark_filter = benchmark_filter.lower()
    selected_benchmarks = []
    for path_benchmark, max_instances_to_check in PATH_BENCHMARKS:
        benchmark_name = Path(path_benchmark).name
        if benchmark_filter and benchmark_filter not in benchmark_name.lower():
            continue
        selected_benchmarks.append((path_benchmark, max_instances_to_check))
    return selected_benchmarks


def resolve_instances(repo_root: Path, selected_benchmarks):
    total_benchmarks = len(selected_benchmarks)
    for benchmark_index, (path_benchmark, max_instances_to_check) in enumerate(selected_benchmarks, start=1):
        benchmark_dir = repo_root / path_benchmark
        benchmark_name = benchmark_dir.name

        all_files = sorted(os.listdir(benchmark_dir))
        files_in_benchmark = [f for f in all_files if f.endswith("hddl") or f.endswith("pddl")]
        domain_files = [f for f in files_in_benchmark if "domain" in f.lower() and f.endswith("hddl")]
        problem_files = [f for f in files_in_benchmark if "domain" not in f.lower()]
        num_instances_to_check = min(max_instances_to_check, len(problem_files))

        for problem_index in range(num_instances_to_check):
            problem_file = problem_files[problem_index]
            domain_file_name = "domain.hddl"
            if domain_file_name not in domain_files:
                domain_file_name = problem_file.split(".")[0] + "-domain.hddl"
                if domain_file_name not in domain_files:
                    raise FileNotFoundError(
                        f"Domain file not found for benchmark {benchmark_name}, problem {problem_file}"
                    )

            yield {
                "benchmark_index": benchmark_index,
                "benchmark_name": benchmark_name,
                "benchmark_count": total_benchmarks,
                "problem_name": problem_file,
                "domain_path": benchmark_dir / domain_file_name,
                "problem_path": benchmark_dir / problem_file,
            }


def clean_problem_processing(repo_root: Path) -> None:
    problem_processing_dir = repo_root / "ProblemProcessing"
    for filename in PROBLEM_PROCESSING_FILES:
        filepath = problem_processing_dir / filename
        if filepath.exists():
            filepath.unlink()


def extract_clause_count(output: str) -> int:
    match = CLAUSE_PATTERN.search(output)
    if match is None:
        raise ValueError("Could not find 'Total amount of clauses encoded' in planner output")
    return int(match.group(1))


def build_command(binary: Path, domain_path: Path, problem_path: Path) -> str:
    return (
        f"{shlex.quote(str(binary))} "
        f"{shlex.quote(str(domain_path))} "
        f"{shlex.quote(str(problem_path))} "
        "-optimal=0 -reusePreviousCores=0 -sibylsat=0"
    )


def run_planner(command: str, repo_root: Path) -> tuple[int, str]:
    clean_problem_processing(repo_root)
    result = subprocess.run(
        shlex.split(command),
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        universal_newlines=True,
        timeout=TIMEOUT_S,
        cwd=repo_root,
    )
    return result.returncode, result.stdout


def ensure_binary_exists(binary_path: Path, label: str) -> None:
    if not binary_path.is_file():
        raise FileNotFoundError(f"{label} binary not found: {binary_path}")


if __name__ == "__main__":
    args = parse_args()

    logging.basicConfig(format="%(asctime)s %(levelname)s:%(message)s", level=logging.INFO)

    repo_root = Path(__file__).resolve().parent.parent
    main_binary = (repo_root / args.main_binary).resolve() if not Path(args.main_binary).is_absolute() else Path(args.main_binary)
    current_binary = (repo_root / args.current_binary).resolve() if not Path(args.current_binary).is_absolute() else Path(args.current_binary)

    ensure_binary_exists(main_binary, "Reference")
    ensure_binary_exists(current_binary, "Current")

    start_time = time.time()
    num_instances_checked = 0

    selected_benchmarks = select_benchmarks(args.benchmark_filter)
    if not selected_benchmarks:
        logging.error("No benchmark matched the requested filter.")
        raise SystemExit(1)

    logging.info("Using the same benchmark limits as scripts/confirm_ok.py")

    try:
        instances = list(resolve_instances(repo_root, selected_benchmarks))
    except FileNotFoundError as exc:
        logging.error(str(exc))
        raise SystemExit(1)

    current_benchmark = None
    benchmark_start_time = 0.0
    for instance in instances:
        benchmark_name = instance["benchmark_name"]
        if benchmark_name != current_benchmark:
            if current_benchmark is not None:
                benchmark_elapsed = round(time.time() - benchmark_start_time, 2)
                logging.info(
                    "Benchmark %s is OK (done in %s s)",
                    current_benchmark,
                    benchmark_elapsed,
                )
            current_benchmark = benchmark_name
            benchmark_start_time = time.time()
            logging.info(
                "Compare benchmark %s (%d/%d)",
                benchmark_name,
                instance["benchmark_index"],
                instance["benchmark_count"],
            )

        main_command = build_command(
            main_binary,
            instance["domain_path"],
            instance["problem_path"],
        )
        print(f"MAIN    {main_command}", flush=True)
        return_code_main, output_main = run_planner(main_command, repo_root)
        if return_code_main != 0:
            logging.error(
                "Reference binary failed on %s/%s",
                benchmark_name,
                instance["problem_name"],
            )
            raise SystemExit(1)

        current_command = build_command(
            current_binary,
            instance["domain_path"],
            instance["problem_path"],
        )
        print(f"CURRENT {current_command}", flush=True)
        return_code_current, output_current = run_planner(current_command, repo_root)
        if return_code_current != 0:
            logging.error(
                "Current binary failed on %s/%s",
                benchmark_name,
                instance["problem_name"],
            )
            raise SystemExit(1)

        try:
            main_clauses = extract_clause_count(output_main)
            current_clauses = extract_clause_count(output_current)
        except ValueError as exc:
            logging.error(
                "%s on %s/%s",
                str(exc),
                benchmark_name,
                instance["problem_name"],
            )
            raise SystemExit(1)

        if main_clauses != current_clauses:
            logging.error(
                "Clause mismatch on %s/%s: main=%d current=%d",
                benchmark_name,
                instance["problem_name"],
                main_clauses,
                current_clauses,
            )
            raise SystemExit(1)

        num_instances_checked += 1

    if current_benchmark is not None:
        benchmark_elapsed = round(time.time() - benchmark_start_time, 2)
        logging.info(
            "Benchmark %s is OK (done in %s s)",
            current_benchmark,
            benchmark_elapsed,
        )

    elapsed = round(time.time() - start_time, 2)
    logging.info(
        "All clause counts match (%d problems checked) (done in %s s)",
        num_instances_checked,
        elapsed,
    )
