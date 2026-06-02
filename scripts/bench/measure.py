#!/usr/bin/env python3

import argparse
import json
import resource
import subprocess
import sys
import time
from argparse import Namespace
from dataclasses import dataclass
from pathlib import Path


@dataclass
class RusageMetric:
    name: str
    factor: float = 1
    unit: str | None = None


@dataclass
class Result:
    category: str
    value: float
    unit: str | None

    def fmt(self, topic: str) -> str:
        data: dict[str, str | float] = {"metric": f"{topic}//{self.category}", "value": self.value}
        if self.unit is not None:
            data["unit"] = self.unit
        return json.dumps(data)


RUSAGE_METRICS = {
    "maxrss": RusageMetric("ru_maxrss", factor=1000, unit="B"),
}

WALL_CLOCK_METRICS = {"wall-clock"}

ALL_METRICS = {*RUSAGE_METRICS, *WALL_CLOCK_METRICS}
DEFAULT_METRICS = {"maxrss", "wall-clock"}


@dataclass
class MeasureResult:
    stdout: str
    stderr: str


def resolve_metrics(metrics: set[str]) -> tuple[set[str], set[str]]:
    rusage = set()
    wall_clock = set()
    unknown = set()

    for metric in metrics:
        if metric in RUSAGE_METRICS:
            rusage.add(metric)
        elif metric in WALL_CLOCK_METRICS:
            wall_clock.add(metric)
        else:
            unknown.add(metric)

    if unknown:
        raise SystemExit(f"unknown metrics: {', '.join(sorted(unknown))}")

    return rusage, wall_clock


def measure_subprocess(cmd: list[str], capture: bool) -> MeasureResult:
    result = subprocess.run(cmd, capture_output=capture, encoding="utf-8")
    if result.returncode != 0:
        if capture:
            print(result.stdout, end="", file=sys.stdout)
            print(result.stderr, end="", file=sys.stderr)
        raise SystemExit(result.returncode)

    return MeasureResult(
        stdout=result.stdout or "",
        stderr=result.stderr or "",
    )


def get_rusage_result(rusage: resource.struct_rusage, metric: str) -> Result:
    info = RUSAGE_METRICS[metric]
    value = getattr(rusage, info.name) * info.factor
    return Result(category=metric, value=value, unit=info.unit)


def main(
    cmd: list[str],
    output: Path,
    topics: list[str],
    metrics: set[str],
    append: bool = True,
    capture: bool = False,
) -> tuple[str, str]:
    rusage_metrics, wall_clock_metrics = resolve_metrics(metrics)

    start = time.monotonic()
    measured = measure_subprocess(cmd, capture=capture)
    elapsed = time.monotonic() - start
    rusage = resource.getrusage(resource.RUSAGE_CHILDREN)

    results = [get_rusage_result(rusage, metric) for metric in rusage_metrics]
    results.extend(Result(category=metric, value=elapsed, unit="s") for metric in wall_clock_metrics)

    with output.open("a" if append else "w", encoding="utf-8") as handle:
        for result in results:
            for topic in topics:
                handle.write(result.fmt(topic) + "\n")

    return measured.stdout, measured.stderr


@dataclass
class Args(Namespace):
    topic: list[str]
    metric: list[str]
    default_metrics: bool
    output: Path
    append: bool
    cmd: str
    args: list[str]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Measure command resource usage.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--topic", "-t", action="append", default=[], help="metric topic prefix")
    parser.add_argument(
        "--metric",
        "-m",
        action="append",
        default=[],
        help=f"metric to record; available metrics: {', '.join(sorted(ALL_METRICS))}",
    )
    parser.add_argument(
        "--default-metrics",
        "-d",
        action="store_true",
        help=f"record the default metric set: {', '.join(sorted(DEFAULT_METRICS))}",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=Path,
        default=Path("measurements.jsonl"),
        help="JSON Lines output file",
    )
    parser.add_argument("--append", "-a", action="store_true", help="append to output")
    parser.add_argument("cmd", help="command to measure")
    parser.add_argument("args", nargs="*", default=[], help="arguments for command")
    args = parser.parse_args(namespace=Args)

    metrics = set(args.metric)
    if args.default_metrics:
        metrics |= DEFAULT_METRICS

    if not args.topic:
        raise SystemExit("at least one --topic is required")

    main(
        cmd=[args.cmd] + args.args,
        output=args.output,
        topics=args.topic,
        metrics=metrics,
        append=args.append,
    )
