#!/usr/bin/env python3

import argparse
import json
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path


@dataclass
class Measurements:
    by_metric: dict[str, float]


@dataclass
class ModuleRow:
    module: str
    current: float
    baseline: float | None

    @property
    def delta(self) -> float | None:
        if self.baseline is None:
            return None
        return self.current - self.baseline

    @property
    def delta_pct(self) -> float | None:
        if self.baseline in (None, 0):
            return None
        return (self.current - self.baseline) / self.baseline * 100


def load(path: Path) -> Measurements:
    by_metric: dict[str, float] = {}
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            if not line.strip():
                continue
            record = json.loads(line)
            metric = record["metric"]
            value = float(record["value"])
            by_metric[metric] = by_metric.get(metric, 0) + value
    return Measurements(by_metric=by_metric)


def module_metric(module: str) -> str:
    return f"build/module/{module}//heartbeats"


def module_from_metric(metric: str) -> str | None:
    prefix = "build/module/"
    suffix = "//heartbeats"
    if not metric.startswith(prefix) or not metric.endswith(suffix):
        return None
    return metric[len(prefix) : -len(suffix)]


def build_heartbeats(measurements: Measurements) -> float | None:
    total = sum(
        value
        for metric, value in measurements.by_metric.items()
        if module_from_metric(metric) is not None
    )
    if total == 0:
        return None
    return total


def fmt_int(value: float) -> str:
    return f"{value:,.0f}"


def fmt_heartbeats_k(value: float) -> str:
    return f"{value / 1_000:,.0f}"


def fmt_signed_int(value: float | None) -> str:
    if value is None:
        return "new"
    return f"{value:+,.0f}"


def fmt_signed_heartbeats_k(value: float | None) -> str:
    if value is None:
        return "new"
    rounded = round(value / 1_000)
    if rounded == 0:
        return "0"
    return f"{rounded:+,}"


def fmt_pct(value: float | None) -> str:
    if value is None:
        return "-"
    return f"{value:+.2f}%"


def fmt_seconds(value: float) -> str:
    return f"{value:,.2f}s"


def fmt_bytes(value: float) -> str:
    mib = value / 1024 / 1024
    return f"{mib:,.1f} MiB"


def fmt_metric(metric: str, value: float) -> str:
    if metric.endswith("//heartbeats"):
        return fmt_heartbeats_k(value)
    if metric.endswith("//wall-clock"):
        return fmt_seconds(value)
    if metric.endswith("//maxrss"):
        return fmt_bytes(value)
    return fmt_int(value)


def fmt_delta(metric: str, value: float | None) -> str:
    if value is None:
        return "new"
    if metric.endswith("//heartbeats"):
        return fmt_signed_heartbeats_k(value)
    if metric.endswith("//wall-clock"):
        return f"{value:+,.2f}s"
    if metric.endswith("//maxrss"):
        sign = "+" if value >= 0 else "-"
        return f"{sign}{fmt_bytes(abs(value))}"
    return fmt_signed_int(value)


def print_summary(current: Measurements, baseline: Measurements | None) -> None:
    metrics = [
        ("Build heartbeats (k)", "build//heartbeats"),
        ("Wall time", "build//wall-clock"),
        ("Max RSS", "build//maxrss"),
    ]

    print("# Build Benchmark Report")
    print()
    print("| Metric | Current | Baseline | Delta | Delta % |")
    print("| --- | ---: | ---: | ---: | ---: |")
    for label, metric in metrics:
        if metric == "build//heartbeats":
            current_value = build_heartbeats(current)
            baseline_value = build_heartbeats(baseline) if baseline else None
        else:
            current_value = current.by_metric.get(metric)
            baseline_value = baseline.by_metric.get(metric) if baseline else None
        if current_value is None:
            continue
        delta = None if baseline_value is None else current_value - baseline_value
        pct = None if baseline_value in (None, 0) else delta / baseline_value * 100
        baseline_text = "-" if baseline_value is None else fmt_metric(metric, baseline_value)
        delta_text = "-" if baseline_value is None else fmt_delta(metric, delta)
        print(
            f"| {label} | {fmt_metric(metric, current_value)} | {baseline_text} | "
            f"{delta_text} | {fmt_pct(pct)} |"
        )
    print()


def get_module_rows(
    current: Measurements,
    baseline: Measurements | None,
) -> list[ModuleRow]:
    modules = sorted(
        module
        for metric in current.by_metric
        if (module := module_from_metric(metric)) is not None
    )
    rows = []
    for module in modules:
        metric = module_metric(module)
        rows.append(
            ModuleRow(
                module=module,
                current=current.by_metric[metric],
                baseline=baseline.by_metric.get(metric) if baseline else None,
            )
        )
    return rows


def print_module_table(
    title: str,
    rows: Iterable[ModuleRow],
    limit: int | None,
    empty_message: str,
) -> None:
    rows = list(rows)
    if limit is not None:
        rows = rows[:limit]
    print(f"## {title}")
    print()
    if not rows:
        print(empty_message)
        print()
        return

    print("| Delta (k) | Delta % | Current (k) | Baseline (k) | Module |")
    print("| ---: | ---: | ---: | ---: | --- |")
    for row in rows:
        metric = module_metric(row.module)
        baseline_text = "-" if row.baseline is None else fmt_metric(metric, row.baseline)
        print(
            f"| {fmt_delta(metric, row.delta)} | {fmt_pct(row.delta_pct)} | "
            f"{fmt_metric(metric, row.current)} | {baseline_text} | `{row.module}` |"
        )
    print()


def print_modules(current: Measurements, baseline: Measurements | None, limit: int) -> None:
    rows = get_module_rows(current, baseline)

    if baseline is None:
        print_module_table(
            "Longest-Running Modules By Heartbeats",
            sorted(rows, key=lambda row: row.current, reverse=True),
            limit,
            "No module heartbeat measurements found.",
        )
        return

    def is_regression(row: ModuleRow) -> bool:
        return row.delta is None or row.delta > 0

    def is_improvement(row: ModuleRow) -> bool:
        return row.delta is not None and row.delta < 0

    print_module_table(
        "Top Module Heartbeat Regressions",
        sorted(filter(is_regression, rows), key=regression_key, reverse=True),
        limit,
        "No module heartbeat regressions found.",
    )
    print_module_table(
        "Top Module Heartbeat Improvements",
        sorted(filter(is_improvement, rows), key=lambda row: row.delta or 0),
        limit,
        "No module heartbeat improvements found.",
    )
    print_module_table(
        "Longest-Running Modules By Heartbeats",
        sorted(rows, key=lambda row: row.current, reverse=True),
        limit,
        "No module heartbeat measurements found.",
    )


def print_all_modules(current: Measurements, baseline: Measurements | None) -> None:
    rows = get_module_rows(current, baseline)
    print("# Build Benchmark Module Table")
    print()
    print_module_table(
        "All Modules By Heartbeats",
        sorted(rows, key=lambda row: row.module),
        None,
        "No module heartbeat measurements found.",
    )


def regression_key(row: ModuleRow) -> float:
    if row.delta is None:
        return row.current
    return row.delta


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return parsed


def main() -> None:
    parser = argparse.ArgumentParser(description="Render build benchmark measurements.")
    parser.add_argument("current", type=Path)
    parser.add_argument("baseline", type=Path, nargs="?")
    parser.add_argument("--limit", type=positive_int, default=10)
    parser.add_argument(
        "--all-modules",
        action="store_true",
        help="render one alphabetically sorted table with every measured module",
    )
    args = parser.parse_args()

    current = load(args.current)
    baseline = load(args.baseline) if args.baseline else None
    if args.all_modules:
        print_all_modules(current, baseline)
    else:
        print_summary(current, baseline)
        print_modules(current, baseline, args.limit)


if __name__ == "__main__":
    main()
