#!/usr/bin/env python3

import argparse
import json
from dataclasses import dataclass
from pathlib import Path


@dataclass
class Measurements:
    by_metric: dict[str, float]


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
    return f"build/module/{module}//instructions"


def module_from_metric(metric: str) -> str | None:
    prefix = "build/module/"
    suffix = "//instructions"
    if not metric.startswith(prefix) or not metric.endswith(suffix):
        return None
    return metric[len(prefix) : -len(suffix)]


def fmt_int(value: float) -> str:
    return f"{value:,.0f}"


def fmt_pct(value: float) -> str:
    return f"{value:+.2f}%"


def print_summary(current: Measurements, baseline: Measurements | None) -> None:
    current_total = current.by_metric.get("build//instructions")
    baseline_total = baseline.by_metric.get("build//instructions") if baseline else None

    print("# Build Benchmark Report")
    print()
    if current_total is None:
        print("No whole-build instruction count found.")
    elif baseline_total is None:
        print(f"- Build instructions: `{fmt_int(current_total)}`")
    else:
        delta = current_total - baseline_total
        pct = (delta / baseline_total * 100) if baseline_total else 0
        print(f"- Build instructions: `{fmt_int(current_total)}` ({fmt_int(delta)} / {fmt_pct(pct)})")
    print()


def print_modules(current: Measurements, baseline: Measurements | None, limit: int) -> None:
    modules = sorted(
        module
        for metric in current.by_metric
        if (module := module_from_metric(metric)) is not None
    )

    if baseline is None:
        rows = sorted(
            ((current.by_metric[module_metric(module)], module) for module in modules),
            reverse=True,
        )[:limit]
        print(f"## Slowest Modules By Instructions")
        print()
        print("| Instructions | Module |")
        print("| ---: | --- |")
        for instructions, module in rows:
            print(f"| {fmt_int(instructions)} | `{module}` |")
        return

    rows = []
    for module in modules:
        metric = module_metric(module)
        current_value = current.by_metric[metric]
        baseline_value = baseline.by_metric.get(metric)
        if baseline_value is None:
            rows.append((current_value, 100.0, current_value, baseline_value, module))
            continue
        delta = current_value - baseline_value
        pct = (delta / baseline_value * 100) if baseline_value else 0
        rows.append((delta, pct, current_value, baseline_value, module))

    rows.sort(key=lambda row: row[0], reverse=True)
    print(f"## Largest Module Instruction Regressions")
    print()
    print("| Delta | Delta % | Current | Baseline | Module |")
    print("| ---: | ---: | ---: | ---: | --- |")
    for delta, pct, current_value, baseline_value, module in rows[:limit]:
        baseline_text = "-" if baseline_value is None else fmt_int(baseline_value)
        print(
            f"| {fmt_int(delta)} | {fmt_pct(pct)} | {fmt_int(current_value)} | "
            f"{baseline_text} | `{module}` |"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="Render build benchmark measurements.")
    parser.add_argument("current", type=Path)
    parser.add_argument("baseline", type=Path, nargs="?")
    parser.add_argument("--limit", type=int, default=20)
    args = parser.parse_args()

    current = load(args.current)
    baseline = load(args.baseline) if args.baseline else None
    print_summary(current, baseline)
    print_modules(current, baseline, args.limit)


if __name__ == "__main__":
    main()
