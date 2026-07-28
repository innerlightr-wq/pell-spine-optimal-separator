#!/usr/bin/env python3
"""One-command reproduction of the computational results.

    python reproduce.py                 # full run, c <= 5,000,000
    python reproduce.py --cmax 100000   # quick check on a smaller bound

The script enumerates primitive Pythagorean triples, computes the record
minima of Delta_k = (b - a)/c using exact integer arithmetic, writes the two
CSV files, regenerates both figures, and prints a verification summary.

Nothing is forced to match the manuscript: the summary reports what the code
actually found.  Expected values are printed alongside only when running at
the manuscript's bound of 5,000,000.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "src"))

from enumerate_triples import leg_differences, sorted_triples  # noqa: E402
from generate_figures import (  # noqa: E402
    figure_1_separation_cloud,
    figure_2_record_staircase,
    sample_stride,
)
from pell_spine import LIMITING_CONTRACTION, spine_terms_up_to, verify_spine  # noqa: E402
from verify_records import (  # noqa: E402
    check_records,
    record_minima,
    write_record_csv,
    write_spine_csv,
)

MANUSCRIPT_CMAX = 5_000_000
MANUSCRIPT_COUNT = 795_763
MANUSCRIPT_RECORD_HYPOTENUSES = [5, 29, 169, 985, 5741, 33461, 195025, 1136689]


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cmax", type=int, default=MANUSCRIPT_CMAX,
                        help="hypotenuse bound (default: 5000000)")
    parser.add_argument("--data-dir", type=Path, default=ROOT / "data")
    parser.add_argument("--figures-dir", type=Path, default=ROOT / "figures")
    parser.add_argument("--no-figures", action="store_true",
                        help="skip figure generation")
    args = parser.parse_args(argv)

    cmax = args.cmax
    print(f"Enumerating primitive Pythagorean triples with c <= {cmax} ...")
    triples = sorted_triples(cmax)
    records = record_minima(triples)
    checks = check_records(records)
    spine = spine_terms_up_to(cmax)
    spine_checks = verify_spine(spine)
    diffs = leg_differences(triples)

    if cmax != MANUSCRIPT_CMAX:
        print(f"Note: --cmax is {cmax}, not the manuscript bound {MANUSCRIPT_CMAX}. "
              "The output file data/record_minima_c5e6.csv keeps its canonical name "
              "but will contain the smaller table.")

    record_csv = write_record_csv(records, args.data_dir / "record_minima_c5e6.csv")
    spine_csv = write_spine_csv(spine, args.data_dir / "pell_spine_terms.csv")

    if not args.no_figures:
        fig1 = figure_1_separation_cloud(
            triples, records, args.figures_dir / "figure_1_separation_cloud.png")
        fig2 = figure_2_record_staircase(
            records, args.figures_dir / "figure_2_record_staircase.png")
    else:
        fig1 = fig2 = None

    print()
    print("=" * 62)
    print("VERIFICATION SUMMARY")
    print("=" * 62)
    print(f"Primitive triples with c <= {cmax}: {len(triples)}")
    print(f"Record minima found: {checks['count']}")
    print(f"All records have b-a = 1: {checks['all_leg_difference_one']}")
    print(f"All records satisfy c*Delta_k = 1: {checks['all_c_times_delta_k_one']}")
    print(f"Record sequence strictly decreasing in Delta_k: {checks['strictly_decreasing']}")
    print()
    print("Record hypotenuses: " + ", ".join(str(c) for c in checks["hypotenuses"]))
    print()
    print(f"{'idx':>3} {'a':>9} {'b':>9} {'c':>9} {'b-a':>4} {'Delta_k':>16} {'c*Delta_k':>10}")
    for r in records:
        print(f"{r.index:>3} {r.a:>9} {r.b:>9} {r.c:>9} {r.d:>4} "
              f"{float(r.delta_k):>16.12f} {str(r.c_times_delta_k):>10}")
    print()
    print(f"Pell-spine terms with c <= {cmax}: {len(spine)}")
    for name, ok in spine_checks.items():
        print(f"  spine {name}: {ok}")
    print(f"  limiting contraction q = 3 - 2*sqrt(2) = {LIMITING_CONTRACTION:.10f}")
    print()
    print(f"Records coincide with spine terms: "
          f"{[r.c for r in records] == [t.c for t in spine]}")
    print(f"Observed leg differences (first 16): {diffs[:16]}")
    print(f"All observed leg differences are 1 or >= 7: "
          f"{all(d == 1 or d >= 7 for d in diffs)}")
    print()
    print(f"Figure 1 sample stride: every {sample_stride(len(triples))} triples "
          f"(records overlaid in full)")
    print(f"Wrote {record_csv.relative_to(ROOT)}")
    print(f"Wrote {spine_csv.relative_to(ROOT)}")
    if fig1 is not None:
        print(f"Wrote {fig1.relative_to(ROOT)}")
        print(f"Wrote {fig2.relative_to(ROOT)}")

    if cmax == MANUSCRIPT_CMAX:
        print()
        print("Comparison with the manuscript (Section 5, Table 2):")
        print(f"  count matches 795763: {len(triples) == MANUSCRIPT_COUNT}")
        print(f"  record hypotenuses match Table 2: "
              f"{checks['hypotenuses'] == MANUSCRIPT_RECORD_HYPOTENUSES}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
