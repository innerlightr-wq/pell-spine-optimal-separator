"""Exact record minima of Delta_k = (b - a)/c, and deterministic CSV output.

Exact arithmetic
----------------
Record detection never compares floating-point quotients.  Two separations
d1/c1 and d2/c2 are compared by integer cross-multiplication,

    d1/c1 < d2/c2   <==>   d1 * c2 < d2 * c1        (c1, c2 > 0),

which is exact for arbitrarily large integers in Python.  Floats appear only
in the human-readable decimal column of the CSV output.

Ordering and ties
-----------------
Definition 4.1 of the manuscript requires a record T to satisfy

    Delta_k(T) <  Delta_k(T')  for every T' with c(T') < c(T),  and
    Delta_k(T) <= Delta_k(T')  for every T' with c(T') = c(T).

We therefore group triples by hypotenuse before updating the running record,
so behaviour at equal c is explicit rather than an artifact of sort order.
Within a group we take the minimal Delta_k (equivalently the minimal leg
difference, since c is fixed) and compare it to the running best drawn from
strictly smaller hypotenuses.  If several triples in a group attain that same
minimal value, all of them satisfy Definition 4.1 and all are reported.

Empirically no such tie occurs anywhere in c <= 5x10^6: no two primitive
triples with equal hypotenuse share a leg difference in that range.  The tie
branch is implemented for correctness, not because it is exercised.
"""

from __future__ import annotations

import csv
from fractions import Fraction
from itertools import groupby
from pathlib import Path
from typing import Iterable, List, NamedTuple, Sequence

from enumerate_triples import Triple
from pell_spine import SpineTerm


class Record(NamedTuple):
    """A record minimum of Delta_k, with its 1-based position in the sequence."""

    index: int
    a: int
    b: int
    c: int
    d: int

    @property
    def delta_k(self) -> Fraction:
        """Exact rational value of Delta_k = (b - a)/c, in lowest terms."""
        return Fraction(self.d, self.c)

    @property
    def c_times_delta_k(self) -> Fraction:
        """Exact value of c * Delta_k; equals 1 for every spine record."""
        return Fraction(self.c) * self.delta_k


def is_strictly_smaller(d1: int, c1: int, d2: int, c2: int) -> bool:
    """Exact test d1/c1 < d2/c2 for positive integers, by cross-multiplication."""
    return d1 * c2 < d2 * c1


def record_minima(triples: Sequence[Triple]) -> List[Record]:
    """Successive record minima of Delta_k over triples ordered by hypotenuse.

    ``triples`` must be sorted by increasing hypotenuse (see
    ``enumerate_triples.sorted_triples``).
    """
    records: List[Record] = []
    best_d: int | None = None
    best_c: int | None = None
    index = 0

    for c, group_iter in groupby(triples, key=lambda t: t.c):
        group = list(group_iter)
        min_d = min(t.d for t in group)
        if best_d is None or is_strictly_smaller(min_d, c, best_d, best_c):
            best_d, best_c = min_d, c
            # All triples in this group attaining min_d are records.
            for t in sorted((t for t in group if t.d == min_d), key=lambda t: t.a):
                index += 1
                records.append(Record(index=index, a=t.a, b=t.b, c=t.c, d=t.d))

    return records


def _format_fraction(value: Fraction) -> str:
    """Exact string for a Fraction: an integer when possible, else 'p/q'."""
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def write_record_csv(records: Iterable[Record], path: Path) -> Path:
    """Write the record-minima table.  Deterministic: no timestamps, no RNG."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="\n", encoding="utf-8") as fh:
        writer = csv.writer(fh, lineterminator="\n")
        writer.writerow(
            [
                "record_index",
                "a",
                "b",
                "c",
                "leg_difference",
                "delta_k_numerator",
                "delta_k_denominator",
                "delta_k_decimal",
                "c_times_delta_k",
            ]
        )
        for r in records:
            dk = r.delta_k
            writer.writerow(
                [
                    r.index,
                    r.a,
                    r.b,
                    r.c,
                    r.d,
                    dk.numerator,
                    dk.denominator,
                    f"{float(dk):.12f}",
                    _format_fraction(r.c_times_delta_k),
                ]
            )
    return path


def write_spine_csv(terms: Iterable[SpineTerm], path: Path) -> Path:
    """Write the Pell-spine table.  Deterministic: no timestamps, no RNG."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="\n", encoding="utf-8") as fh:
        writer = csv.writer(fh, lineterminator="\n")
        writer.writerow(
            [
                "index",
                "a",
                "b",
                "c",
                "u",
                "leg_difference",
                "delta_k_numerator",
                "delta_k_denominator",
            ]
        )
        for t in terms:
            dk = Fraction(t.b - t.a, t.c)
            writer.writerow(
                [t.index, t.a, t.b, t.c, t.u, t.b - t.a, dk.numerator, dk.denominator]
            )
    return path


def check_records(records: Sequence[Record]) -> dict:
    """Exact checks applied to the computed record sequence.

    Every value returned is computed from the records actually found; nothing
    is forced to agree with the manuscript.
    """
    return {
        "count": len(records),
        "all_leg_difference_one": all(r.d == 1 for r in records),
        "all_c_times_delta_k_one": all(r.c_times_delta_k == 1 for r in records),
        "strictly_decreasing": all(
            is_strictly_smaller(records[i + 1].d, records[i + 1].c, records[i].d, records[i].c)
            for i in range(len(records) - 1)
        ),
        "hypotenuses": [r.c for r in records],
    }
