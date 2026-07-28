"""Tests for exact record detection, CSV determinism, and the full
c <= 5x10^6 verification."""

from fractions import Fraction

import pytest

from enumerate_triples import Triple, sorted_triples
from pell_spine import spine_terms_up_to
from verify_records import (
    check_records,
    is_strictly_smaller,
    record_minima,
    write_record_csv,
    write_spine_csv,
)

FULL_CMAX = 5_000_000
FULL_COUNT = 795_763
FULL_RECORDS = [5, 29, 169, 985, 5741, 33461, 195025, 1136689]


def test_exact_comparison_is_not_floating_point():
    """Cross-multiplication must resolve differences that doubles cannot.

    1/2^60 and 1/(2^60 + 1) are distinct rationals whose float quotients are
    equal, so a float-based record test would miss the second as an
    improvement.
    """
    big = 2 ** 60
    assert 1 / big == 1 / (big + 1)  # doubles cannot separate these
    assert is_strictly_smaller(1, big + 1, 1, big)
    assert not is_strictly_smaller(1, big, 1, big + 1)


def test_comparison_agrees_with_fractions():
    cases = [(1, 5), (1, 29), (7, 13), (17, 145), (119, 169), (1, 1136689)]
    for d1, c1 in cases:
        for d2, c2 in cases:
            assert is_strictly_smaller(d1, c1, d2, c2) == (
                Fraction(d1, c1) < Fraction(d2, c2)
            )


def test_records_at_small_bounds():
    assert [r.c for r in record_minima(sorted_triples(1000))] == [5, 29, 169, 985]
    assert [r.c for r in record_minima(sorted_triples(100_000))] == FULL_RECORDS[:6]


def test_record_indices_are_sequential():
    records = record_minima(sorted_triples(100_000))
    assert [r.index for r in records] == list(range(1, len(records) + 1))


def test_records_are_exactly_spine_terms():
    bound = 1_000_000
    records = record_minima(sorted_triples(bound))
    assert [(r.a, r.b, r.c) for r in records] == [
        (t.a, t.b, t.c) for t in spine_terms_up_to(bound)
    ]


def test_record_properties():
    records = record_minima(sorted_triples(200_000))
    for r in records:
        assert r.b - r.a == 1
        assert r.delta_k == Fraction(1, r.c)
        assert r.c_times_delta_k == 1


def test_tie_handling_at_equal_hypotenuse():
    """A synthetic tie: two triples at the same c with the same minimal
    Delta_k are both records under Definition 4.1.  (No such tie occurs
    among real primitive triples with c <= 5x10^6.)"""
    fake = [
        Triple(c=100, d=10, a=45, b=55),
        Triple(c=100, d=10, a=40, b=50),
        Triple(c=100, d=20, a=30, b=50),
    ]
    records = record_minima(fake)
    assert [(r.a, r.d) for r in records] == [(40, 10), (45, 10)]


def test_no_improvement_at_equal_hypotenuse_is_not_a_record():
    """A later triple tying the running best does not start a new record."""
    fake = [Triple(c=5, d=1, a=3, b=4), Triple(c=10, d=2, a=6, b=8)]
    records = record_minima(fake)
    assert [r.c for r in records] == [5]


def test_csv_generation_is_deterministic(tmp_path):
    triples = sorted_triples(200_000)
    records = record_minima(triples)
    spine = spine_terms_up_to(200_000)

    first = (
        write_record_csv(records, tmp_path / "a" / "rec.csv").read_bytes(),
        write_spine_csv(spine, tmp_path / "a" / "spine.csv").read_bytes(),
    )
    second = (
        write_record_csv(records, tmp_path / "b" / "rec.csv").read_bytes(),
        write_spine_csv(spine, tmp_path / "b" / "spine.csv").read_bytes(),
    )
    assert first == second
    assert b"\n1,3,4,5,1,1,5,0.200000000000,1\n" in first[0]


@pytest.mark.slow
def test_full_range_count_and_records():
    """Full manuscript bound.  Marked slow; must be run before delivery."""
    triples = sorted_triples(FULL_CMAX)
    assert len(triples) == FULL_COUNT

    records = record_minima(triples)
    checks = check_records(records)
    assert checks["hypotenuses"] == FULL_RECORDS
    assert checks["count"] == 8
    assert checks["all_leg_difference_one"]
    assert checks["all_c_times_delta_k_one"]
    assert checks["strictly_decreasing"]

    # records coincide exactly with the spine in this range
    assert [(r.a, r.b, r.c) for r in records] == [
        (t.a, t.b, t.c) for t in spine_terms_up_to(FULL_CMAX)
    ]
