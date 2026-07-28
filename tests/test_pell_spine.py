"""Tests for the Pell spine: recurrences, Pell identity, and consistency
with the general enumeration."""

from math import gcd, sqrt

from enumerate_triples import primitive_triples
from pell_spine import (
    LIMITING_CONTRACTION,
    LIMITING_GROWTH,
    hypotenuse_recurrence,
    spine_terms,
    spine_terms_up_to,
    u_recurrence,
    verify_spine,
)

EXPECTED_HYPOTENUSES = [5, 29, 169, 985, 5741, 33461, 195025, 1136689]
EXPECTED_U = [7, 41, 239, 1393, 8119, 47321, 275807, 1607521]
# Table 3 of the manuscript: (s, n, a, b, c)
TABLE_3 = [
    (1, 1, 3, 4, 5),
    (3, 2, 20, 21, 29),
    (7, 5, 119, 120, 169),
    (17, 12, 696, 697, 985),
    (41, 29, 4059, 4060, 5741),
    (99, 70, 23660, 23661, 33461),
    (239, 169, 137903, 137904, 195025),
    (577, 408, 803760, 803761, 1136689),
]


def test_hypotenuse_sequence():
    assert [t.c for t in spine_terms(8)] == EXPECTED_HYPOTENUSES


def test_table_3_entries():
    for term, (s, n, a, b, c) in zip(spine_terms(8), TABLE_3):
        assert (term.s, term.n, term.a, term.b, term.c) == (s, n, a, b, c)


def test_u_values():
    assert [t.u for t in spine_terms(8)] == EXPECTED_U


def test_recurrence_matches_construction():
    """c_{j+1} = 6c_j - c_{j-1} (c_0 = 1) reproduces the constructed spine."""
    assert hypotenuse_recurrence(12) == [t.c for t in spine_terms(12)]
    assert u_recurrence(12) == [t.u for t in spine_terms(12)]


def test_recurrence_is_exact_integer_arithmetic():
    cs = hypotenuse_recurrence(30)
    assert all(isinstance(c, int) for c in cs)
    seq = [1] + cs
    assert all(seq[j + 1] == 6 * seq[j] - seq[j - 1] for j in range(1, len(seq) - 1))


def test_pell_identity():
    """u^2 - 2c^2 = -1 for every spine term."""
    for t in spine_terms(25):
        assert t.u * t.u - 2 * t.c * t.c == -1


def test_structural_checks_all_true():
    checks = verify_spine(spine_terms(20))
    assert all(checks.values()), checks


def test_leg_difference_is_one_and_triples_are_primitive():
    for t in spine_terms(20):
        assert t.b - t.a == 1
        assert t.a * t.a + t.b * t.b == t.c * t.c
        assert gcd(t.a, t.b) == 1
        assert t.u == t.a + t.b


def test_spine_is_subset_of_enumeration():
    bound = 1_000_000
    enumerated = {(t.a, t.b, t.c) for t in primitive_triples(bound)}
    spine = {(t.a, t.b, t.c) for t in spine_terms_up_to(bound)}
    assert spine <= enumerated
    # and the spine is exactly the enumerated triples with b - a = 1
    assert spine == {(a, b, c) for (a, b, c) in enumerated if b - a == 1}


def test_spine_up_to_bound():
    assert [t.c for t in spine_terms_up_to(5_000_000)] == EXPECTED_HYPOTENUSES
    assert [t.c for t in spine_terms_up_to(1000)] == [5, 29, 169, 985]
    assert spine_terms_up_to(4) == []


def test_growth_ratios_bounded_by_limit_exactly():
    """Lemma 4.3: c_{j+1}/c_j < 3 + 2*sqrt(2) < 7, tested in exact integers.

    Since c_{j+1} > 3 c_j, the bound c_{j+1}/c_j < 3 + 2*sqrt(2) is equivalent
    to (c_{j+1} - 3 c_j)^2 < 8 c_j^2, which involves no irrational quantity.
    A float comparison would fail here: by j ~ 15 the double-precision ratio
    rounds to the limit itself.
    """
    cs = hypotenuse_recurrence(22)
    assert all((cs[j + 1] - 3 * cs[j]) ** 2 < 8 * cs[j] ** 2 for j in range(len(cs) - 1))
    assert all(cs[j + 1] < 7 * cs[j] for j in range(len(cs) - 1))
    # ratios increase strictly toward the limit: c_{j+1}^2 < c_j * c_{j+2}
    assert all(cs[j + 1] ** 2 < cs[j] * cs[j + 2] for j in range(len(cs) - 2))
    # and they do converge to it numerically
    assert abs(cs[-1] / cs[-2] - LIMITING_GROWTH) < 1e-9


def test_limiting_contraction_constant():
    assert abs(LIMITING_CONTRACTION - (3 - 2 * sqrt(2))) < 1e-15
    assert abs(LIMITING_CONTRACTION * LIMITING_GROWTH - 1.0) < 1e-12
    assert f"{LIMITING_CONTRACTION:.10f}" == "0.1715728753"
