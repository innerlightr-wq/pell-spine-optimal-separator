"""Tests for the primitive-triple enumeration."""

from math import gcd

import pytest

from enumerate_triples import (
    count_primitive_triples,
    is_primitive_triple,
    leg_differences,
    primitive_triples,
    sorted_triples,
)

# Independently checked counts of primitive triples with c <= bound.
# The asymptotic density is bound/(2*pi); e.g. 5e6/(2*pi) = 795775, close to
# the exact 795763, which is a useful sanity anchor against undercounting.
KNOWN_COUNTS = {100: 16, 1000: 158, 10_000: 1593, 100_000: 15_919, 1_000_000: 159_139}

# All 16 primitive triples with c <= 100, in the a < b convention.
TRIPLES_TO_100 = {
    (3, 4, 5), (5, 12, 13), (7, 24, 25), (8, 15, 17), (9, 40, 41),
    (11, 60, 61), (12, 35, 37), (13, 84, 85), (16, 63, 65), (20, 21, 29),
    (28, 45, 53), (33, 56, 65), (36, 77, 85), (39, 80, 89), (48, 55, 73),
    (65, 72, 97),
}


def test_known_small_triples_exactly():
    got = {(t.a, t.b, t.c) for t in primitive_triples(100)}
    assert got == TRIPLES_TO_100


@pytest.mark.parametrize("bound,expected", sorted(KNOWN_COUNTS.items()))
def test_known_counts(bound, expected):
    assert count_primitive_triples(bound) == expected


def test_primitiveness_and_conventions():
    for t in primitive_triples(20_000):
        assert t.a * t.a + t.b * t.b == t.c * t.c
        assert gcd(t.a, t.b) == 1
        assert t.a < t.b, "leg-ordering convention a < b must hold"
        assert t.d == t.b - t.a > 0
        assert t.c <= 20_000
        # one leg odd, one even, so the difference is odd
        assert (t.a % 2) != (t.b % 2)


def test_no_duplicate_triples():
    triples = list(primitive_triples(200_000))
    assert len(triples) == len({(t.a, t.b, t.c) for t in triples})


def test_sorted_by_hypotenuse():
    cs = [t.c for t in sorted_triples(50_000)]
    assert cs == sorted(cs)


def test_enumeration_is_deterministic():
    assert list(primitive_triples(30_000)) == list(primitive_triples(30_000))


def test_no_triples_below_smallest_hypotenuse():
    assert list(primitive_triples(4)) == []
    assert [(t.a, t.b, t.c) for t in primitive_triples(5)] == [(3, 4, 5)]


def test_admissible_leg_differences_lemma_4_2():
    """Lemma 4.2: every leg difference is 1 or >= 7, with all prime factors
    congruent to +-1 (mod 8)."""
    diffs = leg_differences(list(primitive_triples(200_000)))
    assert all(d == 1 or d >= 7 for d in diffs)
    assert not ({3, 5, 9, 11, 13, 15} & set(diffs))
    for d in diffs:
        for p in _prime_factors(d):
            assert p % 8 in (1, 7), f"prime {p} of difference {d} is not +-1 mod 8"


def test_first_sixteen_leg_differences_match_manuscript():
    diffs = leg_differences(list(primitive_triples(5_000_000 // 50)))
    assert diffs[:16] == [1, 7, 17, 23, 31, 41, 47, 49, 71, 73, 79, 89, 97, 103, 113, 119]


def test_is_primitive_triple_helper():
    assert is_primitive_triple(3, 4, 5)
    assert not is_primitive_triple(6, 8, 10)  # not primitive
    assert not is_primitive_triple(3, 4, 6)  # not Pythagorean


def _prime_factors(n: int):
    factors = set()
    d = 3  # all leg differences are odd
    while d * d <= n:
        while n % d == 0:
            factors.add(d)
            n //= d
        d += 2
    if n > 1:
        factors.add(n)
    return factors
