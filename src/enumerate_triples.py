"""Enumeration of primitive Pythagorean triples via Euclid's parametrization.

Leg-ordering convention (used everywhere in this repository)
------------------------------------------------------------
Euclid's parametrization produces the two legs

    x = m^2 - n^2   (odd leg),    y = 2mn   (even leg),    c = m^2 + n^2,

subject to  m > n >= 1,  gcd(m, n) = 1,  m - n odd,  c <= cmax.

We then *reorder the legs by size*:

    a = min(x, y),   b = max(x, y),   so that  a < b,

and define the normalized separation

    Delta_k = (b - a) / c.

Note that the manuscript's Section 2 uses the alternative convention in which
`a` is the odd leg and `b` the even leg, and works with |b - a|.  The two
conventions give the same leg difference and the same Delta_k, since
|b - a| is invariant under swapping the legs.  This repository uses a < b
consistently (see AUDIT.md, item 3).

All arithmetic here is exact integer arithmetic.  Floating point is used
nowhere in this module.
"""

from __future__ import annotations

from math import gcd, isqrt
from typing import Iterator, List, NamedTuple


class Triple(NamedTuple):
    """A primitive Pythagorean triple, stored in canonical sort order.

    Fields are ordered (c, d, a, b) so that the natural tuple ordering sorts
    by increasing hypotenuse first.  Record logic never relies on this
    ordering to break ties; see ``verify_records.record_minima``.
    """

    c: int  # hypotenuse
    d: int  # leg difference b - a  (>= 1)
    a: int  # smaller leg
    b: int  # larger leg


def primitive_triples(cmax: int) -> Iterator[Triple]:
    """Yield every primitive Pythagorean triple with hypotenuse c <= cmax.

    Generation order is deterministic: m ascending, then n ascending.
    Each primitive triple is produced exactly once (Proposition 2.1 of the
    manuscript states the correspondence is a bijection).

    The bound m <= isqrt(cmax) is exact and must not be tightened: since
    c = m^2 + n^2 > m^2, any triple with c <= cmax has m <= sqrt(cmax).
    Truncating m below floor(sqrt(cmax)) silently drops the thin
    large-m / small-n family and undercounts substantially.
    """
    if cmax < 5:
        return
    for m in range(2, isqrt(cmax) + 1):
        m2 = m * m
        for n in range(1, m):
            if (m - n) % 2 == 0 or gcd(m, n) != 1:
                continue
            c = m2 + n * n
            if c > cmax:
                # For fixed m the hypotenuse is strictly increasing in n,
                # so no larger n can qualify.
                break
            x = m2 - n * n
            y = 2 * m * n
            a, b = (x, y) if x < y else (y, x)
            yield Triple(c=c, d=b - a, a=a, b=b)


def sorted_triples(cmax: int) -> List[Triple]:
    """All primitive triples with c <= cmax, sorted by increasing hypotenuse.

    Sorting uses the hypotenuse as the sole key.  Python's sort is stable, so
    triples sharing a hypotenuse retain their generation order, which makes
    the output fully deterministic without letting incidental tuple ordering
    define any mathematics.
    """
    return sorted(primitive_triples(cmax), key=lambda t: t.c)


def count_primitive_triples(cmax: int) -> int:
    """Count primitive triples with c <= cmax without materializing them."""
    return sum(1 for _ in primitive_triples(cmax))


def leg_differences(triples) -> List[int]:
    """Sorted list of the distinct leg differences occurring in ``triples``.

    Lemma 4.2 of the manuscript proves every such value is 1 or >= 7, with
    all prime factors congruent to +-1 (mod 8).
    """
    return sorted({t.d for t in triples})


def is_primitive_triple(a: int, b: int, c: int) -> bool:
    """Exact check that (a, b, c) is a primitive Pythagorean triple."""
    return a > 0 and b > 0 and c > 0 and a * a + b * b == c * c and gcd(a, b) == 1
