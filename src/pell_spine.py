"""The Pell spine: primitive Pythagorean triples with b - a = 1.

The spine is generated here by exact integer recurrences only.  No
floating-point approximation enters the generation or the verification of
any identity; floats appear solely in ``LIMITING_CONTRACTION`` and
``LIMITING_GROWTH``, which are reported for context.

Definitions follow the manuscript (Proposition 3.2 and Appendix B):

    s_{j+1} = s_j + 2 n_j,      n_{j+1} = s_j + n_j,       (s_1, n_1) = (1, 1)
    c_{j+1} = 6 c_j - c_{j-1},  with  c_0 = 1,  c_1 = 5
    u_{j+1} = 6 u_j - u_{j-1},  with  u_0 = 1,  u_1 = 7

where s/n are the convergents of sqrt(2), c is the hypotenuse and u = a + b
satisfies the negative Pell equation u^2 - 2 c^2 = -1.

Note on indexing: c_0 = 1 is the degenerate seed required by the recurrence;
it is not the hypotenuse of a triple.  Spine terms are indexed from j = 1,
matching Table 3 of the manuscript.
"""

from __future__ import annotations

from math import sqrt
from typing import List, NamedTuple

# Limiting ratios, reported for context only; never used in exact tests.
LIMITING_GROWTH = 3.0 + 2.0 * sqrt(2.0)      # c_{j+1}/c_j  -> 5.828427...
LIMITING_CONTRACTION = 3.0 - 2.0 * sqrt(2.0)  # Delta_k ratio -> 0.171572...


class SpineTerm(NamedTuple):
    """One element of the Pell spine, indexed as in Table 3 (j starts at 1)."""

    index: int
    s: int
    n: int
    a: int
    b: int
    c: int
    u: int  # u = a + b


def spine_terms(count: int) -> List[SpineTerm]:
    """First ``count`` spine terms, built from the (s, n) convergent recurrence.

    From (s, n) we set m = s + n and apply Euclid's parametrization, then
    order the legs as a < b (the repository-wide convention).
    """
    terms: List[SpineTerm] = []
    s, n = 1, 1
    for j in range(1, count + 1):
        m = s + n
        x, y = m * m - n * n, 2 * m * n
        a, b = (x, y) if x < y else (y, x)
        c = m * m + n * n
        terms.append(SpineTerm(index=j, s=s, n=n, a=a, b=b, c=c, u=a + b))
        s, n = s + 2 * n, s + n
    return terms


def spine_terms_up_to(cmax: int) -> List[SpineTerm]:
    """Spine terms with hypotenuse c <= cmax."""
    terms: List[SpineTerm] = []
    s, n = 1, 1
    j = 1
    while True:
        m = s + n
        c = m * m + n * n
        if c > cmax:
            return terms
        x, y = m * m - n * n, 2 * m * n
        a, b = (x, y) if x < y else (y, x)
        terms.append(SpineTerm(index=j, s=s, n=n, a=a, b=b, c=c, u=a + b))
        s, n = s + 2 * n, s + n
        j += 1


def hypotenuse_recurrence(count: int) -> List[int]:
    """Hypotenuses from c_{j+1} = 6 c_j - c_{j-1}, c_0 = 1, c_1 = 5.

    Returns [c_1, ..., c_count]; the seed c_0 = 1 is not included because it
    is not a triple hypotenuse.
    """
    if count <= 0:
        return []
    seq = [1, 5]  # c_0, c_1
    while len(seq) < count + 1:
        seq.append(6 * seq[-1] - seq[-2])
    return seq[1:]


def u_recurrence(count: int) -> List[int]:
    """u-values from u_{j+1} = 6 u_j - u_{j-1}, u_0 = 1, u_1 = 7."""
    if count <= 0:
        return []
    seq = [1, 7]
    while len(seq) < count + 1:
        seq.append(6 * seq[-1] - seq[-2])
    return seq[1:]


def verify_spine(terms: List[SpineTerm]) -> dict:
    """Exact structural checks on a list of spine terms.

    Returns a dict of booleans, all of which must be True:
      leg_difference_one  : b - a = 1 for every term
      pythagorean         : a^2 + b^2 = c^2
      primitive           : gcd(a, b) = 1
      pell_identity       : u^2 - 2 c^2 = -1 with u = a + b
      c_recurrence        : c_{j+1} = 6 c_j - c_{j-1} (seed c_0 = 1)
      u_recurrence        : u_{j+1} = 6 u_j - u_{j-1} (seed u_0 = 1)
    """
    from math import gcd

    cs = [1] + [t.c for t in terms]  # prepend seed c_0 = 1
    us = [1] + [t.u for t in terms]  # prepend seed u_0 = 1
    return {
        "leg_difference_one": all(t.b - t.a == 1 for t in terms),
        "pythagorean": all(t.a * t.a + t.b * t.b == t.c * t.c for t in terms),
        "primitive": all(gcd(t.a, t.b) == 1 for t in terms),
        "pell_identity": all(t.u * t.u - 2 * t.c * t.c == -1 for t in terms),
        "c_recurrence": all(
            cs[j + 1] == 6 * cs[j] - cs[j - 1] for j in range(1, len(cs) - 1)
        ),
        "u_recurrence": all(
            us[j + 1] == 6 * us[j] - us[j - 1] for j in range(1, len(us) - 1)
        ),
    }
