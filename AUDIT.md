# Manuscript audit

Notes from checking the manuscript's computational claims against independent
computation while building this repository. The manuscript PDF in `paper/` is
the version supplied by the author and has **not** been altered.

None of the items below affects Theorem 4.4, its proof, or any Tier-1 result.

## Confirmed

All of the following were recomputed independently and agree with the
manuscript exactly.

| claim | location | status |
|---|---|---|
| 795,763 primitive triples with `c <= 5x10^6` | §5 | confirmed |
| Record minima: `c = 5, 29, 169, 985, 5741, 33461, 195025, 1136689` | Table 2 | confirmed |
| Every record has `b - a = 1` and `c * Delta_k = 1` | Table 2 | confirmed |
| `Delta_k` decimals to 12 places | Table 2 | confirmed |
| First 16 admissible leg differences: `1, 7, 17, 23, 31, 41, 47, 49, 71, 73, 79, 89, 97, 103, 113, 119` | §5 | confirmed |
| No observed difference in `{3, 5, 9, 11, 13, 15}`; all prime factors `±1 (mod 8)` | Lemma 4.2, §5 | confirmed |
| Table 1: errors of `u/c` scale as `c^-2`, of `a/c` as `c^-1`; all listed values | Table 1 | confirmed |
| Table 3: all `(s, n, a, b, c, u, Delta_k)` entries | Table 3 | confirmed |
| Recurrences `c_{j+1} = 6c_j - c_{j-1}` (`c_0 = 1`) and `u_{j+1} = 6u_j - u_{j-1}` (`u_0 = 1`) | App. B | confirmed |
| `u^2 - 2c^2 = -1` along the spine | Prop. 3.2 | confirmed |
| `q = 3 - 2*sqrt(2) = 0.1715728752...` | App. B | confirmed |
| `q^2 = 0.0294372515...` | App. B | confirmed |
| `K(1/sqrt(2)) = 1.8540746773...` | Def. 6.8, App. B | confirmed |
| `C_K = 0.6462200520...` | Prop. 6.10, App. B | confirmed |
| `log10(3 + 2*sqrt(2)) = 0.76555...`, `log10(29/5) = 0.76343` | Fig. 2 caption | confirmed |

## Discrepancies found

These were identified before this repository was built and remain present in
the supplied PDF. They are recorded here rather than corrected in place.

**1. Table 4 — numerical ratio for the second-order observables.**
Table 4 reports `0.029440827` as the numerical ratio at `j = 7 -> 8` for both
`R - 1` and `g = R^3(R - 1)`. Computing the exact rational
`R_j - 1 = (2c_j^2 - 1)/(c_j^2 - 1)^2` at `c_7 = 195025` and `c_8 = 1136689`
gives

```
(R_8 - 1)/(R_7 - 1) = 0.0294372515219...
g_8 / g_7           = 0.0294372515174...
```

against the limit `q^2 = 0.0294372515229...`. The correct value is therefore
approximately **0.029437252**, not 0.029440827. The reported figure differs in
the sixth significant digit and appears to be a transcription error; the
first-order entries in the same table (`0.171572875`) are correct.

**2. Appendix B — the constant `C_K/sqrt(2)`.**
Appendix B gives `C_K/sqrt(2) = 0.4569465817...`. Evaluating
`C_K = (dK/dk)/K` at `k = 1/sqrt(2)` to 40 digits and dividing by `sqrt(2)`
gives

```
C_K / sqrt(2) = 0.45694658104446...
```

so the value is **0.4569465810**, not 0.4569465817; the last two digits are
wrong. Corollary 6.11's rounded statement `0.4569466...` is unaffected, and
the numerically computed `delta_j / sqrt(R_j - 1)` at `j = 8` agrees with
`0.456946581044`.

**3. Leg-ordering convention.**
Section 2 states that `a` is the odd leg and `b` the even leg and explicitly
does not assume `a < b`, whereas the abstract, Tables 2 and 3 all use `a < b`.
The two agree for `Delta_k`, which depends only on `|b - a|`. They do not agree
in the elliptic-detuning material of Section 6.4, where `k = a/c` and
`k' = b/c` are treated as an ordered pair: under the odd/even convention a
triple such as `(15, 8, 17)` would give `k > k'` and flip the sign of
`delta = log(K(k')/K(k))`. Adopting `a < b` uniformly, as the abstract already
does, removes the ambiguity. This repository uses `a < b` throughout.

## Notes on the appendix listing

The reference implementation in Appendix A uses `if d / c < best`, a
floating-point comparison. It produces the correct answer over
`c <= 5x10^6`, where the separations involved are far from the limits of
double precision, but the comparison is not exact in general. This repository
uses integer cross-multiplication instead (see `src/verify_records.py`), and
the test suite includes a case where the float comparison would fail.

The appendix listing also does not group triples by hypotenuse, so its
behaviour at equal `c` is determined by tuple-sort order rather than stated
explicitly. No tie of that kind occurs in the tested range — no two primitive
triples with the same hypotenuse share a leg difference for `c <= 5x10^6` — so
the two implementations agree here.
