# The Pell Spine as an Optimal Rational Separator

> **Companion repository for the archived Zenodo manuscript.**
> The manuscript is the scholarly record; this repository provides deterministic computational reproduction of its arithmetic results.

**Paper (archival record):** https://doi.org/10.5281/zenodo.21510910

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21510910.svg)](https://doi.org/10.5281/zenodo.21510910)

This DOI represents all versions of the Zenodo record and resolves to the latest version.

---

## Purpose

This repository exists so that an independent reader can rerun the arithmetic
behind Sections 3–5 and Appendices A–B of the paper. It is a supplement, not a
replacement: **the manuscript is the primary scholarly record**, and the
repository deliberately reproduces only the parts of it that benefit from
independent computation.

The theorem is proved in the manuscript. The finite enumeration in this
repository is an independent computational confirmation, not the proof.

## The main theorem

For a primitive Pythagorean triple, order the legs so that `a < b` and define
the normalized separation

```
Delta_k = (b - a) / c.
```

**Theorem (Theorem 4.4 of the paper).** When primitive Pythagorean triples are
ordered by increasing hypotenuse, the record minima of `Delta_k` are attained
*exactly* at the near-isosceles triples with `b - a = 1` — the Pell spine
`(3,4,5), (20,21,29), (119,120,169), ...` — for which `c * Delta_k = 1`. The
record sequence contracts with limiting ratio `3 - 2*sqrt(2) = 0.171572875...`

The proof rests on two facts. In the shifted parametrization `m = s + n`, the
leg difference is `|s^2 - 2n^2|` with `gcd(s, n) = 1`, so `2` is a quadratic
residue modulo every prime divisor of the difference; hence every such prime is
`±1 (mod 8)` and the difference is `1` or at least `7`. Consecutive spine
hypotenuses grow by a factor below `3 + 2*sqrt(2) < 7`, which closes the gap.

## What this repository reproduces

1. Enumeration of all primitive Pythagorean triples up to a chosen hypotenuse bound.
2. The count of primitive triples with `c <= 5,000,000`.
3. The record-minimum sequence of `Delta_k`, computed with exact integer arithmetic.
4. Verification that the records are exactly the Pell-spine triples within the tested range.
5. The Pell-spine recurrence `c_{j+1} = 6 c_j - c_{j-1}` and the identity `u^2 - 2 c^2 = -1`.
6. Tables 2 and 3, and Figures 1 and 2.

## Installation

Requires Python 3.10 or newer.

```bash
git clone <this repository>
cd pell-spine-optimal-separator
python -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
```

## One-command reproduction

```bash
python reproduce.py
```

For a quick check on a smaller bound:

```bash
python reproduce.py --cmax 100000
```

The full run enumerates 795,763 triples. On a single modern core it completes
in well under a minute (measured: about 6 seconds, 257 MiB peak resident
memory), since the triples are held in memory to be grouped by hypotenuse.
Running the same command twice in the same environment produces identical
scientific outputs, including byte-identical CSV files and figures. No random
sampling is used anywhere and PNG creation-date metadata is suppressed. Across
*different* environments the CSV files remain byte-identical, since they are
produced by pure-Python integer and rational arithmetic; the PNG bytes may
differ between matplotlib versions because the rendering differs, while the
plotted content does not.

## Expected output

The summary printed by the full run includes:

```
Primitive triples with c <= 5000000: 795763
Record minima found: 8
All records have b-a = 1: True
All records satisfy c*Delta_k = 1: True
```

and the record sequence

| # | a | b | c | b − a | Delta_k | c · Delta_k |
|---|---|---|---|-------|---------|-------------|
| 1 | 3 | 4 | 5 | 1 | 0.200000000000 | 1 |
| 2 | 20 | 21 | 29 | 1 | 0.034482758621 | 1 |
| 3 | 119 | 120 | 169 | 1 | 0.005917159763 | 1 |
| 4 | 696 | 697 | 985 | 1 | 0.001015228426 | 1 |
| 5 | 4059 | 4060 | 5741 | 1 | 0.000174185682 | 1 |
| 6 | 23660 | 23661 | 33461 | 1 | 0.000029885538 | 1 |
| 7 | 137903 | 137904 | 195025 | 1 | 0.000005127548 | 1 |
| 8 | 803760 | 803761 | 1136689 | 1 | 0.000000879748 | 1 |

The run also writes `data/record_minima_c5e6.csv`, `data/pell_spine_terms.csv`,
`figures/figure_1_separation_cloud.png` and `figures/figure_2_record_staircase.png`.

## Repository structure

```
pell-spine-optimal-separator/
├── README.md
├── AUDIT.md                 notes on manuscript numerics checked here
├── LICENSE                  CC BY 4.0 (prose, data, figures, manuscript)
├── LICENSE-CODE             MIT (source code)
├── CITATION.cff
├── requirements.txt
├── pytest.ini
├── conftest.py              puts src/ on the import path for pytest
├── .gitignore
├── paper/
│   └── manuscript.pdf
├── src/
│   ├── enumerate_triples.py   Euclid enumeration, leg-ordering convention
│   ├── pell_spine.py          spine terms, integer recurrences, Pell identity
│   ├── verify_records.py      exact record logic and CSV writers
│   └── generate_figures.py    deterministic Figures 1 and 2
├── data/
│   ├── README.md
│   ├── record_minima_c5e6.csv
│   └── pell_spine_terms.csv
├── figures/
│   ├── figure_1_separation_cloud.png
│   └── figure_2_record_staircase.png
├── tests/
│   ├── test_enumeration.py
│   ├── test_pell_spine.py
│   └── test_records.py
└── reproduce.py
```

## Leg-ordering convention

Euclid's parametrization gives `x = m^2 - n^2`, `y = 2mn`, `c = m^2 + n^2`
with `m > n >= 1`, `gcd(m, n) = 1`, `m - n` odd. This repository then sets
`a = min(x, y)` and `b = max(x, y)`, so `a < b` throughout the code, data,
tests, figures and this README. Section 2 of the manuscript instead lets `a`
be the odd leg and `b` the even leg and works with `|b - a|`; the two
conventions give the same leg difference and the same `Delta_k`.

## Exact arithmetic

Record detection uses exact integer arithmetic only. Separations are compared
by cross-multiplication,

```python
if best_d is None or d * best_c < best_d * c:
```

never by comparing floating-point quotients. `Delta_k` values are carried as
`fractions.Fraction` where a rational value is needed. Floating point appears
only in plotting and in the human-readable decimal column of the CSV output.

Ties are handled explicitly: triples are grouped by hypotenuse before the
running record is updated, the minimum within a group is taken, and that
minimum is compared against the best value from strictly smaller hypotenuses.
If several triples were to share a hypotenuse and attain the same minimal
`Delta_k`, all of them would satisfy Definition 4.1 and all would be reported.
No such tie occurs anywhere in `c <= 5,000,000`. Nothing in the record logic
depends on incidental tuple-sort ordering.

## Scope and limitations

- The smooth-transport results in Section 6 are analytic consequences of
  Taylor's theorem and are not independently established by the computational
  repository. This repository focuses on reproducing the arithmetic
  enumeration and record-minimum results.
- Figure 3 (the transport fan) is a schematic and remains only in the
  manuscript.
- The enumeration is a finite check over `c <= 5,000,000`. It confirms the
  theorem on that range; it does not and cannot establish the infinite
  statement.
- The claimed optimality is specific to primitive Pythagorean triples ordered
  by hypotenuse and the objective `Delta_k = (b - a)/c`. It is not a claim
  that `a/c` is the ordinary best rational approximation to `1/sqrt(2)`; the
  error `|a/c - 1/sqrt(2)|` is of order `1/c`, not `1/c^2`. The classical
  best-approximation property belongs to `u/c` and `s/n`, not to `a/c`
  (Remark 3.4 and Table 1 of the paper).
- No physical realization is claimed. The oscillator assignment in Section 6.5
  requires an externally supplied time scale and is not reproduced here.

## Citation

Cite the paper, not the repository:

> De Jesús, E. (2026). *The Pell Spine as an Optimal Rational Separator:
> Extremal Resolution and Smooth Transport in Primitive Pythagorean Triples.*
> Zenodo. https://doi.org/10.5281/zenodo.21510910

Machine-readable metadata is in `CITATION.cff`.

## Licensing

Two licenses apply, and the distinction is deliberate:

- **Source code** (`src/`, `tests/`, `reproduce.py`, `conftest.py`): MIT
  License, see `LICENSE-CODE`.
- **Manuscript, README prose, data tables and figures** (`paper/`, `data/`,
  `figures/`, and this file): Creative Commons Attribution 4.0 International
  (CC BY 4.0), see `LICENSE`.

## AI-assistance disclosure

AI assistance (Anthropic's Claude) was used for algebraic and computational
verification, adversarial auditing, repository construction, testing, and
manuscript preparation. Conceptual development, research direction,
interpretation, and final responsibility for all content remain with the
author. AI systems are not authors.

## Author

Elias De Jesús — Independent Researcher
ORCID: [0009-0007-0190-9143](https://orcid.org/0009-0007-0190-9143)
Email: dejesuselias10@gmail.com
