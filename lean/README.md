# Stages A and C — Lean 4 formalization of the two record theorems

A self-contained, `sorry`-free formalization of the two complementary record
theorems for positive primitive Pythagorean triples ordered by hypotenuse, with
legs written `a < b`:

> **Stage A (record minima).** A triple is a chronological record **minimum** of
> `Δ = (b − a)/c` if and only if `b − a = 1`.
>
> **Stage C (record maxima).** A triple is a chronological record **maximum** of
> `Δ`, equivalently a record **minimum** of `h = ab/c²`, if and only if
> `c − b = 1`.

Headline statements:

| | |
|---|---|
| `PellRecord.record_min_iff_leg_difference_one` | [`PellRecord/Main.lean`](PellRecord/Main.lean) |
| `PellRecord.record_max_iff_boundary_defect_one` | [`PellRecord/BoundaryMain.lean`](PellRecord/BoundaryMain.lean) |
| `PellRecord.record_min_h_iff_boundary_defect_one` | [`PellRecord/BoundaryMain.lean`](PellRecord/BoundaryMain.lean) |

Stages A and C only. Pell enumeration completeness, counting asymptotics
(logarithmic versus square-root), envelope limits, majorization and entropy,
elliptic transport, and any classification by algebraic degree are **not**
formalized here and are not assumed anywhere.

## Build

```bash
cd lean
lake exe cache get          # only if .lake/packages is absent; see "Toolchain"
lake build                  # builds the four modules; ~10 s once mathlib is in place
lake env lean axioms_check.lean    # the axiom audit, output quoted below
```

The `lake build` must end with no `error:` lines and no `warning: declaration uses 'sorry'`.

### Module dependency structure

```
PellRecord.Basic            Adm, IsRecordMin, c >= 5, the ℚ bridge
  └─ PellRecord.Gap         d odd, 3 ∤ d, 5 ∤ d  ⟹  d = 1 ∨ 7 ≤ d
       └─ PellRecord.Ladder Pell ladder, growth < 6, bracketing
            └─ PellRecord.Main          STAGE A theorem
                 └─ PellRecord.Boundary order mechanism: w ↔ Δ ↔ h
                      └─ PellRecord.BoundaryMain      STAGE C theorem
                           └─ PellRecord.BoundaryExamples  examples + parametrization
```

Stage C reuses Stage A's `Adm`, `Adm.dpos`, `Adm.cpos`, `Adm.five_le_c` and the
example triples; it introduces no competing model of a triple and changes no
Stage A statement.

### Toolchain

Pinned, and chosen to match a mathlib build already present on the development
machine so that no new mathlib compilation was needed:

| | |
|---|---|
| Lean | `leanprover/lean4:v4.33.1` (`lean-toolchain`) |
| mathlib | tag `v4.33.1`, revision `0df444a360` (`lake-manifest.json`) |
| other deps | batteries, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli — all at the revisions mathlib `v4.33.1` pins |

No `lake update` was run and no unrelated project was touched.

**Dependency isolation.** The first setup populated `.lake/packages` by *hard
linking* from a sibling project, so the two shared inodes and a write by `lake`
would have modified the sibling's mathlib in place. That has been corrected: the
tree was replaced with a btrfs **reflink** copy (`cp --reflink=always`), which
gives independent inodes with copy-on-write extents — isolated for writing, and
still costing no extra disk. Verified by `stat -c %i` (distinct inodes, link
count 1) and by rebuilding both projects afterwards.

## Source/version map

| artifact | version used | note |
|---|---|---|
| repository | branch `lean-record-core`, from `cbdd2227b495f568d98cb5f312aef27f196a0927` | the starting commit was verified, not assumed |
| manuscript | `paper/manuscript.pdf`, md5 `bd4bcbdf1982d52d962777c302a8d9cd`, 14 pp. | **the version formalized** |
| revised manuscript | `~/Downloads/pell_spine_rev (2).pdf`, md5 `3f12d1f851c1665e2a003eb03482ee61`, 26 pp. | consulted; **Stage A is unchanged** between the two — Definition 4.1, Lemmas 4.2–4.3 and Theorem 4.4 agree verbatim. The revision adds §4.1 on prior art, which is why no novelty is claimed below for the `d = 1` family. |
| boundary paper | `~/Downloads/record_density_pythagorean_quarter_circle (1).pdf`, 11 pp. | **the version formalized for Stage C**: Definition 1.1, Theorem 1.4, Proposition 2.1(ii), Lemmas 3.2–3.4 |
| partitions paper | `pythagorean_partitions (1) (2).pdf` | **not used.** Its boundary-record statement is only computational, and its odd-leg-first orientation is the issue recorded in the Stage A brief; superseded here by the boundary paper |
| `AUDIT.md` | as committed | §3 (leg-ordering) is the item that matters here: this formalization adopts `a < b` uniformly, as the repository does |

The three copies of `pell_spine_rev*.pdf` in `~/Downloads` are byte-identical.

## Definitions

In [`PellRecord/Basic.lean`](PellRecord/Basic.lean), over `ℤ`:

```lean
structure Adm (a b c : ℤ) : Prop where
  apos : 0 < a
  altb : a < b            -- legs ordered; a is NOT required to be odd
  cpos : 0 < c
  pyth : a * a + b * b = c * c
  cop  : Int.gcd a b = 1

def IsRecordMin (a b c : ℤ) : Prop :=
  Adm a b c ∧
  (∀ a' b' c', Adm a' b' c' → c' < c → (b - a) * c' < (b' - a') * c) ∧
  (∀ a' b' c', Adm a' b' c' → c' = c → (b - a) * c' ≤ (b' - a') * c)
```

Three points of fidelity:

* **The quantifier is universal.** `IsRecordMin` ranges over *all* admissible
  triples, not a finite enumeration and not a generated subfamily.
* **Comparisons are exact cross-multiplications**, never quotients, matching
  `src/verify_records.py` rather than the manuscript appendix's float comparison.
  `lt_div_iff_cross` / `le_div_iff_cross` prove the bridge to `ℚ` quotients; the
  development does not otherwise use them.
* **Equal heights are handled explicitly**, by the second clause, exactly as in
  Definition 4.1.

## Stage C definitions

In [`PellRecord/Boundary.lean`](PellRecord/Boundary.lean). The boundary defect is
`g = c − b` (the source's `c − max(a,b)`, under the canonical `a < b`).

```lean
def IsRecordMinW (a b c : ℤ) : Prop :=          -- record minimum of w = (c-b)/c
  Adm a b c ∧
  (∀ a' b' c', Adm a' b' c' → c' < c → (c - b) * c' < (c' - b') * c) ∧
  (∀ a' b' c', Adm a' b' c' → c' = c → (c - b) * c' ≤ (c' - b') * c)

def IsRecordMax (a b c : ℤ) : Prop :=           -- record maximum of Δ = (b-a)/c
  Adm a b c ∧
  (∀ a' b' c', Adm a' b' c' → c' < c → (b' - a') * c < (b - a) * c') ∧
  (∀ a' b' c', Adm a' b' c' → c' = c → (b' - a') * c ≤ (b - a) * c')

def IsRecordMinH (a b c : ℤ) : Prop :=          -- record minimum of h = ab/c²
  Adm a b c ∧
  (∀ a' b' c', Adm a' b' c' → c' < c → a * b * (c' * c') < a' * b' * (c * c)) ∧
  (∀ a' b' c', Adm a' b' c' → c' = c → a * b * (c' * c') ≤ a' * b' * (c * c))
```

`IsRecordMax` is `IsRecordMin` with both inequalities reversed, as Definition 1.1
of the source requires. All three quantify over **every** admissible triple, and
all comparisons are exact integer cross-multiplications. The name `IsRecordMax`
was free; Stage A's `IsRecordMin` is untouched.

## The two chronologies

| | Stage A | Stage C |
|---|---|---|
| extremum | record **minimum** of `Δ` | record **maximum** of `Δ` = record minimum of `h` |
| characterised by | `b − a = 1` | `c − b = 1` |
| ladder | `5, 29, 169, 985, …` (Pell) | `5, 13, 25, 41, 61, …` (centered squares) |
| growth | geometric, `< 6` per step | quadratic, `≤ 2` per step **for n ≥ 2 only** |
| gap in the numerator | `d = 1 ∨ d ≥ 7` (needs residues) | `g = 1 ∨ g ≥ 2` (free: `g` is a positive integer) |
| extra ingredient | — | the initial gap, to cover the failed growth step |

`(3,4,5)` is in both. `(5,12,13)` is a maximum but not a minimum; `(20,21,29)` is
a minimum but not a maximum. All four facts are proved
(`record_both_3_4_5`, `recordMax_5_12_13`, `not_recordMin_5_12_13`,
`recordMin_not_max_20_21_29`).

## Theorem status

| statement | Lean name | status |
|---|---|---|
| minimum hypotenuse `c ≥ 5` | `Adm.five_le_c` | **proved** |
| leg difference is positive | `Adm.dpos` | **proved** |
| leg difference is odd | `odd_diff` | **proved** (via mathlib `even_odd_of_coprime`) |
| `3 ∤ d`, `5 ∤ d` | `not_three_dvd_diff`, `not_five_dvd_diff` | **proved** |
| **arithmetic gap** `d = 1 ∨ 7 ≤ d` | `gap` | **proved** |
| ladder invariant, admissibility | `ladder_inv`, `ladder_adm` | **proved** |
| ladder is strictly increasing | `C_lt_C_succ` | **proved** |
| **slow growth** `C (j+1) < 6 · C j` | `C_succ_lt_six_mul` | **proved** |
| unboundedness `j + 5 ≤ C j` | `C_ge_index` | **proved** |
| **bracketing** `∃ j, C j ≤ c < C (j+1)` | `bracket` | **proved** |
| `d = 1` ⟹ record | `record_of_diff_one` | **proved** |
| record ⟹ `d = 1` | `diff_one_of_record` | **proved** |
| **Stage A theorem** | `record_min_iff_leg_difference_one` | **proved, unconditional** |
| `(3,4,5)`, `(20,21,29)` are records | `record_3_4_5`, `record_20_21_29` | **proved** |
| `(5,12,13)` is not | `not_record_5_12_13` | **proved** |
| **— Stage C —** | | |
| boundary defect positive, `g = 1 ∨ 2 ≤ g` | `Adm.gpos`, `Adm.defect_gap` | **proved** |
| larger `b/c` ⟹ smaller `a/c` | `key_a_of_b`, `key_a_of_b_eq` | **proved** |
| `w` ↔ `Δ` order transfer (strict, non-strict) | `w_lt_iff_delta_gt`, `w_le_iff_delta_ge` | **proved** |
| `h` ↔ `Δ` order transfer (`Δ² = 1 − 2h`) | `h_lt_iff_delta_gt`, `h_le_iff_delta_ge` | **proved** |
| the three record classes coincide | `recordMinW_iff_recordMax`, `recordMinH_iff_recordMax` | **proved** |
| boundary ladder admissible, defect `1` | `badm`, `BC_sub_BB` | **proved** |
| ladder strictly increasing, unbounded | `BC_strict_mono`, `BC_ge_index` | **proved** |
| `c_{n+1} ≤ 2 c_n` for `n ≥ 2` | `BC_growth` | **proved** |
| …and the `n = 1` exception, explicitly | `BC_growth_fails_at_one` | **proved** |
| initial gap: `c < 13 ⟹ (3,4,5)` | `initial_gap` | **proved** (finite kernel-checked search) |
| bracketing at index `≥ 1` | `bracketB` | **proved** |
| `g = 1` ⟹ record minimum of `w` | `recordMinW_of_defect_one` | **proved** |
| record minimum of `w` ⟹ `g = 1` | `defect_one_of_recordMinW` | **proved** |
| **Stage C theorem (Δ maxima)** | `record_max_iff_boundary_defect_one` | **proved, unconditional** |
| **Stage C theorem (h minima)** | `record_min_h_iff_boundary_defect_one` | **proved, unconditional** |
| `(3,4,5)` is both min and max | `record_both_3_4_5` | **proved** |
| `(5,12,13)` max, not min | `recordMax_5_12_13`, `not_recordMin_5_12_13` | **proved** |
| `(20,21,29)` min, not max | `recordMin_not_max_20_21_29` | **proved** |
| **parametrization corollary** (optional item 7) | `boundary_param`, `defect_one_iff_param` | **proved** |
| **— deferred —** | | |
| every prime divisor of `d` is `≡ ±1 (mod 8)` | — | **deferred**, not needed (see below) |
| the ladder is *all* difference-one triples | — | **deferred**, not needed |
| `c_{j+1}/c_j < 3 + 2√2` | — | **deferred**, not needed (`< 6` suffices) |
| the boundary ladder is *all* defect-one triples | — | not needed for the theorem; **but proved anyway** as `defect_one_iff_param` |
| Pell enumeration completeness, counting asymptotics, envelope limits, majorization and entropy, elliptic transport, classification by algebraic degree | — | **deferred**, outside Stages A and C |

Nothing in the "deferred" rows is a hypothesis of any proved row. The gap lemma,
the ladder construction, unboundedness and bracketing are all discharged, so the
headline theorem is unconditional.

## Axiom audit

```
lake env lean axioms_check.lean
```

```
Stage A
'record_min_iff_leg_difference_one'      [propext, Classical.choice, Quot.sound]
'diff_one_of_record'                     [propext, Classical.choice, Quot.sound]
'record_of_diff_one'                     [propext, Classical.choice, Quot.sound]
'gap'                                    [propext, Classical.choice, Quot.sound]
'bracket'                                [propext, Classical.choice, Quot.sound]
'C_succ_lt_six_mul'                      [propext, Classical.choice, Quot.sound]
'ladder_adm'                             [propext, Classical.choice, Quot.sound]
'Adm.five_le_c'                          [propext, Classical.choice, Quot.sound]
'record_3_4_5'                           [propext, Classical.choice, Quot.sound]
'record_20_21_29'                        [propext, Classical.choice, Quot.sound]
'not_record_5_12_13'                     [propext, Classical.choice, Quot.sound]

Stage C -- headline
'record_max_iff_boundary_defect_one'     [propext, Classical.choice, Quot.sound]
'record_min_h_iff_boundary_defect_one'   [propext, Classical.choice, Quot.sound]
'recordMinW_iff_boundary_defect_one'     [propext, Classical.choice, Quot.sound]

Stage C -- supporting
'defect_one_of_recordMinW'               [propext, Classical.choice, Quot.sound]
'recordMinW_of_defect_one'               [propext, Classical.choice, Quot.sound]
'Adm.defect_gap'                         [propext, Classical.choice, Quot.sound]
'key_a_of_b'                             [propext, Classical.choice, Quot.sound]
'w_lt_iff_delta_gt'                      [propext, Classical.choice, Quot.sound]
'w_le_iff_delta_ge'                      [propext, Classical.choice, Quot.sound]
'h_lt_iff_delta_gt'                      [propext, Classical.choice, Quot.sound]
'recordMinW_iff_recordMax'               [propext, Classical.choice, Quot.sound]
'recordMinH_iff_recordMax'               [propext, Classical.choice, Quot.sound]
'badm'                                   [propext, Classical.choice, Quot.sound]
'BC_growth'                              [propext, Classical.choice, Quot.sound]
'initial_gap'                            [propext, Classical.choice, Quot.sound]
'bracketB'                               [propext, Classical.choice, Quot.sound]

Stage C -- examples and parametrization
'recordMax_3_4_5'                        [propext, Classical.choice, Quot.sound]
'recordMax_5_12_13'                      [propext, Classical.choice, Quot.sound]
'not_recordMax_20_21_29'                 [propext, Classical.choice, Quot.sound]
'recordMinH_5_12_13'                     [propext, Classical.choice, Quot.sound]
'boundary_param'                         [propext, Classical.choice, Quot.sound]
'defect_one_iff_param'                   [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard foundational axioms. **No `sorryAx`** (which is what a
`sorry` would introduce), no custom mathematical axiom, no `native_decide` and no
external oracle anywhere in the dependency chain.

The `decide` calls are all **kernel-checked** finite computations: `Gap.lean`
decides `2x² = y²` over `ZMod 3` (9 pairs) and `ZMod 5` (25 pairs); `Main.lean`
evaluates `Int.gcd` on literals; and `BoundaryMain.lean` uses one inside
`initial_gap` to refute `Int.gcd 6 8 = 1` in the single surviving branch of the
finite search. `decide` is reduced by the kernel, unlike `native_decide`,
which is why it is admissible here.

## Non-vacuity

`adm_3_4_5`, `adm_20_21_29` and `adm_5_12_13` exhibit inhabitants of `Adm`;
`record_3_4_5` and `record_20_21_29` exhibit inhabitants of `IsRecordMin`; and
`not_record_5_12_13` exhibits an admissible triple that is *not* a record. So
neither predicate is empty and neither is trivially true.

## Changes from the manuscript's proof

The theorem is the manuscript's Theorem 4.4 and the definition is its
Definition 4.1, unchanged. Three steps are proved differently, each time by
replacing a stronger result with the weakest one that suffices.

1. **The gap lemma avoids quadratic reciprocity.** Manuscript Lemma 4.2 proves
   that *every* prime divisor of `d` is `≡ ±1 (mod 8)`, via the second supplement
   to quadratic reciprocity, and deduces `d = 1 ∨ d ≥ 7`. Only the deduction is
   needed. Since `d` is odd, the sole values to exclude below `7` are `3` and `5`,
   and each falls to a finite residue check: if `p ∣ d` then `a ≡ b (mod p)`, so
   `c² ≡ 2a² (mod p)`, which in `ZMod 3` and `ZMod 5` forces `p ∣ a` and hence
   `p ∣ b`, contradicting `gcd(a,b) = 1`. This keeps the import surface to
   `Mathlib.NumberTheory.PythagoreanTriples` and avoids `Mathlib.NumberTheory.Pell`
   entirely. The stronger `±1 (mod 8)` statement is true and is simply not needed.

2. **The growth bound is cruder and purely polynomial.** Manuscript Lemma 4.3
   proves `c_{j+1}/c_j < 3 + 2√2` by a fixed-point argument on the second-order
   recurrence `c_{j+1} = 6c_j − c_{j−1}`. The theorem only needs a factor below
   `7`, so we prove `C (j+1) < 6 · C j` directly from the ladder invariant:
   `(3c)² − (4a+2)² = 2a² + 2a + 5 > 0`. No irrational constants, no second-order
   recurrence, no limiting ratio.

3. **The ladder is constructed, not classified.** The manuscript identifies the
   difference-one triples with the Pell spine (Proposition 3.2) and then uses the
   spine. We only need *some* unbounded, slowly growing family of difference-one
   triples, so we construct one by the first-order recurrence
   `a' = 3a + 2c + 1`, `c' = 4a + 3c + 2` from `(3,4,5)` and prove its invariant
   by induction. That the family is *exhaustive* — i.e. that it is all of the
   spine — is never used. Its hypotenuses are nonetheless
   `5, 29, 169, 985, …`, agreeing with `data/record_minima_c5e6.csv`.

   This construction is classical (the central stem of the Berggren–Barning tree;
   §4.1 of the revised manuscript), and no novelty is claimed for it.

A fourth, smaller difference: the manuscript establishes that a bracketing spine
element exists by observing that the smallest `d ≥ 7` triple is `(5,12,13)` and
`c₁ = 5 ≤ 13`. We instead prove `c ≥ 5` for *every* admissible triple
(`Adm.five_le_c`) and bracket from `C 0 = 5`, which avoids relying on a
particular minimal example.

### Stage C (boundary paper, Theorem 1.4)

The theorem and Definition 1.1 are the source's, unchanged. Two steps differ.

1. **Lemma 3.2 without square roots.** The source proves the order transfer
   analytically: `µ² = w(2−w)`, `h = µ√(1−µ²)`, `Δ = √(1−2h)`, then argues that
   each reparametrization is strictly monotone on an interval. We avoid
   irrational functions entirely. The whole mechanism is one integer lemma
   (`key_a_of_b`): since `(a₁c₂)² = c₁²c₂² − (b₁c₂)²`, a larger `b/c` forces a
   smaller `a/c`, by comparing the **squares** of the integer cross-products and
   then using positivity. The `h` transfer is the same move applied to
   `2ab·c'² = c²c'² − ((b−a)c')²`, which is the integer form of `Δ² = 1 − 2h`.
   Everything stays in `ℤ`.

2. **Lemma 3.3 is not needed in its stated form.** The source computes
   `g = min(s², 2n²)` from the Euclid parameters to conclude `g = 1 ∨ g ≥ 2`.
   Under the canonical ordering that conclusion is immediate: `c > b` because
   `c² = a² + b² > b²`, so `g = c − b` is a *positive integer*, and a positive
   integer is `1` or at least `2`. No parametrization is used. (The
   parametrization is proved separately, as the optional corollary, where it is
   actually about the shape of the family rather than about the gap.)

The one place Stage C needs **more** than Stage A is the growth bound. The Pell
ladder of Stage A satisfies `c_{j+1} < 6 c_j` uniformly, but the boundary ladder
satisfies `c_{n+1} ≤ 2 c_n` only for `n ≥ 2`: at `n = 1` it fails, `13 > 10`.
That failure is recorded as its own theorem (`BC_growth_fails_at_one`) rather
than skipped, and the gap it leaves is closed by `initial_gap`, which proves by
finite search that an admissible triple with `c < 13` must be `(3,4,5)` — whose
defect is `1`, so the `n = 1` branch cannot contain a counterexample.

## Cross-check against the repository data

`#eval` on the Lean ladder (kernel evaluation of the same `def` the proofs use)
reproduces `data/record_minima_c5e6.csv` exactly, for all eight recorded entries:

```
Lean  C j : [5, 29, 169, 985, 5741, 33461, 195025, 1136689]
CSV   c   :  5  29  169  985  5741  33461  195025  1136689
Lean  A j : [3, 20, 119, 696, 4059, 23660, 137903, 803760]
CSV   a   :  3  20  119  696  4059  23660  137903  803760
```

This is a consistency check between the formalization and the repository's
independent enumeration, not a step in the proof: the theorem is proved for all
triples and does not depend on any finite table.

## Stage C regression check (not a proof)

Independent enumeration over `c ≤ 5000` (792 primitive triples, exact `Fraction`
arithmetic) gives, for all three observables, record sets identical to the
explicit family `2n² + 2n + 1` — 49 entries, `5, 13, 25, 41, 61, …`:

```
record maxima of Δ  == explicit family : True
record minima of h  == explicit family : True
record minima of w  == explicit family : True
no primitive hypotenuse strictly between 5 and 13 : True
c_{n+1} <= 2 c_n for n >= 2 : True ; fails at n = 1 : True (13 > 10)
```

The same run reproduces Stage A's record minima as `5, 29, 169, 985`, all with
`b − a = 1`. This is a consistency check on the formalization, not a step in any
proof: both theorems are proved for all triples.

## Relationship to the Python suite

The Lean proof and the Python suite are independent and play different roles.
The Lean development proves the theorem for all triples; `src/` enumerates and
checks it over `c ≤ 5×10⁶`. Neither is evidence for the other. The suite was run
as a regression while this work was done: **36 passed**.
