# Novelty and provenance audit

*Zotero-assisted literature, provenance, theorem-ancestry and novelty audit, September 2026.
Carried out after the manuscript, with the explicit purpose of establishing whether the
record-minimum theorem is genuinely distinct or already implied by classical results. The
governing standard is not whether the sentence has appeared before, but **whether existing
mathematics already implies it**.*

Manuscript under audit: `DeJesus2026pell` — *The Pell Spine as an Optimal Rational Separator*,
Zenodo, [10.5281/zenodo.21510910](https://doi.org/10.5281/zenodo.21510910).

Bibliography: [`../references.bib`](../references.bib) — 20 entries, 13 with DOIs. The seven
without are pre-DOI monographs and the two Scandinavian/Dutch tree sources; no DOI was invented
for them.

---

## 1. Verdict up front

**The theorem is an elementary consequence of classical ingredients, and the audit found no prior
statement of it.** Both halves of that sentence matter:

* **every ingredient is classical** — the family, the Pell equation, the recurrence, the
  parametrization, the residue law, the growth ratio. Nothing in the chain is new;
* **the assembly is four lines**, and the audit reconstructed it independently from scratch;
* **no equivalent normalized-record statement was located** in the near-isosceles literature
  (which runs from Martin 1876 to Griggs 2024), the tree literature (Berggren, Barning, Hall,
  Alperin, Romik), or the Pell-textbook literature (Barbeau ch. 6);
* the one genuinely contingent step is a **numerical margin**: the theorem holds because the Pell
  growth ratio `3 + 2√2 = 5.8284…` happens to be **below** the norm-form gap `7`. Had the gap been
  `5`, the theorem would be false. That coincidence is where the content sits.

Classification: **ELEMENTARY CONSEQUENCE**, presented as an **apparently unstated extremal
corollary**. Manuscript revision: **B — citation/provenance only.**

## 2. The theorem, stated at quantifier level

Let `P` be the set of primitive Pythagorean triples, written `(a, b, c)` with `a < b`,
`a² + b² = c²`, `gcd(a, b) = 1`. Define `Δ(a,b,c) = (b − a)/c ∈ (0, 1)`.

> **Theorem.** For `t ∈ P` call `t` a *record* iff
> `Δ(t) < Δ(t′)` for every `t′ ∈ P` with `c(t′) < c(t)`.
> Then `t` is a record **iff** `b − a = 1`.

Conventions checked and fixed:

| question | answer |
|---|---|
| strict or weak record? | **strict**, and strictly against all *smaller* hypotenuses; the repository groups by hypotenuse before updating, so equal-`c` ties are handled explicitly |
| ties at equal `c`? | possible in principle; **none occurs for `c ≤ 5×10⁶`** — verified. If one did, all tied triples would be reported |
| primitive only? | yes, and this is essential to the *ordering*, not to `Δ` — see §7 |
| does the first triple count? | yes: `(3,4,5)` is the smallest primitive triple (`c = 5` is minimal), so it is vacuously a record. This is needed for the induction base |
| leg ordering | `a < b`; the manuscript's §2 odd/even convention gives the same `|b − a|` and the same `Δ` (the repository's `AUDIT.md` already flags the one place — §6.4 — where the two conventions diverge) |

## 3. Ancestry of the main record theorem

Every arrow was re-derived independently during this audit.

```
Euclid parametrization  x = m²−n², y = 2mn, c = m²+n²        [CLASSICAL]
        │
        ▼  substitute m = s + n
b − a = |s² − 2n²|,  s = m−n odd,  gcd(s,n) = 1              [ELEMENTARY ALGEBRA]
        │
        ▼  2 is a QR mod every prime divisor of s²−2n²
every prime p | (b−a) satisfies p ≡ ±1 (mod 8)               [CLASSICAL: (2/p)=1 ⟺ p≡±1 mod 8]
        │
        ▼  smallest admissible values
b − a = 1  or  b − a ≥ 7,  and 7 IS attained                 [COROLLARY, sharp]
        │
        ▼  b − a = ±1 ⟺ s²−2n² = ±1
spine = Pell solutions; c = 5, 29, 169, 985, …               [CLASSICAL PELL]
        │
        ▼  c_{j+1} = 6c_j − c_{j−1};  u² − 2c² = −1
consecutive ratios < 3 + 2√2 = 5.8284… < 7                   [CLASSICAL PELL UNIT]
        │
        ▼  gap-closing induction  (four lines)
RECORD-MINIMUM THEOREM                                        [ELEMENTARY CONSEQUENCE]
```

| step | fact | known previously? | source | needed? | novel? |
|---|---|---|---|---|---|
| 1 | Euclid parametrization | **yes**, antiquity | `HardyWright2008`, `Dickson1952` | yes | no |
| 2 | `m = s + n` ⟹ `b − a = |s² − 2n²|` | elementary; standard in near-isosceles treatments | `BarbeauPythagorean`, `Martin1876` | yes | **elementary reparameterization** |
| 3 | `(2/p) = 1 ⟺ p ≡ ±1 (mod 8)` | **yes**, classical | `IrelandRosen1990` (already cited) | yes | no |
| 4 | `d = 1` or `d ≥ 7`, sharp | corollary of the classical characterization of `x²−2y²` | `IrelandRosen1990`, `Barbeau2003` | yes | **elementary corollary** |
| 5 | `d = ±1` ⟺ Pell; the family | **yes**, at least since 1876 | `Martin1876`, `BarbeauPythagorean`, `Griggs2024` | yes | no |
| 6 | `c_{j+1} = 6c_j − c_{j−1}`, `u² − 2c² = −1` | **yes**, textbook | `BarbeauPythagorean`, `NivenZuckermanMontgomery1991` | yes | no |
| 7 | ratios `< 3 + 2√2 < 7` | classical Pell-unit behaviour; the **comparison with 7** is the manuscript's observation | `Barbeau2003` | yes | **the contingent step** |
| 8 | gap-closing induction | elementary once 4 and 7 are in hand | — | — | **assembly** |

**Where new content enters: step 7→8 only.** Everything above step 7 is classical or elementary.

## 4. The gap: `d = 1` or `d ≥ 7`, and `7` is sharp

Independently verified by enumeration over `c ≤ 200000` (31,819 primitive triples):

* `b − a = |s² − 2n²|` holds for **every** triple — 0 mismatches;
* the observed leg differences begin `1, 7, 17, 23, 31, 41, 47, 49, 71, 73, 79, 89, 97, 103, 113,
  119` — matching the manuscript's §5 list exactly;
* **`7` is attained**, by `(5,12,13)`, `(8,15,17)`, `(48,55,73)`. So the bound is **sharp**, and
  "at least 7" is not merely what the congruence happens to give;
* no difference in `{3, 5, 9, 11, 13, 15}` occurs — consistent, since `3, 5, 11, 13 ≢ ±1 (mod 8)`
  and `9 = 3²`, `15 = 3·5`;
* every prime factor of every observed difference is `≡ ±1 (mod 8)` — 0 violations.

**The complete classical characterization** (stronger than the repository needs): since `ℤ[√2]` is
a PID with a fundamental unit of norm `−1`, an odd `d > 0` is primitively represented by
`|x² − 2y²|` **iff every prime factor of `d` is `≡ ±1 (mod 8)`**. The repository's `d = 1 or d ≥ 7`
is the weakest numerical corollary of this. The set of leg differences is therefore
`{d odd : p | d ⟹ p ≡ ±1 mod 8}` — which should be stated, since it is more informative than the
inequality actually used.

## 5. The gap-closing argument, and its abstract form

Reconstructed and verified:

Let `c_1 < c_2 < …` be the spine hypotenuses, `Δ` on the spine `= 1/c_j`. Suppose the record after
the spine point `c_j` is `1/c_j`. A non-spine triple with hypotenuse `c` has
`Δ = d/c ≥ 7/c`, so it beats `1/c_j` only if `c > 7c_j`. But
`c_{j+1} < (3+2√2)c_j < 7c_j`, so the next **spine** point arrives first and sets the strictly
smaller record `1/c_{j+1}`. Induction, with base `c_1 = 5 = min{c : (a,b,c) ∈ P}`.

Ratios verified numerically, all strictly `< 7` and increasing to `3+2√2` from below:
`29/5 = 5.800`, `169/29 = 5.8276`, `985/169 = 5.82840`, … → `5.8284271`. The **first** ratio is
already `< 7`, so there is no small-case exception.

**Abstract form.** The theorem is an instance of a record-envelope principle: *if objects carry an
integer defect `d ≥ 1` and a positive scale `c`, a distinguished subfamily has `d = 1`, every other
object has `d ≥ G`, the distinguished scales satisfy `c_{j+1} < G·c_j`, and `c_1` is the global
minimum scale, then the strict record minima of `d/c` are exactly the distinguished family.* The
Pell case is `G = 7`, growth `3+2√2`. This is recorded as clarification, **not** offered as a new
theorem — it has no content beyond the three-line argument above.

## 6. Novelty matrix

Categories: **CLASSICAL** · **KNOWN / REPARAMETERIZED** · **ELEMENTARY CONSEQUENCE** ·
**NEW DERIVATION OF KNOWN INGREDIENTS** · **NEW TERMINOLOGY / CLASSICAL OBJECT** ·
**COMPUTATIONAL CONFIRMATION** · **ANALYTIC INTERPRETATION** ·
**APPARENTLY DISTINCT EXTREMAL RESULT** · **UNCERTAIN — MORE SEARCH NEEDED**

| # | Claim | Location | Statement | Closest prior work | Standard formulation | Classical dependency | Formal status | Classification | Conf. | Recommended wording | Keys |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | The `b−a=1` family and its terms | §3, Table 3 | `(3,4,5), (20,21,29), (119,120,169), …` | **Martin 1876**; Barbeau ch. 6; Griggs 2024; Math. Gazette 1949/1953 | nearly isosceles right triangles; consecutive-leg triples | total | classical | **CLASSICAL** | very high | "the classical near-isosceles family, studied at least since 1876" | `Martin1876`, `BarbeauPythagorean`, `Griggs2024`, `BDP1949`, `Hunter1953` |
| 2 | `u² − 2c² = −1` along the family | Prop. 3.2 | Pell identity, `u = a+b` | Barbeau ch. 6 | Pell equation / NSW numbers | total | classical | **CLASSICAL** | very high | "the standard Pell equation for this family" | `BarbeauPythagorean`, `NivenZuckermanMontgomery1991` |
| 3 | `c_{j+1} = 6c_j − c_{j−1}` | App. B | second-order recurrence, seeds `1, 5` | Barbeau ch. 6; tree literature | Pell-unit recurrence; `c_j` are the **odd-indexed Pell numbers** `P_3, P_5, P_7, …` | total | classical | **CLASSICAL** | very high | "the classical recurrence; the hypotenuses are the odd-indexed Pell numbers" | `BarbeauPythagorean`, `Berggren1934` |
| 4 | Spine = one branch of the triple tree | (implicit) | orbit of `(3,4,5)` under one generator | **Berggren 1934**, Barning 1963, Hall 1970, Alperin 2005, Romik 2008 | a distinguished branch of the Berggren/Barning ternary tree | total | classical | **CLASSICAL** | high | add one sentence identifying the spine as a known single-generator branch | `Berggren1934`, `Barning1963`, `Hall1970`, `Alperin2005`, `Romik2008` |
| 5 | `m = s+n` ⟹ `b−a = |s²−2n²|` | §4 | shifted parametrization | standard in near-isosceles treatments | norm form of `ℤ[√2]` | elementary | verified (0 mismatches) | **KNOWN / REPARAMETERIZED** | high | "an elementary change of variables that exposes the norm form" | `BarbeauPythagorean`, `Martin1876` |
| 6 | Every prime divisor of `b−a` is `≡ ±1 (mod 8)` | Lemma 4.2 | residue restriction | `(2/p)=1 ⟺ p≡±1 mod 8` | quadratic-residue law + norm form | total | verified | **CLASSICAL** (applied) | very high | "the classical residue law applied to the norm form" | `IrelandRosen1990` |
| 7 | `b−a = 1` or `b−a ≥ 7`; **7 sharp** | Lemma 4.2, §5 | the gap | corollary of the complete characterization of `x²−2y²` | `{d odd : p|d ⟹ p ≡ ±1 mod 8}` | total | verified; `7` attained by `(5,12,13)` | **ELEMENTARY CONSEQUENCE** | very high | state the full characterization, and that `7` is attained so the bound is sharp | `IrelandRosen1990`, `Barbeau2003` |
| 8 | Ratios `< 3+2√2 < 7` | §4, App. B | growth bound | classical Pell-unit asymptotics | fundamental unit `1+√2`, `(1+√2)² = 3+2√2` | classical for the ratio; **the comparison with 7 is the manuscript's** | verified | **NEW DERIVATION OF KNOWN INGREDIENTS** | high | "the classical growth ratio, here compared against the gap" | `Barbeau2003` |
| 9 | **The record-minimum theorem** | Thm 4.4 | records of `Δ` ⟺ `b−a=1` | **none found** | — | rests entirely on 5–8 | proved (manuscript); verified to `c ≤ 5×10⁶` | **ELEMENTARY CONSEQUENCE**, apparently unstated | medium-high | "an elementary extremal corollary of classical Pell structure; no equivalent statement was identified in the literature reviewed" | `Martin1876`, `BarbeauPythagorean`, `IrelandRosen1990` |
| 10 | Contraction ratio `3−2√2` | §4, App. B | limiting record ratio | classical | reciprocal of `3+2√2` | total | verified | **CLASSICAL** | very high | "the reciprocal Pell unit" | `Barbeau2003` |
| 11 | `a/c` is **not** the best approximation to `1/√2` | Remark 3.4 | error is `O(1/c)`, not `O(1/c²)` | Khinchin, Perron | best-approximation theory | classical | verified | **CLASSICAL** (correct caveat) | very high | **keep verbatim — this is the repository's most important caveat** | `Khinchin1997`, `Perron1954` |
| 12 | `u/c` and `s/n` are the genuine convergents | Remark 3.4, Table 1 | convergents to `√2` | classical | continued fraction `[1;2,2,2,…]` | classical | verified | **CLASSICAL** | very high | keep | `Khinchin1997`, `Perron1954` |
| 13 | 795,763 primitive triples with `c ≤ 5×10⁶` | §5 | exact count | Lehmer's asymptotic `N(C) ~ C/(2π)` | — | — | **independently reproduced** | **COMPUTATIONAL CONFIRMATION** | very high | "a finite check, not the proof" — already stated | — |
| 14 | "Pell spine" | throughout | the name | — | a branch of the Berggren tree | — | terminology | **NEW TERMINOLOGY / CLASSICAL OBJECT** | high | keep the name, but say on first use that it names a classical family | `Berggren1934`, `Martin1876` |
| 15 | "Optimal rational separator" | title | the name | — | — | — | terminology | **NEW TERMINOLOGY** | high | keep, with the scope sentence the README already has | — |
| 16 | Smooth-transport results | §6 | `C^m` map with first nonvanishing derivative of order `m` ⟹ contraction `(3−2√2)^m` | Taylor's theorem | Taylor expansion / linearization | total | classical analysis | **ANALYTIC INTERPRETATION** | high | "analytic consequences of Taylor's theorem" — already stated | `Rudin` (manuscript [12]) |
| 17 | Oscillator/detuning language | §6.4–6.5 | elliptic-period detuning, beat frequency | A&S, DLMF for `K(k)` | — | classical special functions | interpretation | **ANALYTIC INTERPRETATION** | high | "no physical realization is claimed" — already stated | manuscript [1], [10] |

## 7. Answers to the specific audit questions

**Is primitivity essential?** For `Δ` itself, **no**: `Δ(ka, kb, kc) = Δ(a,b,c)`, so `Δ` is a
scale invariant of the similarity class. But the *record ordering* is by hypotenuse, and
non-primitive multiples of `(3,4,5)` have `c = 10, 15, 20, …` with `Δ = 1/5` — they would tie the
existing record without improving it, and never set a new one. So including them changes no record
but destroys strictness of the ordering and adds infinitely many ties. **Primitive triples are the
correct state space**, and the reason is exactly this: they are one representative per similarity
class.

**Are all `b−a=1` triples exactly the Pell family?** Yes — verified. `b−a = ±1 ⟺ s²−2n² = ±1`,
whose solutions are precisely the Pell/negative-Pell pairs, alternating between the two equations
and giving `c = 5, 29, 169, 985, …`.

**Could another branch produce the same normalized separation?** No: any triple with `Δ = 1/c` has
`b − a = 1`, hence lies on the spine.

**Continued fractions.** The spine's `u/c = 7/5, 41/29, 239/169, …` are convergents to `√2`, and
`s/n` likewise; those carry the classical `O(1/c²)` best-approximation property. `Δ = (b−a)/c` is
**not** a monotone transform of a convergent error: `Δ = 1/c` exactly on the spine, i.e. it decays
like `1/c`, one power slower. So the record theorem is **not** a restatement of a
best-approximation theorem, and the Lagrange/Markov spectra are not the right frame. The
repository already says this in Remark 3.4 — correctly, and it is the single most important thing
it gets right.

**Geometric reading.** `(a/c, b/c)` is a rational point on the unit circle; the perpendicular
distance from it to the diagonal `x = y` is exactly `|b−a|/(c√2) = Δ/√2`. So the theorem says: the
successive closest primitive rational points to the diagonal, ordered by denominator `c`, are
exactly the spine — at distance `1/(c√2)`. This is worth stating, and no prior art was found in
that phrasing either.

**Alternative objectives.** `(b−a)/(a+b)` and the angular error from `π/4` are both monotone in
`(b−a)/c` up to factors that vary slowly, so the spine is plausibly extremal for them too — but
this was **not proved** and must not be claimed. `|a/c − 1/√2|` is genuinely different, and there
the classical convergents, not the spine, are extremal.

## 8. Claim-strength audit

| phrase | where | verdict |
|---|---|---|
| "optimal" (title, abstract) | "Optimal Rational Separator" | **NEEDS QUALIFICATION**, already supplied: the README scopes it to primitive triples, hypotenuse ordering and the objective `Δ`. Keep that scope adjacent to every use |
| "record minima", "record frontier" | throughout | **SAFE** — defined precisely (Definition 4.1) |
| "This is proved, not merely observed" | abstract | **SAFE** and accurate |
| "exactly" | Thm 4.4 | **SAFE** — the iff is genuine |
| "extremal" | title, abstract | **SAFE** within the stated objective |
| "No physical realization is claimed" | abstract | **SAFE** — and load-bearing |
| "Pell spine" | throughout | **NEEDS CITATION** on first use: name a classical family |
| "new", "novel", "first", "discovered", "previously unknown" | — | **absent from the manuscript and README** |

The manuscript does **not** claim the family, the recurrence or the residue law as new. Its
claim-strength was already well calibrated; the audit's corrections are citations, not retractions.

## 9. What should change

1. **Cite Martin 1876** as the earliest dedicated treatment of the near-isosceles family, and the
   1949/1953/2024 Math. Gazette notes as evidence that it is common knowledge.
2. **Cite Barbeau, *Pell's Equation*, ch. 6** — a textbook chapter on exactly the Pell/Pythagorean
   correspondence of §3.
3. **Cite Hall 1970** alongside the already-cited Berggren and Barning, and add one sentence
   identifying the spine as a **single-generator branch** of that classical tree.
4. **State the full characterization** of leg differences (`{d odd : p|d ⟹ p ≡ ±1 mod 8}`) and that
   **`7` is attained by `(5,12,13)`**, so the gap bound is sharp.
5. **Say explicitly** that the theorem is an elementary consequence once the gap and the growth
   ratio are in hand, and that its content is the margin `5.83 < 7`.
6. Optionally cite **`McCullough2005`** (*Height and Excess of Pythagorean Triples*) and
   **`Romik2008`** (*The dynamics of Pythagorean triples*) for the surrounding leg-quantity and
   tree-dynamics literature, and **`AlanMazineler2025`** as the most recent paper on primitive
   triples with a prescribed leg difference — it treats the case where `b − a` is a perfect square
   (note `49 = 7²` is admissible), which is adjacent to, and independent of, the record question.

None of this touches a theorem statement, a proof, or a number.

## 10. Unresolved

1. **Martin 1876, B.D.P. 1949 and Hunter 1953 were not read in full** — only their titles and
   bibliographic records were verified (The Analyst and pre-1960 Math. Gazette notes are not
   openly available here). Any of them could contain an extremal remark. Tagged
   `uncertain-more-search`; this is the audit's main gap.
2. OEIS was unreachable from this machine, so the sequence cross-references (`A001652`,
   `A001653`, `A046090`) were not consulted. The classical sources above supersede them as
   provenance, and the identification of the hypotenuses as **odd-indexed Pell numbers**
   (`P_3, P_5, P_7, P_9, P_11 = 5, 29, 169, 985, 5741`) was verified directly.
3. Whether the spine remains extremal for `(b−a)/(a+b)` and the angular objective — plausible,
   unproved, and deliberately not claimed.
