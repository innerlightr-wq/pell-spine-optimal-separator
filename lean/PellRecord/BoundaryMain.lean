/-
# Stage C, part 2: the boundary ladder and the boundary-record theorem.

Source: `record_density_pythagorean_quarter_circle (1).pdf`, Lemma 3.4 and the
proof of Theorem 1.4.

The ladder is the ancient odd-leg family (Prop. 2.1(ii) of the source, classical;
its hypotenuses are the centered square numbers, OEIS A001844):

    a_n = 2n+1,   b_n = 2n(n+1),   c_n = 2n² + 2n + 1     (n ≥ 1).

Two features differ from the Pell ladder of Stage A and both matter:

* the growth bound `c_{n+1} ≤ 2 c_n` holds only for `n ≥ 2`; **it fails at n = 1**
  (`c₂ = 13 > 10 = 2c₁`).  That exception is not hidden — it is discharged by
  the initial-gap lemma, which is the extra ingredient this stage needs;
* the defect gap is only a factor of `2` (`g = 1 ∨ g ≥ 2`), but it is free:
  `g = c - b` is a positive integer, with no residue argument at all.
-/
import PellRecord.Boundary

namespace PellRecord

variable {a b c : ℤ}

theorem Adm.blt (h : Adm a b c) : b < c := by have := h.gpos; omega

/-! ## The boundary ladder -/

/-- Smaller leg of the `n`-th boundary triple (`n ≥ 1`). -/
def BA (n : ℕ) : ℤ := 2 * (n : ℤ) + 1
/-- Larger leg. -/
def BB (n : ℕ) : ℤ := 2 * (n : ℤ) * ((n : ℤ) + 1)
/-- Hypotenuse: the centered square numbers `1, 5, 13, 25, 41, …`. -/
def BC (n : ℕ) : ℤ := 2 * (n : ℤ) * (n : ℤ) + 2 * (n : ℤ) + 1

@[simp] theorem BC_one : BC 1 = 5 := by norm_num [BC]
@[simp] theorem BC_two : BC 2 = 13 := by norm_num [BC]
@[simp] theorem BC_zero : BC 0 = 1 := by norm_num [BC]

/-- The defining property: the boundary defect is exactly `1`. -/
@[simp] theorem BC_sub_BB (n : ℕ) : BC n - BB n = 1 := by simp only [BC, BB]; ring

theorem BC_nonneg (n : ℕ) : 0 < BC n := by
  have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  simp only [BC]; nlinarith

/-- Every ladder entry is admissible. -/
theorem badm (n : ℕ) (hn : 1 ≤ n) : Adm (BA n) (BB n) (BC n) where
  apos := by have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n; simp only [BA]; omega
  altb := by
    have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    simp only [BA, BB]; nlinarith
  cpos := BC_nonneg n
  pyth := by simp only [BA, BB, BC]; ring
  -- `(2n+1)² - 2·2n(n+1) = 1`, so the legs are coprime with explicit cofactors
  cop := Int.isCoprime_iff_gcd_eq_one.mp ⟨2 * (n : ℤ) + 1, -2, by simp only [BA, BB]; ring⟩

theorem BC_strict_mono (n : ℕ) : BC n < BC (n + 1) := by
  have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  simp only [BC]; push_cast; nlinarith

/-- **Lemma 3.4(i).**  `c_{n+1} ≤ 2 c_n` for `n ≥ 2` — and only for `n ≥ 2`. -/
theorem BC_growth (n : ℕ) (hn : 2 ≤ n) : BC (n + 1) ≤ 2 * BC n := by
  have h2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  simp only [BC]; push_cast; nlinarith

/-- The exception at `n = 1`, recorded explicitly rather than hidden. -/
theorem BC_growth_fails_at_one : ¬ (BC 2 ≤ 2 * BC 1) := by norm_num

theorem BC_ge_index (n : ℕ) : (n : ℤ) + 1 ≤ BC n := by
  have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  simp only [BC]; nlinarith

/-- **Lemma 3.4(ii), the initial gap.**  There is no primitive triple with
hypotenuse strictly between `5` and `13`; equivalently an admissible triple with
`c < 13` is `(3,4,5)`.

Proved by a genuine finite search over the region forced by `5 ≤ c < 13`,
`a < b < c`, kernel-checked — not by a lookup table. -/
theorem initial_gap (h : Adm a b c) (hc : c < 13) : a = 3 ∧ b = 4 ∧ c = 5 := by
  have h5 := h.five_le_c
  have hbc := h.blt
  have hab := h.altb
  have ha1 := h.apos
  have hpy := h.pyth
  have hcop := h.cop
  have hb12 : b ≤ 12 := by omega
  have ha11 : a ≤ 11 := by omega
  have hb2 : 2 ≤ b := by omega
  have ha1' : 1 ≤ a := h.apos
  interval_cases c <;> interval_cases b <;> interval_cases a <;>
    first
      | omega
      | (exfalso; revert hcop; decide)

/-- **Bracketing.**  Every admissible height sits between consecutive ladder
entries, at an index `≥ 1`. -/
theorem bracketB (c : ℤ) (hc : 5 ≤ c) :
    ∃ n : ℕ, 1 ≤ n ∧ BC n ≤ c ∧ c < BC (n + 1) := by
  classical
  have hex : ∃ n : ℕ, c < BC n := by
    refine ⟨c.toNat + 1, ?_⟩
    have h := BC_ge_index (c.toNat + 1)
    have ht : (c.toNat : ℤ) = c := Int.toNat_of_nonneg (by omega)
    push_cast at h
    omega
  obtain ⟨n₀, hn₀, hmin⟩ := Nat.findX hex
  -- `n₀ ≥ 2`, because `BC 0 = 1 ≤ c` and `BC 1 = 5 ≤ c`
  have h1 : ¬ (c < BC 1) := by simp only [BC_one]; omega
  have hge : 2 ≤ n₀ := by
    by_contra hcon
    interval_cases n₀
    · simp only [BC_zero] at hn₀; omega
    · exact h1 hn₀
  obtain ⟨k, rfl⟩ : ∃ k, n₀ = k + 1 := ⟨n₀ - 1, by omega⟩
  exact ⟨k, by omega, by have := hmin k (by omega); omega, hn₀⟩

/-! ## The boundary-record theorem -/

/-- **Forward.**  Defect `1` ⟹ record minimum of `w`.  Identical in shape to the
Stage A forward direction: at a smaller height `g' ≥ 1` gives `g'/c' > 1/c`. -/
theorem recordMinW_of_defect_one (h : Adm a b c) (hg : c - b = 1) : IsRecordMinW a b c := by
  refine ⟨h, ?_, ?_⟩
  · intro a' b' c' h' hlt
    have hg' : 0 < c' - b' := h'.gpos
    have hcp : 0 < c := h.cpos
    rw [hg, one_mul]
    nlinarith
  · intro a' b' c' h' heq
    have hg' : 0 < c' - b' := h'.gpos
    have hcp : 0 < c := h.cpos
    rw [hg, one_mul, heq]
    nlinarith

/-- **Reverse.**  A record minimum of `w` has defect `1`.

For `g ≥ 2` bracket `BC n ≤ c < BC (n+1)`.  If `n ≥ 2` then
`c < BC (n+1) ≤ 2·BC n ≤ g·BC n`.  If `n = 1` then `5 ≤ c < 13`, so the triple is
`(3,4,5)` by the initial gap — which has defect `1`, contradicting `g ≥ 2`. -/
theorem defect_one_of_recordMinW (h : IsRecordMinW a b c) : c - b = 1 := by
  obtain ⟨hadm, hstrict, hsame⟩ := h
  rcases hadm.defect_gap with h1 | h2
  · exact h1
  exfalso
  obtain ⟨n, hn1, hCn, hcC⟩ := bracketB c hadm.five_le_c
  have hladm := badm n hn1
  have hCpos := BC_nonneg n
  -- the ladder triple at height `BC n` has strictly smaller `w`
  have hkey : c < (c - b) * BC n := by
    rcases Nat.lt_or_ge n 2 with hlt2 | hge2
    · -- n = 1 : the initial gap forces (3,4,5), whose defect is 1
      exfalso
      have hn : n = 1 := by omega
      subst hn
      have : c < 13 := by simpa using hcC
      obtain ⟨-, hb, hcv⟩ := initial_gap hadm this
      omega
    · have hgrow := BC_growth n hge2
      have : 2 * BC n ≤ (c - b) * BC n := by nlinarith
      linarith
  rcases eq_or_lt_of_le hCn with heq | hlt
  · have hcmp := hsame (BA n) (BB n) (BC n) hladm heq
    rw [BC_sub_BB] at hcmp
    linarith
  · have hcmp := hstrict (BA n) (BB n) (BC n) hladm hlt
    rw [BC_sub_BB] at hcmp
    linarith

/-- **The boundary-record theorem** (source Theorem 1.4), in the `w` formulation. -/
theorem recordMinW_iff_boundary_defect_one (h : Adm a b c) :
    IsRecordMinW a b c ↔ c - b = 1 :=
  ⟨defect_one_of_recordMinW, recordMinW_of_defect_one h⟩

/-- **The boundary-record theorem** (source Theorem 1.4), for record maxima of
`Δ = (b-a)/c`. -/
theorem record_max_iff_boundary_defect_one (h : Adm a b c) :
    IsRecordMax a b c ↔ c - b = 1 :=
  (recordMinW_iff_recordMax h).symm.trans (recordMinW_iff_boundary_defect_one h)

/-- **The boundary-record theorem**, for record minima of `h = ab/c²`. -/
theorem record_min_h_iff_boundary_defect_one (h : Adm a b c) :
    IsRecordMinH a b c ↔ c - b = 1 :=
  (recordMinH_iff_recordMax h).trans (record_max_iff_boundary_defect_one h)

end PellRecord
