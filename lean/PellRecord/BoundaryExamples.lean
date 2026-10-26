/-
# Stage C, part 3: the two chronologies compared, and the parametrization.

The examples required by the brief, showing that the Stage A and Stage C record
classes are genuinely different — each contains a triple the other excludes.
-/
import PellRecord.BoundaryMain

namespace PellRecord

variable {a b c : ℤ}

/-! ## The two chronologies are different -/

/-- `(3,4,5)` is a record **maximum** of `Δ` (defect `c - b = 1`). -/
theorem recordMax_3_4_5 : IsRecordMax 3 4 5 :=
  (record_max_iff_boundary_defect_one adm_3_4_5).mpr (by norm_num)

/-- `(3,4,5)` is simultaneously a record minimum and a record maximum: it is the
first triple, so both conditions are vacuous below it. -/
theorem record_both_3_4_5 : IsRecordMin 3 4 5 ∧ IsRecordMax 3 4 5 :=
  ⟨record_3_4_5, recordMax_3_4_5⟩

/-- `(5,12,13)` is a record **maximum** but **not** a record minimum. -/
theorem recordMax_5_12_13 : IsRecordMax 5 12 13 :=
  (record_max_iff_boundary_defect_one adm_5_12_13).mpr (by norm_num)

theorem not_recordMin_5_12_13 : ¬ IsRecordMin 5 12 13 := not_record_5_12_13

/-- `(20,21,29)` is a record **minimum** but **not** a record maximum: its defect
is `29 - 21 = 8 ≠ 1`. -/
theorem not_recordMax_20_21_29 : ¬ IsRecordMax 20 21 29 := by
  intro hr
  have := (record_max_iff_boundary_defect_one adm_20_21_29).mp hr
  norm_num at this

theorem recordMin_not_max_20_21_29 : IsRecordMin 20 21 29 ∧ ¬ IsRecordMax 20 21 29 :=
  ⟨record_20_21_29, not_recordMax_20_21_29⟩

/-- The same triples, in the `h = ab/c²` formulation. -/
theorem recordMinH_5_12_13 : IsRecordMinH 5 12 13 :=
  (record_min_h_iff_boundary_defect_one adm_5_12_13).mpr (by norm_num)

/-- The first five boundary hypotenuses: the centered square numbers. -/
example : BC 1 = 5 ∧ BC 2 = 13 ∧ BC 3 = 25 ∧ BC 4 = 41 ∧ BC 5 = 61 := by
  refine ⟨by norm_num [BC], by norm_num [BC], ?_, ?_, ?_⟩ <;> norm_num [BC]

/-! ## Optional corollary: the explicit boundary family -/

/-- **Proposition 2.1(ii).**  A triple has defect `1` exactly when it is the
`n`-th member of the odd-leg family.

Forward: `a² = c² - b² = (c-b)(c+b) = 2b+1`, so `a` is odd; writing `a = 2n+1`
gives `b = 2n(n+1)` and `c = b+1`. -/
theorem boundary_param (h : Adm a b c) (hg : c - b = 1) :
    ∃ n : ℤ, 1 ≤ n ∧ a = 2 * n + 1 ∧ b = 2 * n * (n + 1) ∧ c = 2 * n * n + 2 * n + 1 := by
  have hcb : c = b + 1 := by omega
  -- a² = c² - b² = (c-b)(c+b) = 2b+1
  have ha2 : a * a = 2 * b + 1 := by
    linear_combination h.pyth + (c + b + 1) * hcb
  -- `a` is odd, since `a²` is
  have hodd : Odd a := by
    rcases Int.even_or_odd a with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := he
      have hdvd : (2 : ℤ) ∣ a * a := ⟨2 * k * k, by subst hk; ring⟩
      rw [ha2] at hdvd
      omega
    · exact ho
  obtain ⟨n, hn⟩ := hodd
  have h2b : 2 * b = 2 * (2 * n * (n + 1)) := by
    linear_combination -ha2 + (a + 2 * n + 1) * hn
  have hbval : b = 2 * n * (n + 1) := by linarith
  have hapos := h.apos
  have hn0 : 0 ≤ n := by omega
  have hn1 : 1 ≤ n := by
    rcases eq_or_lt_of_le hn0 with h0 | h0
    · exfalso
      have hab := h.altb
      rw [← h0] at hn hbval
      simp only [mul_zero, zero_add, mul_one] at hn hbval
      omega
    · omega
  exact ⟨n, hn1, hn, hbval, by linear_combination hcb + hbval⟩

/-- Converse: every member of the family is admissible with defect `1`. -/
theorem boundary_param_converse (n : ℕ) (hn : 1 ≤ n) :
    Adm (BA n) (BB n) (BC n) ∧ BC n - BB n = 1 :=
  ⟨badm n hn, BC_sub_BB n⟩

/-- Packaged both ways, for `n` ranging over the positive integers. -/
theorem defect_one_iff_param (h : Adm a b c) :
    c - b = 1 ↔
      ∃ n : ℤ, 1 ≤ n ∧ a = 2 * n + 1 ∧ b = 2 * n * (n + 1) ∧ c = 2 * n * n + 2 * n + 1 := by
  constructor
  · exact boundary_param h
  · rintro ⟨n, -, -, hb, hc⟩; subst hb; subst hc; ring

end PellRecord
