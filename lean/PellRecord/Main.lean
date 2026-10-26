/-
# Stage A, part 4: the record-minimum theorem.

    An admissible triple is a chronological record minimum of `(b-a)/c`
    **if and only if** its leg difference is `1`.

Both directions are unconditional: the gap lemma, the ladder, its unboundedness
and the bracketing lemma are all *proved* in parts 2–3, not assumed here.
-/
import PellRecord.Ladder

namespace PellRecord

variable {a b c : ℤ}

/-- **Forward direction.**  A difference-one triple is a record.

At any strictly smaller height `c'` every admissible competitor has `d' ≥ 1`, so
`d'/c' ≥ 1/c' > 1/c`; at equal height `d'/c' ≥ 1/c`.  No property of the Pell
ladder is used — this holds for *every* admissible triple with `b - a = 1`. -/
theorem record_of_diff_one (h : Adm a b c) (hd : b - a = 1) : IsRecordMin a b c := by
  refine ⟨h, ?_, ?_⟩
  · intro a' b' c' h' hlt
    have hd' : 0 < b' - a' := h'.dpos
    have hcp : 0 < c := h.cpos
    rw [hd, one_mul]
    nlinarith
  · intro a' b' c' h' heq
    have hd' : 0 < b' - a' := h'.dpos
    have hcp : 0 < c := h.cpos
    rw [hd, one_mul, heq]
    nlinarith

/-- **Reverse direction.**  A record must have leg difference `1`.

If `d ≥ 7`, bracket the height as `C j ≤ c < C (j+1)`.  Since `C (j+1) < 6 C j`
and `6 < 7 ≤ d`, we get `c < d * C j`, i.e. the ladder triple at height `C j` has
separation `1 / C j < d / c`.  That contradicts the record condition — the strict
one if `C j < c`, the equal-height one if `C j = c`. -/
theorem diff_one_of_record (h : IsRecordMin a b c) : b - a = 1 := by
  obtain ⟨hadm, hstrict, hsame⟩ := h
  rcases gap hadm with h1 | h7
  · exact h1
  exfalso
  obtain ⟨j, hCj, hcC⟩ := bracket c hadm.five_le_c
  have hlad := ladder_adm j
  have h6 := C_succ_lt_six_mul j
  have hCpos : 0 < C j := by have := C_ge_five j; omega
  -- the ladder triple at height `C j` beats the candidate
  have hmul : 7 * C j ≤ (b - a) * C j := mul_le_mul_of_nonneg_right h7 hCpos.le
  have hkey : c < (b - a) * C j := by linarith
  rcases eq_or_lt_of_le hCj with heq | hlt
  · have hcmp := hsame (A j) (A j + 1) (C j) hlad heq
    rw [ladder_diff] at hcmp
    linarith
  · have hcmp := hstrict (A j) (A j + 1) (C j) hlad hlt
    rw [ladder_diff] at hcmp
    linarith

/-- **Stage A, the theorem.**  For positive primitive Pythagorean triples ordered
by hypotenuse, with legs written `a < b`, a triple is a chronological record
minimum of the normalized separation `(b - a)/c` **if and only if** `b - a = 1`. -/
theorem record_min_iff_leg_difference_one (h : Adm a b c) :
    IsRecordMin a b c ↔ b - a = 1 :=
  ⟨diff_one_of_record, record_of_diff_one h⟩

/-! ### The statement is not vacuous -/

theorem adm_3_4_5 : Adm 3 4 5 where
  apos := by norm_num
  altb := by norm_num
  cpos := by norm_num
  pyth := by norm_num
  cop := by decide

theorem adm_20_21_29 : Adm 20 21 29 where
  apos := by norm_num
  altb := by norm_num
  cpos := by norm_num
  pyth := by norm_num
  cop := by decide

theorem adm_5_12_13 : Adm 5 12 13 where
  apos := by norm_num
  altb := by norm_num
  cpos := by norm_num
  pyth := by norm_num
  cop := by decide

/-- `(3,4,5)` is a record minimum. -/
theorem record_3_4_5 : IsRecordMin 3 4 5 :=
  record_of_diff_one adm_3_4_5 (by norm_num)

/-- `(20,21,29)` is a record minimum. -/
theorem record_20_21_29 : IsRecordMin 20 21 29 :=
  record_of_diff_one adm_20_21_29 (by norm_num)

/-- `(5,12,13)` is **not** a record minimum: its leg difference is `7`.
This is the first admissible difference above `1`, and the triple is defeated by
`(3,4,5)`: `7/13 > 1/5`. -/
theorem not_record_5_12_13 : ¬ IsRecordMin 5 12 13 := by
  intro hrec
  have := diff_one_of_record hrec
  norm_num at this

/-- The ladder's first two entries are the first two records, as in
`data/record_minima_c5e6.csv`. -/
example : A 0 = 3 ∧ C 0 = 5 ∧ A 1 = 20 ∧ C 1 = 29 ∧ A 2 = 119 ∧ C 2 = 169 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> norm_num [A, C, L, step]

end PellRecord
