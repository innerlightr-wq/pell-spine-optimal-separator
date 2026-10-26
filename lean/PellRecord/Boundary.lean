/-
# Stage C: the boundary-record theorem.

Source: `record_density_pythagorean_quarter_circle (1).pdf`, Definition 1.1,
Theorem 1.4, Proposition 2.1(ii), Lemmas 3.2–3.4.

Under the canonical ordering `a < b` of Stage A, the paper's boundary defect
`g = c - max(a,b)` is `g = c - b`.  The theorem is

    the chronological record maxima of `Δ = (b-a)/c`, equivalently the record
    minima of `h = ab/c²`, are exactly the triples with `c - b = 1`.

Structure, following §3 of the source but with one deliberate change: the paper's
Lemma 3.2 passes through `µ = √(w(2-w))` and `h = µ√(1-µ²)`.  We avoid square
roots entirely.  The order transfer is done by comparing *squares* of integer
cross-products, which is exact and needs no analysis — see `key_a_of_b` below.
-/
import PellRecord.Main

namespace PellRecord

variable {a b c : ℤ}

/-! ## 1. The boundary defect -/

/-- The boundary defect `g = c - b` is a positive integer.  Hence `g = 1 ∨ 2 ≤ g`
with no arithmetic input at all — in contrast with Stage A, where the gap
`d = 1 ∨ 7 ≤ d` needed residue arguments. -/
theorem Adm.gpos (h : Adm a b c) : 0 < c - b := by
  have hb := h.bpos
  have ha := h.apos
  have hc := h.cpos
  nlinarith [h.pyth]

theorem Adm.defect_gap (h : Adm a b c) : c - b = 1 ∨ 2 ≤ c - b := by
  have := h.gpos; omega

/-! ## 2. The order mechanism, by exact integer comparison

`w = (c-b)/c`, `Δ = (b-a)/c` and `h = ab/c²` are compared only through
cross-multiplied integers.  Everything rests on one lemma. -/

/-- From `x² < y²` with both positive, `x < y`. -/
private theorem lt_of_sq_lt {x y : ℤ} (hx : 0 < x) (hy : 0 < y) (h : x * x < y * y) :
    x < y := by nlinarith

/-- From `x² = y²` with both positive, `x = y`. -/
private theorem eq_of_sq_eq {x y : ℤ} (hx : 0 < x) (hy : 0 < y) (h : x * x = y * y) :
    x = y := by
  have hfac : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h' <;> omega

/-- **The mechanism.**  A larger `b/c` forces a smaller `a/c`.

Proof: `(a₁c₂)² = c₁²c₂² - (b₁c₂)²` and `(a₂c₁)² = c₁²c₂² - (b₂c₁)²`, so
`b₂c₁ < b₁c₂` gives `(a₁c₂)² < (a₂c₁)²`, and both sides are positive.  No square
roots: the comparison is made between the squares themselves. -/
theorem key_a_of_b {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ} (h₁ : Adm a₁ b₁ c₁) (h₂ : Adm a₂ b₂ c₂)
    (hb : b₂ * c₁ < b₁ * c₂) : a₁ * c₂ < a₂ * c₁ := by
  have hp₁ := h₁.pyth
  have hp₂ := h₂.pyth
  have hb₂ : 0 < b₂ * c₁ := mul_pos h₂.bpos h₁.cpos
  have hsq : (b₂ * c₁) * (b₂ * c₁) < (b₁ * c₂) * (b₁ * c₂) :=
    mul_self_lt_mul_self hb₂.le hb
  exact lt_of_sq_lt (mul_pos h₁.apos h₂.cpos) (mul_pos h₂.apos h₁.cpos)
    (by nlinarith [hsq, hp₁, hp₂])

/-- The same at equality. -/
theorem key_a_of_b_eq {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ} (h₁ : Adm a₁ b₁ c₁) (h₂ : Adm a₂ b₂ c₂)
    (hb : b₂ * c₁ = b₁ * c₂) : a₁ * c₂ = a₂ * c₁ := by
  have hp₁ := h₁.pyth
  have hp₂ := h₂.pyth
  -- (a₁c₂)² - (a₂c₁)² = (b₂c₁)² - (b₁c₂)², which vanishes by `hb`
  exact eq_of_sq_eq (mul_pos h₁.apos h₂.cpos) (mul_pos h₂.apos h₁.cpos)
    (by linear_combination (c₂ * c₂) * hp₁ - (c₁ * c₁) * hp₂ + (b₂ * c₁ + b₁ * c₂) * hb)

/-- `w₁ < w₂` is literally `b₂c₁ < b₁c₂`: the defect comparison is a leg
comparison. -/
theorem w_lt_iff_b_gt {b₁ c₁ b₂ c₂ : ℤ} :
    (c₁ - b₁) * c₂ < (c₂ - b₂) * c₁ ↔ b₂ * c₁ < b₁ * c₂ := by
  rw [sub_mul, sub_mul, mul_comm c₂ c₁]
  constructor <;> intro h <;> linarith

theorem w_le_iff_b_ge {b₁ c₁ b₂ c₂ : ℤ} :
    (c₁ - b₁) * c₂ ≤ (c₂ - b₂) * c₁ ↔ b₂ * c₁ ≤ b₁ * c₂ := by
  rw [sub_mul, sub_mul, mul_comm c₂ c₁]
  constructor <;> intro h <;> linarith

private theorem delta_lt_of_b_lt {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ}
    (h₁ : Adm a₁ b₁ c₁) (h₂ : Adm a₂ b₂ c₂) (hb : b₂ * c₁ < b₁ * c₂) :
    (b₂ - a₂) * c₁ < (b₁ - a₁) * c₂ := by
  have ha := key_a_of_b h₁ h₂ hb
  have : b₂ * c₁ - a₂ * c₁ < b₁ * c₂ - a₁ * c₂ := by linarith
  linarith [this, sub_mul b₂ a₂ c₁, sub_mul b₁ a₁ c₂]

private theorem delta_eq_of_b_eq {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ}
    (h₁ : Adm a₁ b₁ c₁) (h₂ : Adm a₂ b₂ c₂) (hb : b₂ * c₁ = b₁ * c₂) :
    (b₂ - a₂) * c₁ = (b₁ - a₁) * c₂ := by
  have ha := key_a_of_b_eq h₁ h₂ hb
  linear_combination hb + ha

/-- **Order transfer, strict.**  Smaller defect ratio ⟺ larger separation. -/
theorem w_lt_iff_delta_gt {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ} (h₁ : Adm a₁ b₁ c₁) (h₂ : Adm a₂ b₂ c₂) :
    (c₁ - b₁) * c₂ < (c₂ - b₂) * c₁ ↔ (b₂ - a₂) * c₁ < (b₁ - a₁) * c₂ := by
  rw [w_lt_iff_b_gt]
  constructor
  · exact delta_lt_of_b_lt h₁ h₂
  · intro hd
    rcases lt_trichotomy (b₂ * c₁) (b₁ * c₂) with hlt | heq | hgt
    · exact hlt
    · exfalso; have := delta_eq_of_b_eq h₁ h₂ heq; linarith
    · exfalso; have := delta_lt_of_b_lt h₂ h₁ hgt; linarith

/-- **Order transfer, non-strict.** -/
theorem w_le_iff_delta_ge {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ} (h₁ : Adm a₁ b₁ c₁) (h₂ : Adm a₂ b₂ c₂) :
    (c₁ - b₁) * c₂ ≤ (c₂ - b₂) * c₁ ↔ (b₂ - a₂) * c₁ ≤ (b₁ - a₁) * c₂ := by
  rw [w_le_iff_b_ge]
  constructor
  · intro hb
    rcases eq_or_lt_of_le hb with heq | hlt
    · exact le_of_eq (delta_eq_of_b_eq h₁ h₂ heq)
    · exact le_of_lt (delta_lt_of_b_lt h₁ h₂ hlt)
  · intro hd
    by_contra hcon
    have hgt : b₁ * c₂ < b₂ * c₁ := not_le.mp hcon
    have := delta_lt_of_b_lt h₂ h₁ hgt
    linarith

/-- `Δ² = 1 - 2h` in cross-multiplied integer form: `h` reverses the order of `Δ`. -/
theorem h_lt_iff_delta_gt {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ} (h₁ : Adm a₁ b₁ c₁) (h₂ : Adm a₂ b₂ c₂) :
    a₁ * b₁ * (c₂ * c₂) < a₂ * b₂ * (c₁ * c₁) ↔ (b₂ - a₂) * c₁ < (b₁ - a₁) * c₂ := by
  have hp₁ := h₁.pyth
  have hp₂ := h₂.pyth
  have hd₁ : 0 < (b₁ - a₁) * c₂ := mul_pos h₁.dpos h₂.cpos
  have hd₂ : 0 < (b₂ - a₂) * c₁ := mul_pos h₂.dpos h₁.cpos
  constructor
  · intro hh
    exact lt_of_sq_lt hd₂ hd₁ (by nlinarith [hh, hp₁, hp₂])
  · intro hd
    have hsq := mul_self_lt_mul_self hd₂.le hd
    nlinarith [hsq, hp₁, hp₂]

theorem h_le_iff_delta_ge {a₁ b₁ c₁ a₂ b₂ c₂ : ℤ} (h₁ : Adm a₁ b₁ c₁) (h₂ : Adm a₂ b₂ c₂) :
    a₁ * b₁ * (c₂ * c₂) ≤ a₂ * b₂ * (c₁ * c₁) ↔ (b₂ - a₂) * c₁ ≤ (b₁ - a₁) * c₂ := by
  constructor
  · intro hh
    by_contra hcon
    have := (h_lt_iff_delta_gt h₂ h₁).mpr (not_le.mp hcon)
    linarith
  · intro hd
    by_contra hcon
    have := (h_lt_iff_delta_gt h₂ h₁).mp (not_le.mp hcon)
    linarith

/-! ## 3. The three record predicates -/

/-- Record **minimum** of the defect ratio `w = (c-b)/c`. -/
def IsRecordMinW (a b c : ℤ) : Prop :=
  Adm a b c ∧
  (∀ a' b' c', Adm a' b' c' → c' < c → (c - b) * c' < (c' - b') * c) ∧
  (∀ a' b' c', Adm a' b' c' → c' = c → (c - b) * c' ≤ (c' - b') * c)

/-- Record **maximum** of the separation `Δ = (b-a)/c`: Definition 1.1 with both
inequalities of `IsRecordMin` reversed. -/
def IsRecordMax (a b c : ℤ) : Prop :=
  Adm a b c ∧
  (∀ a' b' c', Adm a' b' c' → c' < c → (b' - a') * c < (b - a) * c') ∧
  (∀ a' b' c', Adm a' b' c' → c' = c → (b' - a') * c ≤ (b - a) * c')

/-- Record **minimum** of `h = ab/c²`. -/
def IsRecordMinH (a b c : ℤ) : Prop :=
  Adm a b c ∧
  (∀ a' b' c', Adm a' b' c' → c' < c → a * b * (c' * c') < a' * b' * (c * c)) ∧
  (∀ a' b' c', Adm a' b' c' → c' = c → a * b * (c' * c') ≤ a' * b' * (c * c))

/-- The three record classes coincide (the content of Lemma 3.2, without
square roots). -/
theorem recordMinW_iff_recordMax (h : Adm a b c) : IsRecordMinW a b c ↔ IsRecordMax a b c := by
  constructor
  · rintro ⟨-, hs, he⟩
    exact ⟨h, fun a' b' c' h' hlt => (w_lt_iff_delta_gt h h').mp (hs a' b' c' h' hlt),
      fun a' b' c' h' heq => (w_le_iff_delta_ge h h').mp (he a' b' c' h' heq)⟩
  · rintro ⟨-, hs, he⟩
    exact ⟨h, fun a' b' c' h' hlt => (w_lt_iff_delta_gt h h').mpr (hs a' b' c' h' hlt),
      fun a' b' c' h' heq => (w_le_iff_delta_ge h h').mpr (he a' b' c' h' heq)⟩

theorem recordMinH_iff_recordMax (h : Adm a b c) : IsRecordMinH a b c ↔ IsRecordMax a b c := by
  constructor
  · rintro ⟨-, hs, he⟩
    exact ⟨h, fun a' b' c' h' hlt => (h_lt_iff_delta_gt h h').mp (hs a' b' c' h' hlt),
      fun a' b' c' h' heq => (h_le_iff_delta_ge h h').mp (he a' b' c' h' heq)⟩
  · rintro ⟨-, hs, he⟩
    exact ⟨h, fun a' b' c' h' hlt => (h_lt_iff_delta_gt h h').mpr (hs a' b' c' h' hlt),
      fun a' b' c' h' heq => (h_le_iff_delta_ge h h').mpr (he a' b' c' h' heq)⟩

end PellRecord
