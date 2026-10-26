/-
# Stage A, part 1: admissible triples and the record-minimum predicate.

Everything is stated over `ℤ`, matching `Mathlib.NumberTheory.PythagoreanTriples`,
whose `PythagoreanTriple x y z` is by definition `x * x + y * y = z * z`.

Conventions follow the repository (and `AUDIT.md` §3): legs are ordered `a < b`,
and `a` is *not* required to be odd.  The separation is `d / c` with `d = b - a`;
it is never formed as a quotient, only compared by cross-multiplication.
-/
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace PellRecord

/-- A positive primitive Pythagorean triple with legs ordered `a < b`.

Note what is *not* assumed: nothing fixes the parity of `a`.  The smaller leg may
be either odd (as in `(3,4,5)`) or even (as in `(20,21,29)`). -/
structure Adm (a b c : ℤ) : Prop where
  apos : 0 < a
  altb : a < b
  cpos : 0 < c
  pyth : a * a + b * b = c * c
  cop  : Int.gcd a b = 1

namespace Adm

variable {a b c : ℤ}

theorem bpos (h : Adm a b c) : 0 < b := lt_trans h.apos h.altb

/-- The leg difference is positive. -/
theorem dpos (h : Adm a b c) : 0 < b - a := sub_pos.mpr h.altb

/-- The underlying mathlib Pythagorean triple. -/
theorem toPythagoreanTriple (h : Adm a b c) : PythagoreanTriple a b c := h.pyth

end Adm

/-- `T` is a **record minimum** of the separation `d/c = (b-a)/c`: strictly smaller
than every admissible triple of strictly smaller hypotenuse, and no larger than any
admissible triple of the *same* hypotenuse.

Both comparisons are exact cross-multiplications of `d/c` against `d'/c'`; since
`c, c' > 0` these are equivalent to the rational inequalities, and no division or
floating point is involved anywhere. -/
def IsRecordMin (a b c : ℤ) : Prop :=
  Adm a b c ∧
  (∀ a' b' c', Adm a' b' c' → c' < c → (b - a) * c' < (b' - a') * c) ∧
  (∀ a' b' c', Adm a' b' c' → c' = c → (b - a) * c' ≤ (b' - a') * c)

/-- The cross-multiplied comparison really is the comparison of the quotients.
This is the bridge demanded by the brief; nothing downstream uses it, because the
development works with the cross-multiplied form throughout. -/
theorem lt_div_iff_cross {d₁ c₁ d₂ c₂ : ℤ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    (d₁ : ℚ) / c₁ < (d₂ : ℚ) / c₂ ↔ d₁ * c₂ < d₂ * c₁ := by
  rw [div_lt_div_iff₀ (by exact_mod_cast h₁ : (0:ℚ) < c₁)
        (by exact_mod_cast h₂ : (0:ℚ) < c₂)]
  exact_mod_cast Iff.rfl

theorem le_div_iff_cross {d₁ c₁ d₂ c₂ : ℤ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    (d₁ : ℚ) / c₁ ≤ (d₂ : ℚ) / c₂ ↔ d₁ * c₂ ≤ d₂ * c₁ := by
  rw [div_le_div_iff₀ (by exact_mod_cast h₁ : (0:ℚ) < c₁)
        (by exact_mod_cast h₂ : (0:ℚ) < c₂)]
  exact_mod_cast Iff.rfl

/-- The smallest possible hypotenuse is `5`, attained by `(3,4,5)`. -/
theorem Adm.five_le_c {a b c : ℤ} (h : Adm a b c) : 5 ≤ c := by
  by_contra hcon
  have hlt : c < 5 := by omega
  have ha1 : 1 ≤ a := h.apos
  have hab : a < b := h.altb
  have hc1 : 1 ≤ c := h.cpos
  have hpy := h.pyth
  have hc4 : c ≤ 4 := by omega
  have hcc : c * c ≤ 16 := by nlinarith
  have hb4 : b ≤ 4 := by nlinarith
  have ha3 : a ≤ 3 := by omega
  have hb1 : 1 ≤ b := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega

end PellRecord
