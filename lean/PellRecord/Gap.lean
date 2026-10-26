/-
# Stage A, part 2: the arithmetic gap `d = 1 ∨ 7 ≤ d`.

The route is elementary and uses only finite residue checks:

* the legs of a primitive triple have opposite parity, so `d = b - a` is **odd**
  (this is `PythagoreanTriple.even_odd_of_coprime` from mathlib);
* if `p ∣ d` for `p ∈ {3, 5}` then `a ≡ b (mod p)`, hence `c² ≡ 2a² (mod p)`;
  the finitely many residues force `p ∣ a`, hence `p ∣ b`, contradicting `gcd(a,b)=1`.

So `d` is odd and divisible by neither `3` nor `5`; the only odd values below `7`
are `3` and `5`, both excluded.  Note this does *not* need the full classification
of prime divisors of `d` (every such prime is `±1 mod 8`); only `3` and `5` matter.
-/
import PellRecord.Basic

namespace PellRecord

variable {a b c : ℤ}

/-- The two finite residue checks, kernel-decided.  `ZMod 3` has `9` pairs to test
and `ZMod 5` has `25`; no `native_decide`, no oracle. -/
private theorem key_three : ∀ x y : ZMod 3, 2 * x * x = y * y → x = 0 := by decide

private theorem key_five : ∀ x y : ZMod 5, 2 * x * x = y * y → x = 0 := by decide

/-- If a prime-like modulus `p` divides the leg difference and the only solution of
`2x² = y²` in `ZMod p` has `x = 0`, then `p` divides both legs — impossible. -/
private theorem absurd_of_dvd_diff (h : Adm a b c) (p : ℕ) (hp2 : 2 ≤ p)
    (key : ∀ x y : ZMod p, 2 * x * x = y * y → x = 0)
    (hdvd : (p : ℤ) ∣ (b - a)) : False := by
  have hab : ((a : ℤ) : ZMod p) = ((b : ℤ) : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mpr hdvd
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) h.pyth
  push_cast at hcast
  rw [← hab] at hcast
  have hcc : 2 * ((a : ℤ) : ZMod p) * ((a : ℤ) : ZMod p)
      = ((c : ℤ) : ZMod p) * ((c : ℤ) : ZMod p) := by linear_combination hcast
  have ha0 : ((a : ℤ) : ZMod p) = 0 := key _ _ hcc
  have hpa : (p : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha0
  have hpb : (p : ℤ) ∣ b := by
    have hb : b = a + (b - a) := by ring
    rw [hb]; exact dvd_add hpa hdvd
  have hco : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr h.cop
  have hu : IsUnit ((p : ℤ)) := hco.isUnit_of_dvd' hpa hpb
  rw [Int.isUnit_iff] at hu
  omega

/-- The leg difference of a primitive triple is odd. -/
theorem odd_diff (h : Adm a b c) : (b - a) % 2 = 1 := by
  rcases h.toPythagoreanTriple.even_odd_of_coprime h.cop with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega

theorem not_three_dvd_diff (h : Adm a b c) : ¬ ((3 : ℤ) ∣ (b - a)) :=
  fun hd => absurd_of_dvd_diff h 3 (by norm_num) key_three (by exact_mod_cast hd)

theorem not_five_dvd_diff (h : Adm a b c) : ¬ ((5 : ℤ) ∣ (b - a)) :=
  fun hd => absurd_of_dvd_diff h 5 (by norm_num) key_five (by exact_mod_cast hd)

/-- The purely arithmetic core: a positive odd integer divisible by neither `3`
nor `5` is `1` or at least `7`, because the only other odd values below `7` are
`3` and `5`. -/
private theorem gap_arith {d : ℤ} (hpos : 0 < d) (h2 : d % 2 = 1)
    (h3 : d % 3 ≠ 0) (h5 : d % 5 ≠ 0) : d = 1 ∨ 7 ≤ d := by
  by_contra hcon
  have hne : d ≠ 1 := fun hh => hcon (Or.inl hh)
  have hlt : d < 7 := by
    by_contra hh
    exact hcon (Or.inr (by omega))
  interval_cases d <;> omega

/-- **The arithmetic gap.**  The leg difference of a positive primitive triple with
`a < b` is either `1` or at least `7`; the values `2,…,6` are all impossible. -/
theorem gap (h : Adm a b c) : b - a = 1 ∨ 7 ≤ b - a := by
  have hpos : 0 < b - a := h.dpos
  have h2 : (b - a) % 2 = 1 := odd_diff h
  -- restate the two non-divisibilities as remainders, which `omega` reasons about
  have h3 : (b - a) % 3 ≠ 0 := fun hh => not_three_dvd_diff h (Int.dvd_of_emod_eq_zero hh)
  have h5 : (b - a) % 5 ≠ 0 := fun hh => not_five_dvd_diff h (Int.dvd_of_emod_eq_zero hh)
  exact gap_arith hpos h2 h3 h5

end PellRecord
