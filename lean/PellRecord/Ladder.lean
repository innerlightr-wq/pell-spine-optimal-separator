/-
# Stage A, part 3: an unbounded ladder of difference-one triples.

We use the direct recurrence on sorted consecutive-leg triples (Option B of the
brief).  From `(a, a+1, c)` put

    a' = 3a + 2c + 1,    b' = a' + 1,    c' = 4a + 3c + 2.

Starting from `(3,4,5)` this produces `5, 29, 169, 985, 5741, …`, the hypotenuses
in `data/record_minima_c5e6.csv`.

Why this form rather than the shifted Euclid parameters: the invariant is a single
equation `a² + (a+1)² = c²`, and primitivity is free because consecutive integers
are coprime.  No parity or gcd side conditions have to be carried along.

We do **not** claim this ladder contains *every* difference-one triple; only that
it exists, grows, and grows slowly enough (`c' < 6c`) to close the gap of part 2.
-/
import PellRecord.Gap

namespace PellRecord

/-- One step of the ladder, on the pair `(a, c)`. -/
def step (p : ℤ × ℤ) : ℤ × ℤ := (3 * p.1 + 2 * p.2 + 1, 4 * p.1 + 3 * p.2 + 2)

/-- The ladder itself, seeded at `(3,5)`, i.e. the triple `(3,4,5)`. -/
def L : ℕ → ℤ × ℤ
  | 0 => (3, 5)
  | j + 1 => step (L j)

/-- Smaller leg of the `j`-th ladder triple. -/
def A (j : ℕ) : ℤ := (L j).1

/-- Hypotenuse of the `j`-th ladder triple. -/
def C (j : ℕ) : ℤ := (L j).2

@[simp] theorem A_zero : A 0 = 3 := rfl
@[simp] theorem C_zero : C 0 = 5 := rfl
@[simp] theorem A_succ (j : ℕ) : A (j + 1) = 3 * A j + 2 * C j + 1 := rfl
@[simp] theorem C_succ (j : ℕ) : C (j + 1) = 4 * A j + 3 * C j + 2 := rfl

/-- The ladder invariant: positivity and the Pythagorean identity with
consecutive legs.  Proved by induction; the identity step is the polynomial
identity `a'² + (a'+1)² - c'² = (a² + (a+1)²) - c²`. -/
theorem ladder_inv (j : ℕ) :
    3 ≤ A j ∧ 5 ≤ C j ∧ A j * A j + (A j + 1) * (A j + 1) = C j * C j := by
  induction j with
  | zero => refine ⟨by simp, by simp, by norm_num⟩
  | succ k ih =>
    obtain ⟨hA, hC, hid⟩ := ih
    refine ⟨by simp only [A_succ]; omega, by simp only [C_succ]; omega, ?_⟩
    simp only [A_succ, C_succ]
    linear_combination hid

theorem A_ge (j : ℕ) : 3 ≤ A j := (ladder_inv j).1
theorem C_ge_five (j : ℕ) : 5 ≤ C j := (ladder_inv j).2.1
theorem ladder_pyth (j : ℕ) :
    A j * A j + (A j + 1) * (A j + 1) = C j * C j := (ladder_inv j).2.2

/-- Every ladder entry is an admissible triple, with leg difference exactly `1`. -/
theorem ladder_adm (j : ℕ) : Adm (A j) (A j + 1) (C j) where
  apos := by have := A_ge j; omega
  altb := by omega
  cpos := by have := C_ge_five j; omega
  pyth := ladder_pyth j
  cop := Int.isCoprime_iff_gcd_eq_one.mp ⟨-1, 1, by ring⟩

@[simp] theorem ladder_diff (j : ℕ) : (A j + 1) - A j = 1 := by ring

/-- The ladder is strictly increasing. -/
theorem C_lt_C_succ (j : ℕ) : C j < C (j + 1) := by
  have hA := A_ge j
  have hC := C_ge_five j
  simp only [C_succ]; omega

/-- **The slow-growth bound.**  Consecutive ladder hypotenuses grow by a factor
below `6`.  This is where the gap `d ≥ 7` of part 2 is paid for: `6 < 7`. -/
theorem C_succ_lt_six_mul (j : ℕ) : C (j + 1) < 6 * C j := by
  have hA := A_ge j
  have hC := C_ge_five j
  have hid := ladder_pyth j
  simp only [C_succ]
  -- reduces to `4 * A j + 2 < 3 * C j`, i.e. `(3C)² - (4A+2)² = 2A² + 2A + 5 > 0`
  nlinarith [hid, hA, hC, sq_nonneg (A j), sq_nonneg (C j - A j)]

/-- The ladder is unbounded: `C j` grows at least linearly. -/
theorem C_ge_index (j : ℕ) : (j : ℤ) + 5 ≤ C j := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hA := A_ge k
    have hC := C_ge_five k
    simp only [C_succ]
    push_cast
    omega

/-- **Bracketing.**  Every admissible height is caught between two consecutive
ladder entries.  Proved from `C 0 = 5`, strict monotonicity and unboundedness. -/
theorem bracket (c : ℤ) (hc : 5 ≤ c) : ∃ j : ℕ, C j ≤ c ∧ c < C (j + 1) := by
  classical
  have hex : ∃ j : ℕ, c < C j := by
    refine ⟨c.toNat + 1, ?_⟩
    have h := C_ge_index (c.toNat + 1)
    have : (c.toNat : ℤ) = c := Int.toNat_of_nonneg (by omega)
    push_cast at h
    omega
  obtain ⟨j₀, hj₀, hmin⟩ := Nat.findX hex
  have hnz : j₀ ≠ 0 := by
    intro h
    rw [h] at hj₀
    simp only [C_zero] at hj₀
    omega
  obtain ⟨k, rfl⟩ : ∃ k, j₀ = k + 1 := ⟨j₀ - 1, by omega⟩
  refine ⟨k, ?_, hj₀⟩
  have := hmin k (by omega)
  omega

end PellRecord
