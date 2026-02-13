import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Karatsuba Multiplication Algorithm

The Karatsuba algorithm is a divide-and-conquer approach to multiply two numbers
that reduces the multiplication of two n-digit numbers to at most three multiplications
of n/2-digit numbers.
-/

abbrev Base := {n : ℕ // n > 1}

def split (n : ℕ) (i : Base) : ℕ × ℕ :=
  (n / i, n % i)

lemma split_decreasing (n : ℕ) (i : Base) (hin : i ≤ n) :
  let (hi, lo) := split n i
  hi < n ∧ lo < n := by
  simp only [split]
  constructor
  · apply Nat.div_lt_self
    · omega
    · omega
  · have h_pos : 0 < i.val := Nat.zero_lt_of_lt i.property
    calc n % i
      _ < i := Nat.mod_lt n h_pos
      _ ≤ n := hin

lemma split_sum_le (n : ℕ) (i : Base) : n / i + n % i ≤ n := by
  calc
    n / i + n % i ≤ (n / i) * i + n % i := by
      simp only [add_le_add_iff_right]
      apply Nat.le_mul_of_pos_right (n / i)
      omega
    _ = n := Nat.div_add_mod' n i

lemma split_sum_decreasing (n : ℕ) (i : Base) (hin : i ≤ n) :
  n / i + n % i < n := by
  calc n / i + n % i
    _ < (n / i) * i + n % i := by
      apply Nat.add_lt_add_right
      apply lt_mul_of_one_lt_right
      · apply Nat.div_pos
        repeat omega
      · omega
    _ = n := Nat.div_add_mod' n i

lemma z2_lt (x y : ℕ) (pos : Base) (hx_pos : 0 < x) :
  x / pos + y / pos < x + y := by
  calc x / pos + y / pos
    _ < x + y / pos := by
      apply Nat.add_lt_add_right
      exact Nat.div_lt_self hx_pos pos.property
    _ ≤ x + y := by
      apply Nat.add_le_add_left
      exact Nat.div_le_self y pos

lemma z0_lt (x y : ℕ) (pos : Base) (hpos_le_max : (pos : ℕ) ≤ max x y) :
  x % pos + y % pos < x + y := by
  by_cases hxy : x ≤ y
  · calc x % pos + y % pos
      _ < x % pos + pos := by
        apply Nat.add_lt_add_left
        exact Nat.mod_lt y (Nat.zero_lt_of_lt pos.property)
      _ ≤ x % pos + y := by
        simpa [max_eq_right hxy] using hpos_le_max
      _ ≤ x + y := by
        apply Nat.add_le_add_right
        exact Nat.mod_le x pos
  · calc x % pos + y % pos
      _ < pos + y % pos := by
        apply Nat.add_lt_add_right
        exact Nat.mod_lt x (Nat.zero_lt_of_lt pos.property)
      _ ≤ x + y % pos := by
        apply Nat.add_le_add_right
        simpa [max_eq_left (Nat.le_of_not_ge hxy)] using hpos_le_max
      _ ≤ x + y := by
        apply Nat.add_le_add_left
        exact Nat.mod_le y pos

lemma z1_part_lt (x y : ℕ) (pos : Base) (hpos_le_max : pos ≤ max x y) :
  (x / pos + x % pos) + (y / pos + y % pos) < x + y := by
  by_cases hxy : x ≤ y
  · calc
      (x / pos + x % pos) + (y / pos + y % pos)
          < (x / pos + x % pos) + y := by
            apply Nat.add_lt_add_left
            apply split_sum_decreasing y pos
            simpa [max_eq_right hxy] using hpos_le_max
      _ ≤ x + y := by
            apply Nat.add_le_add_right
            exact split_sum_le x pos
  · calc
      (x / pos + x % pos) + (y / pos + y % pos)
          < x + (y / pos + y % pos) := by
            apply Nat.add_lt_add_right
            apply split_sum_decreasing x pos
            simpa [max_eq_left (Nat.le_of_not_ge hxy)] using hpos_le_max
      _ ≤ x + y := by
            apply Nat.add_le_add_left
            exact split_sum_le y pos

section
variable (b : Base)

def max_digits (x y : ℕ) : ℕ := Nat.log b (max x y) + 1

def half_digits (x y : ℕ) : ℕ := max_digits b x y / 2

def splitBase (x y : ℕ) (hgrain : ¬(x ≤ b ∨ y ≤ b)) : Base :=
  ⟨(b : ℕ) ^ half_digits b x y, by
    apply Nat.one_lt_pow
    · apply Nat.ne_of_gt
      dsimp [half_digits, max_digits, max]
      rw [Nat.div_pos_iff]
      constructor
      · exact Nat.zero_lt_two
      · simp only [Nat.reduceLeDiff]
        apply Nat.log_pos b.property
        omega
    · exact b.property
  ⟩

lemma splitBase_le_max (x y : ℕ) (hgrain : ¬(x ≤ b ∨ y ≤ b)) :
    (splitBase b x y hgrain : ℕ) ≤ max x y := by
  calc
    (b : ℕ) ^ half_digits b x y ≤ (b : ℕ) ^ Nat.log b (max x y) := by
      apply Nat.pow_le_pow_right
      · exact Nat.zero_lt_of_lt b.property
      · dsimp [half_digits, max_digits, max]
        omega
    _ ≤ max x y := by
      apply Nat.pow_log_le_self b
      apply Nat.ne_of_gt
      apply Nat.lt_trans
      · exact Nat.zero_lt_of_lt b.property
      · dsimp [max]
        omega

def karatsuba (x y : ℕ) : ℕ :=
  if hgrain: x ≤ b ∨ y ≤ b then
    x * y
  else
    let pos := splitBase b x y hgrain
    let sx := split x pos
    let sy := split y pos
    let z2 := karatsuba sx.1 sy.1
    let z0 := karatsuba sx.2 sy.2
    let z1_part := karatsuba (sx.1 + sx.2) (sy.1 + sy.2)
    let z1 := z1_part - z2 - z0
    z2 * pos * pos + z1 * pos + z0
termination_by x + y
decreasing_by
  all_goals
    have : pos ≤ max x y := splitBase_le_max b x y hgrain
  · exact z2_lt x y pos (by omega)
  · exact z0_lt x y pos this
  · exact z1_part_lt x y pos this

theorem equiv_to_mult : ∀ x y, karatsuba b x y = x * y := by
  intro x y
  refine Nat.strong_induction_on (n := x + y)
    (p := fun n ↦ ∀ x y, x + y ≤ n → karatsuba (b := b) x y = x * y) ?_
    x y le_rfl
  intro n ih x y hxy_le
  by_cases hgrain : x ≤ b ∨ y ≤ b
  · simp [karatsuba, hgrain]
  · let pos := splitBase b x y hgrain
    let x1 := x / pos
    let x0 := x % pos
    let y1 := y / pos
    let y0 := y % pos
    rw [karatsuba]
    simp only [hgrain, reduceDIte, split]
    have hsplit_le_max : (pos : ℕ) ≤ max x y := splitBase_le_max b x y hgrain
    rw [
      ih (x1 + y1)
        (Nat.lt_of_lt_of_le (z2_lt x y pos (by omega)) hxy_le)
        x1 y1 le_rfl,
      ih (x0 + y0)
        (Nat.lt_of_lt_of_le (z0_lt x y pos hsplit_le_max) hxy_le)
        x0 y0 le_rfl,
      ih ((x1 + x0) + (y1 + y0))
        (Nat.lt_of_lt_of_le (z1_part_lt x y pos hsplit_le_max) hxy_le)
        (x1 + x0) (y1 + y0) le_rfl
    ]
    let z2 := x1 * y1
    let z0 := x0 * y0
    let z1 := (x1 + x0) * (y1 + y0) - z2 - z0
    calc  z2 * pos * pos + z1 * pos + z0
      _ = z2 * pos * pos + (((x1 + x0) * (y1 + y0) - z2 - z0)) * pos + z0 := rfl
      _ = z2 * pos * pos + (x1 * y0 + x0 * y1) * pos + z0 := by grind
      _ = (x1 * pos + x0) * (y1 * pos + y0) := by
        dsimp [z2, z0]
        ring
      _ = x * (y1 * pos + y0) := by
        dsimp [x1, x0]
        rw [Nat.mul_comm (x / pos) pos]
        rw [Nat.div_add_mod x pos]
      _ = x * y := by
        dsimp [y1, y0]
        rw [Nat.mul_comm (y / pos) pos]
        rw [Nat.div_add_mod y pos]

end
