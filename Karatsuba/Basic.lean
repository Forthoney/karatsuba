import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Karatsuba Multiplication Algorithm

This file implements the Karatsuba multiplication algorithm and proves its correctness.

The Karatsuba algorithm is a divide-and-conquer approach to multiply two numbers
that reduces the multiplication of two n-digit numbers to at most three multiplications
of n/2-digit numbers.
-/

abbrev Base := {n : ℕ // n > 1}

/-- Split a natural number into high and low parts given a base.
    For a number n and base b, returns (n / b, n % b) -/
@[inline]
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
        apply Nat.add_le_add_right
        apply Nat.le_mul_of_pos_right (n / i)
        omega
    _ = n := by simpa [Nat.mul_comm] using (Nat.div_add_mod n i)

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

section
variable (b : Base)

def karatsuba (x y : ℕ) : ℕ :=
  if hgrain: x ≤ b ∨ y ≤ b then
    x * y
  else
    let max_n := max x y
    let max_digits := Nat.log b max_n + 1
    let half_digits := max_digits / 2
    let pos : Base := ⟨(b : ℕ) ^ half_digits, by
      apply Nat.one_lt_pow
      · apply Nat.ne_of_gt
        dsimp [half_digits, max_digits]
        rw [Nat.div_pos_iff]
        constructor
        · exact Nat.zero_lt_two
        · simp only [Nat.reduceLeDiff]
          apply Nat.log_pos b.property
          omega
      · exact b.property
    ⟩
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
    have hsplit_le_max : pos ≤ max x y := by
      calc
        (b : ℕ) ^ half_digits ≤ (b : ℕ) ^ Nat.log b max_n := by
          apply Nat.pow_le_pow_right
          repeat omega
        _ ≤ max_n := by
          apply Nat.pow_log_le_self b
          apply Nat.ne_of_gt
          apply Nat.lt_trans
          · apply Nat.zero_lt_of_lt b.property
          · omega
        _ = max x y := rfl
  · calc x / pos + y / pos
      _ < x + y / pos := by
        apply Nat.add_lt_add_right
        apply Nat.div_lt_self
        repeat omega
      _ ≤ x + y := by
        apply Nat.add_le_add_left
        apply Nat.div_le_self
  · by_cases hxy : x ≤ y
    · calc x % pos + y % pos
        _ < x % pos + pos := by
          apply Nat.add_lt_add_left
          exact Nat.mod_lt y (Nat.zero_lt_of_lt pos.property)
        _ ≤ x % pos + y := by
          simpa [max_eq_right hxy] using hsplit_le_max
        _ ≤ x + y := by
          apply Nat.add_le_add_right
          exact Nat.mod_le x pos
    · calc x % pos + y % pos
        _ < pos + y % pos := by
          apply Nat.add_lt_add_right
          exact Nat.mod_lt x (Nat.zero_lt_of_lt pos.property)
        _ ≤ x + y % pos := by
          apply Nat.add_le_add_right
          simpa [max_eq_left (Nat.le_of_not_ge hxy)] using hsplit_le_max
        _ ≤ x + y := by
          apply Nat.add_le_add_left
          exact Nat.mod_le y pos
  · by_cases hxy : x ≤ y
    · calc
        (x / pos + x % pos) + (y / pos + y % pos)
            < (x / pos + x % pos) + y := by
              apply Nat.add_lt_add_left
              apply split_sum_decreasing y pos
              simpa [max_eq_right hxy] using hsplit_le_max
        _ ≤ x + y := by
              apply Nat.add_le_add_right
              exact split_sum_le x pos
    · calc
        (x / pos + x % pos) + (y / pos + y % pos)
            < x + (y / pos + y % pos) := by
              apply Nat.add_lt_add_right
              apply split_sum_decreasing x pos
              simpa [max_eq_left (Nat.le_of_not_ge hxy)] using hsplit_le_max
        _ ≤ x + y := by
              apply Nat.add_le_add_left
              exact split_sum_le y pos

theorem equiv_to_mult : ∀ x y, karatsuba b x y = x * y := by
  intro x y
  refine Nat.strong_induction_on (n := x + y)
    (p := fun n => ∀ x y, x + y = n → karatsuba (b := b) x y = x * y) ?_ x y rfl
  intro n ih x y hxy
  by_cases hgrain : x ≤ b ∨ y ≤ b
  · simp [karatsuba, hgrain]
  · let max_n : ℕ := max x y
    let max_digits : ℕ := Nat.log b max_n + 1
    let half_digits : ℕ := max_digits / 2
    let splitBase : Base := ⟨(b : ℕ) ^ half_digits, by
      have hmax_gt_b : (b : ℕ) < max_n := by
        omega
      have hlog_pos : 0 < Nat.log b max_n := by
        exact Nat.log_pos b.property (Nat.le_of_lt hmax_gt_b)
      have hhalf_pos : 0 < half_digits := by
        omega
      simpa using Nat.one_lt_pow (Nat.ne_of_gt hhalf_pos) b.property⟩
    let x1 : ℕ := x / splitBase
    let x0 : ℕ := x % splitBase
    let y1 : ℕ := y / splitBase
    let y0 : ℕ := y % splitBase
    rw [karatsuba]
    simp only [hgrain]
    simp [split, x1, x0, y1, y0]
    have hx_pos : 0 < x := by omega
    have hdivx : x / splitBase < x := by
      dsimp [x1]
      exact Nat.div_lt_self hx_pos splitBase.property
    have hz2_lt : x1 + y1 < n := by
      have hdivy : y1 ≤ y := by
        dsimp [y1]
        exact Nat.div_le_self y splitBase
      calc
        x1 + y1 < x + y1 := by simpa [x1] using Nat.add_lt_add_right hdivx y1
        _ ≤ x + y := Nat.add_le_add_left hdivy x
        _ = n := hxy
    have hsplit_le_max : (splitBase : ℕ) ≤ max x y := by
      have hmax_gt_b : (b : ℕ) < max_n := by
        omega
      have hhalf_le_log : half_digits ≤ Nat.log b max_n := by omega
      calc
        (b : ℕ) ^ half_digits ≤ (b : ℕ) ^ Nat.log b max_n := by
          exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt b.property) hhalf_le_log
        _ ≤ max_n := Nat.pow_log_le_self b (Nat.ne_of_gt (Nat.lt_trans (Nat.zero_lt_of_lt b.property) hmax_gt_b))
        _ = max x y := by rfl
    have hz0_lt : x0 + y0 < n := by
      by_cases hxy' : x ≤ y
      · have hy_ge : (splitBase : ℕ) ≤ y := by simpa [max_eq_right hxy'] using hsplit_le_max
        have hmodx : x0 ≤ x := by
          dsimp [x0]
          exact Nat.mod_le x splitBase
        have hmody : y0 < y := by
          dsimp [y0]
          calc
            y % splitBase < splitBase := Nat.mod_lt y (Nat.zero_lt_of_lt splitBase.property)
            _ ≤ y := hy_ge
        calc
          x0 + y0 < x0 + y := Nat.add_lt_add_left hmody _
          _ ≤ x + y := Nat.add_le_add_right hmodx _
          _ = n := hxy
      · have hx_ge : (splitBase : ℕ) ≤ x := by
          have hyx : y ≤ x := Nat.le_of_not_ge hxy'
          simpa [max_eq_left hyx] using hsplit_le_max
        have hmodx : x0 < x := by
          dsimp [x0]
          calc
            x % splitBase < splitBase := Nat.mod_lt x (Nat.zero_lt_of_lt splitBase.property)
            _ ≤ x := hx_ge
        have hmody : y0 ≤ y := by
          dsimp [y0]
          exact Nat.mod_le y splitBase
        calc
          x0 + y0 < x + y0 := Nat.add_lt_add_right hmodx _
          _ ≤ x + y := Nat.add_le_add_left hmody _
          _ = n := hxy
    have hz1_lt : (x1 + x0) + (y1 + y0) < n := by
      by_cases hxy' : x ≤ y
      · have hy_ge : (splitBase : ℕ) ≤ y := by simpa [max_eq_right hxy'] using hsplit_le_max
        have hsumx : x1 + x0 ≤ x := by
          dsimp [x1, x0]
          exact split_sum_le x splitBase
        have hsumy : y1 + y0 < y := by
          dsimp [y1, y0]
          exact split_sum_decreasing y splitBase hy_ge
        calc
          (x1 + x0) + (y1 + y0) < (x1 + x0) + y := Nat.add_lt_add_left hsumy _
          _ ≤ x + y := Nat.add_le_add_right hsumx _
          _ = n := hxy
      · have hx_ge : (splitBase : ℕ) ≤ x := by
          have hyx : y ≤ x := Nat.le_of_not_ge hxy'
          simpa [max_eq_left hyx] using hsplit_le_max
        have hsumx : x1 + x0 < x := by
          dsimp [x1, x0]
          exact split_sum_decreasing x splitBase hx_ge
        have hsumy : y1 + y0 ≤ y := by
          dsimp [y1, y0]
          exact split_sum_le y splitBase
        calc
          (x1 + x0) + (y1 + y0) < x + (y1 + y0) := Nat.add_lt_add_right hsumx _
          _ ≤ x + y := Nat.add_le_add_left hsumy _
          _ = n := hxy
    rw [ih (x / splitBase + y / splitBase) (by simpa [x1, y1] using hz2_lt) (x / splitBase) (y / splitBase) rfl]
    rw [ih (x % splitBase + y % splitBase) (by simpa [x0, y0] using hz0_lt) (x % splitBase) (y % splitBase) rfl]
    rw [ih
      ((x / splitBase + x % splitBase) + (y / splitBase + y % splitBase))
      (by simpa [x1, x0, y1, y0] using hz1_lt)
      (x / splitBase + x % splitBase)
      (y / splitBase + y % splitBase)
      rfl]
    let z2 : ℕ := x1 * y1
    let z0 : ℕ := x0 * y0
    let z1 : ℕ := (x1 + x0) * (y1 + y0) - z2 - z0
    calc  z2 * splitBase * splitBase + z1 * splitBase + z0
      _ = z2 * splitBase * splitBase + (((x1 + x0) * (y1 + y0) - z2 - z0)) * splitBase + z0 := rfl
      _ = z2 * splitBase * splitBase + (x1 * y0 + x0 * y1) * splitBase + z0 := by grind
      _ = (x1 * splitBase + x0) * (y1 * splitBase + y0) := by
        dsimp [z2, z0]
        ring
      _ = x * (y1 * splitBase + y0) := by
        dsimp [x1, x0]
        rw [Nat.mul_comm (x / splitBase) splitBase]
        rw [Nat.div_add_mod x splitBase]
      _ = x * y := by
        dsimp [y1, y0]
        rw [Nat.mul_comm (y / splitBase) splitBase]
        rw [Nat.div_add_mod y splitBase]

end
