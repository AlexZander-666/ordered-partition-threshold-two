import OrderedPartitions.FirstJump
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial Finset
namespace OrderedPartitions

/-- The true probability-free ordinary row: each ordered partition enters its degree once. -/
def row (n j : ℕ) : ℝ[X] :=
  ∑ d ∈ range (n+1), C (count n j d : ℝ) * X^d

theorem coeff_row {n j : ℕ} (hj : 1 ≤ j) (d : ℕ) :
    (row n j).coeff d = (count n j d : ℝ) := by
  by_cases hd : d ≤ n
  · simp [row, finsetSum_coeff, sum_ite_eq, hd]
  · have hzero : count n j d = 0 := count_above_degree hj (by
      have h := Nat.le_mul_of_pos_right d (by omega : 0 < j)
      omega)
    simp [row, finsetSum_coeff, sum_ite_eq, hd, hzero]

theorem row_linear {n j : ℕ} (hj : 2 ≤ j) (hn : n < 2*j) :
    row n j = C (count n j 0 : ℝ) + C (count n j 1 : ℝ)*X := by
  ext d
  rcases d with _ | _ | d
  · simp [coeff_row (by omega : 1≤j)]
  · simp [coeff_row (by omega : 1≤j)]
  · have hzero : count n j (d+1+1) = 0 := count_above_degree (by omega)
      (lt_of_lt_of_le hn (Nat.mul_le_mul_right j (by omega)))
    simp [coeff_row (by omega : 1≤j), hzero]

theorem row_first_jump {j : ℕ} (hj : 2 ≤ j) :
    row (2*j) j = C (count (2*j) j 0 : ℝ) + C (count (2*j) j 1 : ℝ)*X
      + C (((2*j).choose j : ℕ) : ℝ)*X^2 := by
  ext d
  by_cases hd0 : d=0
  · subst d
    simp [coeff_row (by omega : 1≤j)]
  by_cases hd1 : d=1
  · subst d
    simp [coeff_row (by omega : 1≤j)]
  by_cases hd2 : d=2
  · subst d
    simp [coeff_row (by omega : 1≤j), first_jump_count (by omega : 1≤j)]
  have hzero : count (2*j) j d = 0 :=
    count_above_degree (by omega) (Nat.mul_lt_mul_of_pos_right (by omega) (by omega))
  simp [coeff_row (by omega : 1≤j), coeff_X, hzero, hd0, hd2, Ne.symm hd1]

#print axioms coeff_row
#print axioms row_linear
#print axioms row_first_jump

end OrderedPartitions
