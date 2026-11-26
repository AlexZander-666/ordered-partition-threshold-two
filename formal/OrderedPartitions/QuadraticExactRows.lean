import OrderedPartitions.MarkedSeries

/-! A four-coefficient dynamic program for the original ordered partition rows. -/

open Finset Polynomial

namespace OrderedPartitions.QuadraticExact

/-- The first four coefficients, in increasing order of degree. -/
structure Coefficients where
  constant : ℕ
  linear : ℕ
  quadratic : ℕ
  cubic : ℕ
  deriving Repr, DecidableEq

def Coefficients.atDegree (c : Coefficients) : ℕ → ℕ
  | 0 => c.constant
  | 1 => c.linear
  | 2 => c.quadratic
  | 3 => c.cubic
  | _ => 0

def zeroRow : Coefficients := ⟨0, 0, 0, 0⟩
def initialRow : Coefficients := ⟨1, 0, 0, 0⟩

/-- Factorial division avoids an exponential Pascal-tree calculation in the kernel. -/
def binomial (n r : ℕ) : ℕ := n.factorial / (r.factorial * (n - r).factorial)

theorem binomial_eq {n r : ℕ} (hr : r ≤ n) : binomial n r = n.choose r :=
  (Nat.choose_eq_factorial_div_factorial hr).symm

/-- The table is stored with the newest row first. Entry `r - 1` leaves a final block of size `r`. -/
def stepCoeff (j n d : ℕ) (history : List Coefficients) : ℕ :=
  ∑ r ∈ Icc 1 n, binomial n r *
    (if j ≤ r then
      if d = 0 then 0 else (history[r-1]?.getD zeroRow).atDegree (d-1)
     else (history[r-1]?.getD zeroRow).atDegree d)

def step (j n : ℕ) (history : List Coefficients) : Coefficients :=
  ⟨stepCoeff j n 0 history, stepCoeff j n 1 history,
   stepCoeff j n 2 history, stepCoeff j n 3 history⟩

theorem step_atDegree (j n d : ℕ) (history : List Coefficients) (hd : d < 4) :
    (step j n history).atDegree d = stepCoeff j n d history := by
  interval_cases d <;> rfl

/-- All rows up to the given size, with the most recent row first. -/
def rows (j : ℕ) : ℕ → List Coefficients
  | 0 => [initialRow]
  | n+1 =>
    let history := rows j n
    step j (n+1) history :: history

private theorem initial_eq {j : ℕ} (hj : 1 ≤ j) {d : ℕ} (hd : d < 4) :
    initialRow.atDegree d = count 0 j d := by
  have h := coeff_row hj d (n := 0)
  rw [row_zero hj, coeff_one] at h
  apply Nat.cast_injective (R := ℝ)
  interval_cases d <;> simpa [initialRow, Coefficients.atDegree] using h

/-- Every available entry agrees with the original count of surjections. -/
theorem rows_eq {j : ℕ} (hj : 1 ≤ j) (n i d : ℕ) (hi : i ≤ n) (hd : d < 4) :
    ((rows j n)[i]?.getD zeroRow).atDegree d = count (n-i) j d := by
  induction n generalizing i d with
  | zero =>
    have : i = 0 := by omega
    subst i
    simpa [rows] using initial_eq hj hd
  | succ n ih =>
    cases i with
    | zero =>
      simp only [Nat.sub_zero, rows, List.getElem?_cons_zero, Option.getD_some]
      rw [step_atDegree _ _ _ _ hd, stepCoeff, count_recurrence n hj d]
      apply sum_congr rfl
      intro r hr
      have hsize := mem_Icc.mp hr
      have hindex : r-1 ≤ n := by omega
      have hsub : n-(r-1) = n+1-r := by omega
      rw [binomial_eq hsize.2]
      split_ifs with hlarge hzero
      · rfl
      · rw [ih (r-1) (d-1) hindex (by omega), hsub]
      · rw [ih (r-1) d hindex hd, hsub]
    | succ i =>
      have hi' : i ≤ n := by omega
      simpa only [rows, List.getElem?_cons_succ, Nat.succ_sub_succ_eq_sub] using ih i d hi' hd

/-- Compute the first four coefficients of the size-`n` row. -/
def coefficientRow (j n : ℕ) : Coefficients := (rows j n)[0]?.getD zeroRow

theorem coefficientRow_eq {j : ℕ} (hj : 1 ≤ j) (n d : ℕ) (hd : d < 4) :
    (coefficientRow j n).atDegree d = count n j d := by
  simpa [coefficientRow] using rows_eq hj n 0 d (Nat.zero_le n) hd

theorem original_coefficient {j : ℕ} (hj : 1 ≤ j) (n d : ℕ) (hd : d < 4) :
    (row n j).coeff d = ((coefficientRow j n).atDegree d : ℝ) := by
  rw [coeff_row hj, coefficientRow_eq hj n d hd]

/-- Read the four stored coefficients as a real polynomial. -/
noncomputable def Coefficients.polynomial (c : Coefficients) : ℝ[X] :=
  C (c.constant : ℝ) + C (c.linear : ℝ) * X +
    C (c.quadratic : ℝ) * X^2 + C (c.cubic : ℝ) * X^3

/-- Before a fourth large block can fit, the dynamic program returns the entire original row. -/
theorem original_row {j n : ℕ} (hj : 1 ≤ j) (hn : n < 4*j) :
    row n j = (coefficientRow j n).polynomial := by
  ext d
  by_cases hd : d < 4
  · rw [original_coefficient hj n d hd]
    interval_cases d <;> simp [Coefficients.polynomial, Coefficients.atDegree, coeff_X]
  · have hmul : 4*j ≤ d*j := Nat.mul_le_mul_right j (by omega)
    have hz : count n j d = 0 := count_above_degree hj (hn.trans_le hmul)
    have h0 : d ≠ 0 := by omega
    have h1 : d ≠ 1 := by omega
    have h2 : d ≠ 2 := by omega
    have h3 : d ≠ 3 := by omega
    simp [Coefficients.polynomial, coeff_row hj, coeff_X, hz, h0, Ne.symm h1, h2, h3]

#print axioms rows_eq
#print axioms original_coefficient
#print axioms original_row

end OrderedPartitions.QuadraticExact
