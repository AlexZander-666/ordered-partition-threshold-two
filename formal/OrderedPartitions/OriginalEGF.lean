import OrderedPartitions.MarkedSeries
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse

noncomputable section
open Finset Polynomial
namespace OrderedPartitions

theorem all_sizes_eq_exp : sizeSeries 1 = PowerSeries.exp ℝ - 1 := by
  ext n
  rw [map_sub, PowerSeries.coeff_exp]
  cases n <;> simp [sizeSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]

theorem free_series {j : ℕ} (hj : 1 ≤ j) :
    momentSeries j 0 = (2 - PowerSeries.exp ℝ)⁻¹ := by
  have hden : (1-sizeSeries 1) = 2-PowerSeries.exp ℝ := by rw [all_sizes_eq_exp]; ring
  have hc : PowerSeries.constantCoeff (2-PowerSeries.exp ℝ) ≠ 0 := by
    rw [← hden, map_sub]; simp [sizeSeries]
  apply Eq.symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one hc).mpr
  simpa [← hden, mul_comm] using free_resolvent hj

theorem moment_coefficient {j : ℕ} (hj : 1 ≤ j) (n h : ℕ) :
    (∑ d ∈ range (n+1), (count n j d : ℝ) * (d.choose h : ℝ)) / n.factorial =
    PowerSeries.coeff n (sizeSeries j ^ h * ((2-PowerSeries.exp ℝ)⁻¹)^(h+1)) := by
  rw [← markedCount_eq_count, ← free_series hj, ← marked_segments hj]
  simp [momentSeries]

/-- The EGF obtained by evaluating each true original row at a fixed real mark. -/
def originalEGF (j : ℕ) (t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n ↦ (row n j).eval t / n.factorial)

private def markedSizes (j : ℕ) (t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun r ↦ if r=0 then 0 else
    (r.factorial : ℝ)⁻¹ * t^(if j ≤ r then 1 else 0))

private theorem block_coeff (j N : ℕ) (t : ℝ) (S : PowerSeries ℝ) :
    PowerSeries.coeff N (markedSizes j t * S) =
      ∑ r ∈ Icc 1 N, (r.factorial : ℝ)⁻¹ * t^(if j ≤ r then 1 else 0) *
        PowerSeries.coeff (N-r) S := by
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [markedSizes, PowerSeries.coeff_mk]
  symm
  apply sum_subset_zero_on_sdiff
  · intro r hr
    simpa only [mem_range, Nat.lt_succ_iff] using (mem_Icc.mp hr).2
  · intro r hr
    obtain ⟨hr,hn⟩ := mem_sdiff.mp hr
    have hN := Nat.le_of_lt_succ (mem_range.mp hr)
    have : r=0 := by by_contra! h; exact hn (mem_Icc.mpr ⟨by omega,hN⟩)
    simp [this]
  · intro r hr
    have h := (mem_Icc.mp hr).1
    simp [show r ≠ 0 by omega]

private theorem denominator_split {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    markedSizes j t = sizeSeries 1 + PowerSeries.C (t-1) * sizeSeries j := by
  ext r
  rw [map_add, PowerSeries.coeff_C_mul]
  simp only [markedSizes, sizeSeries, PowerSeries.coeff_mk]
  by_cases hr : r=0
  · simp [hr, show ¬j ≤ 0 by omega]
  · by_cases h : j ≤ r
    · simp [hr, show 1≤r by omega, h]; ring
    · simp [hr, show 1≤r by omega, h]

/-- The original row EGF equals 1/(1-small(z)-t*large(z)). -/
theorem original_egf {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    originalEGF j t = (2-PowerSeries.exp ℝ-PowerSeries.C (t-1)*sizeSeries j)⁻¹ := by
  have den : 1-markedSizes j t = 2-PowerSeries.exp ℝ-PowerSeries.C (t-1)*sizeSeries j := by
    rw [denominator_split hj, all_sizes_eq_exp]; ring
  rw [← den]
  symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one (show
    PowerSeries.constantCoeff (1-markedSizes j t) ≠ 0 by simp [markedSizes])).mpr
  rw [mul_comm, sub_mul, one_mul]
  ext n
  rw [map_sub, block_coeff]
  cases n with
  | zero => simp [originalEGF, row_zero hj]
  | succ n =>
    simp only [originalEGF, PowerSeries.coeff_mk, PowerSeries.coeff_one, Nat.succ_ne_zero,
      if_false, sub_eq_zero]
    rw [row_recurrence n hj, eval_finsetSum, sum_div]
    apply sum_congr rfl
    intro r hr
    simp only [nsmul_eq_mul, eval_mul, eval_natCast, eval_pow, eval_X]
    rw [Nat.cast_choose ℝ (mem_Icc.mp hr).2]
    field_simp

#print axioms moment_coefficient
#print axioms original_egf

end OrderedPartitions
