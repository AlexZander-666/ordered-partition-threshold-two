import OrderedPartitions.LastBlockRow
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Polynomial.Taylor

noncomputable section
open Finset Polynomial
namespace OrderedPartitions

theorem row_zero {j : ℕ} (hj : 1 ≤ j) : row 0 j = 1 := by
  classical
  rw [row_eq_sum hj]
  have emptyPartition : Onto 0 0 := ⟨id, Function.surjective_id⟩
  have : Unique (Onto 0 0) := ⟨⟨emptyPartition⟩, fun f ↦
    Subtype.ext (funext (fun x ↦ Fin.elim0 x))⟩
  simp [blockRow, large]

/-- Unnormalized binomial moment: sum of choose(number of marked blocks,h). -/
def markedCount (n j h : ℕ) : ℝ := ((row n j).comp (X+1)).coeff h

theorem markedCount_zero (n j : ℕ) : markedCount n j 0 = (row n j).eval 1 :=
  Polynomial.taylor_coeff_zero _ _

theorem markedCount_one (n j : ℕ) : markedCount n j 1 = (row n j).derivative.eval 1 :=
  Polynomial.taylor_coeff_one _ _

theorem markedCount_eq_count (n j h : ℕ) : markedCount n j h =
    ∑ d ∈ range (n+1), (count n j d : ℝ) * (d.choose h : ℝ) := by
  simp [markedCount, row, Polynomial.sum_comp, finsetSum_coeff, mul_comp, pow_comp, coeff_X_add_one_pow]

private def markedPart (j r h : ℕ) (p : ℝ[X]) : ℝ :=
  p.coeff h + (if j ≤ r ∧ h ≠ 0 then p.coeff (h-1) else 0)

private theorem markedPart_eq (j r h : ℕ) (p : ℝ[X]) :
    (p*(X+1)^(if j ≤ r then 1 else 0)).coeff h = markedPart j r h p := by
  by_cases hbig : j ≤ r
  · cases h <;> simp [hbig, markedPart, mul_add, add_comm]
  · simp [hbig, markedPart]

theorem markedCount_recurrence (n : ℕ) {j : ℕ} (hj : 1 ≤ j) (h : ℕ) :
    markedCount (n+1) j h = ∑ r ∈ Icc 1 (n+1), ((n+1).choose r : ℝ) *
      (markedCount (n+1-r) j h +
        if j ≤ r ∧ h ≠ 0 then markedCount (n+1-r) j (h-1) else 0) := by
  unfold markedCount
  rw [row_recurrence n hj]
  simp only [Polynomial.sum_comp, nsmul_eq_mul, mul_comp, natCast_comp, pow_comp, X_comp, finsetSum_coeff,
    coeff_natCast_mul, markedPart_eq, markedPart]

/-- EGF for actual binomial moments. The scalar object at h=0 counts all unrestricted lists. -/
def momentSeries (j h : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n ↦ markedCount n j h / n.factorial)

def sizeSeries (a : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun r ↦ if a ≤ r then (r.factorial : ℝ)⁻¹ else 0)

private theorem product_coeff (a N : ℕ) (ha : 1 ≤ a) (S : PowerSeries ℝ) :
    PowerSeries.coeff N (sizeSeries a * S) =
      ∑ r ∈ Icc 1 N, (if a ≤ r then (r.factorial : ℝ)⁻¹ else 0) *
        PowerSeries.coeff (N-r) S := by
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [sizeSeries, PowerSeries.coeff_mk]
  symm
  apply sum_subset
  · intro r hr
    simpa only [mem_range, Nat.lt_succ_iff] using (mem_Icc.mp hr).2
  · intro r hr hnot
    have hN := Nat.le_of_lt_succ (mem_range.mp hr)
    have : r=0 := by by_contra! h; exact hnot (mem_Icc.mpr ⟨by omega,hN⟩)
    simp [this, show ¬ a ≤ 0 by omega]


private theorem normalized_marked (n : ℕ) {j : ℕ} (hj : 1 ≤ j) (h : ℕ) :
    PowerSeries.coeff (n+1) (momentSeries j h) =
      PowerSeries.coeff (n+1) (sizeSeries 1 * momentSeries j h) +
      (if h = 0 then 0 else PowerSeries.coeff (n+1) (sizeSeries j * momentSeries j (h-1))) := by
  rw [product_coeff 1 _ (by omega), product_coeff j _ hj]
  simp only [momentSeries, PowerSeries.coeff_mk]
  rw [markedCount_recurrence n hj, sum_div]
  by_cases h0 : h = 0
  · simp only [h0, ne_eq, not_true_eq_false, and_false, ite_false, add_zero, ite_true]
    apply sum_congr rfl
    intro r hr
    have hle := (mem_Icc.mp hr).2
    rw [if_pos (mem_Icc.mp hr).1, Nat.cast_choose ℝ hle]
    field_simp
  · rw [if_neg h0, ← sum_add_distrib]
    apply sum_congr rfl
    intro r hr
    have hle := (mem_Icc.mp hr).2
    rw [if_pos (mem_Icc.mp hr).1, Nat.cast_choose ℝ hle]
    by_cases hjr : j ≤ r <;> simp [hjr, h0] <;> field_simp

private theorem moment_zero_rank {j : ℕ} (hj : 1 ≤ j) (h : ℕ) :
    PowerSeries.coeff 0 (momentSeries j h) = if h=0 then 1 else 0 := by
  simp [momentSeries, markedCount, row_zero hj, coeff_one]

theorem free_resolvent {j : ℕ} (hj : 1 ≤ j) :
    (1-sizeSeries 1)*momentSeries j 0 = 1 := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero =>
    rw [map_sub, moment_zero_rank hj, product_coeff 1 0 (by omega)]
    simp
  | succ n =>
    have h := normalized_marked n hj 0
    simpa [PowerSeries.coeff_one] using sub_eq_zero.mpr (by simpa using h :
      PowerSeries.coeff (n+1) (momentSeries j 0) =
      PowerSeries.coeff (n+1) (sizeSeries 1 * momentSeries j 0))

theorem marked_resolvent {j : ℕ} (hj : 1 ≤ j) (h : ℕ) :
    (1-sizeSeries 1)*momentSeries j (h+1) = sizeSeries j * momentSeries j h := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero =>
    rw [map_sub, moment_zero_rank hj, product_coeff j 0 hj, product_coeff 1 0 (by omega)]
    simp
  | succ n =>
    have eqn := normalized_marked n hj (h+1)
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] at eqn
    simpa using sub_eq_iff_eq_add.mpr (eqn.trans (add_comm _ _) :
      PowerSeries.coeff (n+1) (momentSeries j (h+1)) =
      PowerSeries.coeff (n+1) (sizeSeries j * momentSeries j h) +
      PowerSeries.coeff (n+1) (sizeSeries 1 * momentSeries j (h+1)))

/-- Coefficientwise marked-segment identity for the original labeled ordered partitions. -/
theorem marked_segments {j : ℕ} (hj : 1 ≤ j) (h : ℕ) :
    momentSeries j h = sizeSeries j ^ h * momentSeries j 0 ^ (h+1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    calc
      _ = ((1-sizeSeries 1)*momentSeries j 0)*momentSeries j (h+1) := by
        rw [free_resolvent hj, one_mul]
      _ = momentSeries j 0 * ((1-sizeSeries 1)*momentSeries j (h+1)) := by ring
      _ = _ := by rw [marked_resolvent hj, ih, pow_succ (sizeSeries j),
        pow_succ (momentSeries j 0) (h+1)]; ring

#print axioms row_zero
#print axioms markedCount_zero
#print axioms markedCount_one
#print axioms markedCount_eq_count
#print axioms markedCount_recurrence
#print axioms free_resolvent
#print axioms marked_segments

end OrderedPartitions
