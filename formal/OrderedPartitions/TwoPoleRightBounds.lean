import OrderedPartitions.TwoPoleBranch

noncomputable section
namespace OrderedPartitions.TwoPole
open Real Set

theorem cot_deficit_bound {v : ℝ} (iv : v∈Ioo 0 (π/2)) :
    0 ≤ 1-v*cos v/sin v ∧ 1-v*cos v/sin v ≤ v^2/2 := by
  have sv := sin_pos_of_pos_of_lt_pi iv.1 (by linarith [iv.2,pi_pos])
  have cv := cos_pos_of_mem_Ioo (show v∈Ioo (-(π/2)) (π/2) from ⟨by linarith [iv.1,pi_pos],iv.2⟩)
  have t := Real.lt_tan iv.1 iv.2
  rw [Real.tan_eq_sin_div_cos] at t
  have upper := (div_lt_one sv).mpr ((lt_div_iff₀ cv).mp t)
  have lower : cos v ≤ v*cos v/sin v := (le_div_iff₀ sv).mpr
    (by nlinarith [mul_le_mul_of_nonneg_right (sin_le iv.1.le) cv.le])
  exact ⟨by linarith,by linarith [one_sub_sq_div_two_lt_cos iv.1.ne']⟩

theorem height_ub_small {v : ℝ} (iv : v∈Ioo 0 (π/2)) (small : v≤1) :
    height v + 1 ≤ v^2 := by
  have vp := iv.1
  have vst := Real.sin_ge_sub_cube vp.le
  have vsq : v^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr small) (show 0≤1+v by linarith)]
  have sl : v/2 ≤ sin v := by nlinarith [mul_le_mul_of_nonneg_left vsq vp.le]
  have sp : 0 < sin v := by linarith
  have frac : v/sin v-1 ≤ v^2/3 := by
    have aux : v/sin v ≤ v^2/3+1 := (div_le_iff₀ sp).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left sl (sq_nonneg v)])
    linarith
  have logb := log_le_sub_one_of_pos (div_pos vp sp)
  have defic := (cot_deficit_bound iv).2
  unfold height
  linarith [sq_nonneg v]

theorem pole_right_ratio_bound {q : ℝ} (hq : 3/4 ≤ q) (h1 : q<1)
    (osc : -1<level q) (small : (upperPole q).im≤1) :
    0 ≤ (upperPole q).re/(upperPole q).im ∧
    (upperPole q).re/(upperPole q).im ≤ 4*(upperPole q).im := by
  let z := upperPole q
  have qp : 0<q := by linarith
  obtain ⟨hz,iv⟩ := upperPole_spec qp osc
  obtain ⟨hx,_⟩ := (zero_iff qp iv.1 (sin_pos_of_pos_of_lt_pi iv.1 (by linarith [iv.2,pi_pos]))).mp hz
  have xU : z.re ≤ 2*(1-q) := by
    dsimp [z];linarith [(cot_deficit_bound iv).1]
  have logb := one_sub_inv_le_log_of_pos qp
  have lin : (1-q)/2 ≤ level q+1 := by
    have low : (1-q)/2 ≤ 1-q⁻¹+2-2*q := by
      field_simp
      nlinarith [mul_nonneg (show 0≤q-2/3 by linarith) (show 0≤1-q by linarith)]
    unfold level;linarith
  have at_zero := height_ub_small iv small
  rw [pole_height_eq qp osc] at at_zero
  have p := (principal_bounds (by linarith : 1/6<q) h1 hz iv).1
  exact ⟨div_nonneg p.le iv.1.le, (div_le_iff₀ iv.1).mpr (by change z.re ≤ 4*z.im*z.im; dsimp [z] at *; nlinarith)⟩

#print axioms pole_right_ratio_bound
end OrderedPartitions.TwoPole
