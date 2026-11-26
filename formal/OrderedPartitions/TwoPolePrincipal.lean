import OrderedPartitions.TwoPoleGeometry

/-! Existence, dominance in the horizontal strip, and simplicity of the conjugate pole pair. -/

namespace OrderedPartitions.TwoPole
open Set
noncomputable section

private def regularHeight (v : ℝ) : ℝ :=
  -Real.log (Real.sinc v) - Real.cos v / Real.sinc v

private theorem regular_eq {v : ℝ} (hv : v ≠ 0) : regularHeight v = height v := by
  rw [regularHeight, Real.sinc_of_ne_zero hv, height, ← Real.log_inv, inv_div]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private theorem sinc_pos {v : ℝ} (hv : v ∈ Icc 0 (Real.pi/2)) : 0 < Real.sinc v := by
  rcases hv.1.eq_or_lt with h | h
  · simp [← h]
  · rw [Real.sinc_of_ne_zero h.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi h (by linarith [hv.2, Real.pi_pos])) h

private theorem regular_cont : ContinuousOn regularHeight (Icc 0 (Real.pi/2)) := by
  intro v hv
  exact ((Real.continuous_sinc.continuousAt.log (sinc_pos hv).ne').neg.sub
    (Real.continuous_cos.continuousAt.div Real.continuous_sinc.continuousAt
      (sinc_pos hv).ne')).continuousWithinAt

/-- A supercritical parameter has a unique simple upper zero in the full strip. -/
theorem principal_exists {q : ℝ} (hq : 0 < q) (crit : -1 < Real.log q + (1-2*q)) :
    ∃ z : ℂ, G q z = 0 ∧ z.im ∈ Ioo 0 (Real.pi/2) ∧
      ∀ w : ℂ, G q w = 0 → w.im ∈ Ioo 0 Real.pi → w = z := by
  have high : Real.log q + (1-2*q) < regularHeight (Real.pi/2) := by
    rw [regular_eq (by positivity), height, Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp only [div_one, mul_zero, sub_zero]
    have hi := Real.log_le_sub_one_of_pos hq
    linarith [Real.log_pos (show 1 < Real.pi/2 by linarith [Real.pi_gt_three])]
  have low : regularHeight 0 < Real.log q + (1-2*q) := by simpa [regularHeight] using crit
  obtain ⟨v, hv, eq⟩ := intermediate_value_Ioo (show (0 : ℝ) ≤ Real.pi/2 by positivity)
    regular_cont ⟨low, high⟩
  rw [regular_eq hv.1.ne'] at eq
  let x := 1-2*q+v*Real.cos v / Real.sin v
  let z : ℂ := ⟨x,v⟩
  have vz : z.im ∈ Ioo 0 Real.pi := ⟨hv.1, by change v < Real.pi; linarith [hv.2, Real.pi_pos]⟩
  have gz : G q z = 0 := (zero_iff hq hv.1 (Real.sin_pos_of_pos_of_lt_pi hv.1 vz.2)).2 ⟨rfl,eq⟩
  exact ⟨z, gz, hv, fun w hw iw ↦ upper_unique hq hw gz iw vz⟩

/-- Quantitative location and slope bound, retaining the vanishing imaginary part. -/
theorem principal_bounds {q : ℝ} (hq : 1/6 < q) (h1 : q < 1) {z : ℂ}
    (hz : G q z = 0) (iv : z.im ∈ Ioo 0 (Real.pi/2)) :
    0 < z.re ∧ z.re < 5/3 ∧ ‖z‖ < 7/3 ∧ deriv (G q) z ≠ 0 ∧
      ‖deriv (G q) z‖ < 2*z.im := by
  have hp : 0 < q := by linarith
  have hv := iv.1
  have hpi : z.im < Real.pi := by linarith [iv.2, Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hv hpi
  have hc := Real.cos_pos_of_mem_Ioo (show z.im ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos], iv.2⟩)
  obtain ⟨hx, _⟩ := (zero_iff hp hv hs).mp hz
  have hi := congrArg Complex.im hz
  rw [im_G, Complex.zero_im] at hi
  have e1 : 1 < Real.exp z.re := by
    by_contra! h
    have := mul_le_mul_of_nonneg_left h hp.le
    nlinarith [mul_lt_mul_of_pos_right (show q*Real.exp z.re < 1 by linarith) hs,
      Real.sin_lt hv]
  have xpos : 0 < z.re := Real.one_lt_exp_iff.mp e1
  have tanbound := Real.lt_tan hv iv.2
  rw [Real.tan_eq_sin_div_cos] at tanbound
  have hi' : z.im*Real.cos z.im/Real.sin z.im < 1 :=
    (div_lt_one hs).2 ((lt_div_iff₀ hc).mp tanbound)
  have lo' : Real.cos z.im ≤ z.im*Real.cos z.im/Real.sin z.im :=
    (le_div_iff₀ hs).2 (by nlinarith [mul_le_mul_of_nonneg_right (Real.sin_le hv.le) hc.le])
  have xmax : z.re < 5/3 := by linarith
  have vm : z.im < 8/5 := by linarith [iv.2, Real.pi_lt_d2]
  have nr : ‖z‖ < 7/3 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_lt' (by norm_num : (0:ℝ)<7/3)]
    nlinarith [mul_pos (sub_pos.mpr xmax) (show 0<5/3+z.re by linarith),
      mul_pos (sub_pos.mpr vm) (show 0<8/5+z.im by linarith)]
  have de := (derivative_at_zero hz).deriv
  have dre : (deriv (G q) z).re = z.im*Real.cos z.im/Real.sin z.im-1 := by
    rw [de]
    simp
    linarith
  have dim : (deriv (G q) z).im = z.im := by rw [de]; simp
  have deficit : 1-z.im*Real.cos z.im/Real.sin z.im < z.im := by
    nlinarith [Real.one_sub_sq_div_two_lt_cos hv.ne',
      mul_pos hv (show 0<2-z.im by linarith)]
  refine ⟨xpos,xmax,nr,fun h ↦ hv.ne' (by rw [← dim, h, Complex.zero_im]), ?_⟩
  rw [Complex.norm_eq_sqrt_sq_add_sq, dre, dim, Real.sqrt_lt' (by positivity : 0<2*z.im)]
  nlinarith [mul_pos (show 0<z.im-(1-z.im*Real.cos z.im/Real.sin z.im) by linarith)
    (show 0<z.im+(1-z.im*Real.cos z.im/Real.sin z.im) by linarith),
    sq_pos_of_pos hv]

end
end OrderedPartitions.TwoPole
