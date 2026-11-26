import OrderedPartitions.TwoPolePrincipal
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Uniform separation of the exact denominator from zero on the rectangle with vertical sides
at ±3 and horizontal sides at ±π. -/

namespace OrderedPartitions.TwoPole
open Complex Set
open scoped ComplexConjugate
noncomputable section

/-- The supercritical inequality alone implies the quantitative lower bound used on the contour. -/
theorem sixth_lt_of_critical {q : ℝ} (hq : 0 < q) (crit : -1 < Real.log q + (1-2*q)) :
    1/6 < q := by
  have ee : Real.exp 5 < (6 : ℝ)^3 := by
    have e : Real.exp 1 < 11/4 := by linarith [Real.exp_one_lt_d9]
    have ep := pow_lt_pow_left₀ e (Real.exp_pos 1).le (by decide : (5:ℕ) ≠ 0)
    have rep : Real.exp (5:ℝ) = Real.exp 1 ^5 := by simp [← Real.exp_nat_mul]
    rw [rep]
    norm_num at ep ⊢
    linarith
  have l := Real.strictMonoOn_log (show Real.exp 5 ∈ Ioi 0 from Real.exp_pos _)
    (show (6:ℝ)^3 ∈ Ioi 0 by change 0 < (6:ℝ)^3; positivity) ee
  rw [Real.log_exp, Real.log_pow] at l
  norm_num at l
  have ratio := Real.log_le_sub_one_of_pos (show 0<6*q by positivity)
  rw [Real.log_mul (by norm_num) hq.ne'] at ratio
  linarith

private theorem exp_three : 20 < Real.exp 3 := by
  have e : (1359/500 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have ep := pow_lt_pow_left₀ e (by norm_num) (by decide : (3:ℕ)≠0)
  have rep : Real.exp (3:ℝ) = Real.exp 1 ^3 := by simp [← Real.exp_nat_mul]
  rw [rep]
  norm_num at ep
  linarith

private theorem right_upper {q : ℝ} (hq : 1/6 < q) {z : ℂ} (re : z.re=3)
    (lo : 0 ≤ z.im) (hi : z.im ≤ Real.pi) : 1/4 ≤ ‖G q z‖ := by
  have pos : 0 < q := by linarith
  have rr := Complex.abs_re_le_norm (G q z)
  have ii := Complex.abs_im_le_norm (G q z)
  rw [re_G, re] at rr
  rw [im_G, re] at ii
  by_cases sm : z.im ≤ 2/3
  · have co : 7/9 ≤ Real.cos z.im := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x:=z.im),
        mul_nonneg (sub_nonneg.mpr sm) (show 0≤2/3+z.im by linarith)]
    have ce : 20*(7/9:ℝ) ≤ Real.exp 3*Real.cos z.im :=
      mul_le_mul exp_three.le co (by norm_num) (Real.exp_pos 3).le
    have h := mul_le_mul_of_nonneg_left ce pos.le
    nlinarith [(le_abs_self _).trans rr]
  · by_cases mid : z.im ≤ Real.pi/2
    · have si := Real.mul_le_sin lo mid
      have rate : (3/5:ℝ) ≤ 2/Real.pi :=
        (le_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_d2])
      have sl : 3/5*z.im ≤ Real.sin z.im := (mul_le_mul_of_nonneg_right rate lo).trans si
      have pe : 10/3 ≤ q*Real.exp 3 := by
        have := mul_le_mul (le_of_lt hq) exp_three.le (by norm_num) pos.le
        linarith
      have h := mul_le_mul pe sl (show 0≤3/5*z.im by positivity)
        (show 0 ≤ q*Real.exp 3 by positivity)
      nlinarith [(le_abs_self _).trans ii]
    · have co := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_ge mid)
        (show z.im ≤ Real.pi + Real.pi/2 by linarith [Real.pi_pos])
      have ne := mul_nonpos_of_nonneg_of_nonpos (show 0≤q*Real.exp 3 by positivity) co
      linarith [(neg_le_abs _).trans rr]

theorem G_conj (q : ℝ) (z : ℂ) : G q (conj z) = conj (G q z) := by
  simp [G, Complex.exp_conj, map_ofNat]

/-- Every side is controlled, including the points near the real axis on the right side. -/
theorem rectangle_bound {q : ℝ} (hq : 1/6 < q) (h1 : q < 1) (z : ℂ)
    (side : |z.im|=Real.pi ∨ z.re = -3 ∨ (z.re=3 ∧ |z.im|≤Real.pi)) :
    1/4 ≤ ‖G q z‖ := by
  have pq : 0 < q := by linarith
  rcases side with h | h | ⟨xr, hi⟩
  · have si : Real.sin z.im = 0 := by
      rcases (abs_eq (le_of_lt Real.pi_pos)).1 h with hi | hi <;> simp [hi]
    have ab := Complex.abs_im_le_norm (G q z)
    rw [im_G, si, mul_zero, add_zero, abs_neg, h] at ab
    linarith [Real.pi_gt_three]
  · have ab := (le_abs_self _).trans (Complex.abs_re_le_norm (G q z))
    rw [re_G,h] at ab
    have le : q*Real.exp (-3) ≤ 1 := by
      have e : Real.exp (-3) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      have := mul_le_mul_of_nonneg_left e pq.le
      linarith
    have c := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos z.im)
      (show 0≤q*Real.exp (-3) by positivity)
    linarith
  · rcases le_total 0 z.im with hp | hm
    · exact right_upper hq xr hp ((le_abs_self _).trans hi)
    · have b := right_upper (z:=conj z) hq (by simpa using xr)
        (by simpa using hm) (by simpa using (neg_le_abs z.im).trans hi)
      simpa [G_conj] using b

end
end OrderedPartitions.TwoPole
