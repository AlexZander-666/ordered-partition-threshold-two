import OrderedPartitions.TwoPoleContour

/-! Phase-relative bounds for the actual contour integral at shifts one and two. -/
namespace OrderedPartitions.TwoPole
open Real Set
noncomputable section

private theorem cos_quartic {v : ℝ} (hv : 0 ≤ v) :
    Real.cos v ≤ 1-v^2/2+v^4/24 := by
  let f (t : ℝ) := 1-t^2/2+t^4/24-Real.cos t
  have der (t : ℝ) : deriv f t = -t+t^3/6+Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have mono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (by dsimp [f]; fun_prop) (by dsimp [f]; fun_prop)
    intro x hx
    rw [interior_Ici] at hx
    rw [der]
    linarith [Real.sin_ge_sub_cube (le_of_lt hx)]
  have b := mono (show 0 ∈ Ici (0:ℝ) by simp) hv hv
  simp [f] at b
  linarith

private theorem sin_quintic {v : ℝ} (hv : 0 ≤ v) :
    Real.sin v ≤ v-v^3/6+v^5/120 := by
  let f (t : ℝ) := t-t^3/6+t^5/120-Real.sin t
  have der (t : ℝ) : deriv f t = 1-t^2/2+t^4/24-Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have mono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (by dsimp [f]; fun_prop) (by dsimp [f]; fun_prop)
    intro x hx
    rw [interior_Ici] at hx
    rw [der]
    linarith [cos_quartic (le_of_lt hx)]
  have b := mono (show 0 ∈ Ici (0:ℝ) by simp) hv hv
  simp [f] at b
  linarith

/-- The real part vanishes no faster than the squared height; this preserves a second phase shift. -/
theorem principal_lower_re {q : ℝ} (hq : 0<q) (h1 : q<1) {z : ℂ}
    (gz : G q z=0) (iz : z.im ∈ Ioo 0 (Real.pi/2)) : z.im^2/7 < z.re := by
  have hv := iz.1
  have small : z.im < 8/5 := by linarith [iz.2, Real.pi_lt_d2]
  have v2 : z.im^2 < (8/5:ℝ)^2 := pow_lt_pow_left₀ small hv.le (by decide)
  have gap : z.im - z.im^3/6 + z.im^5/120 < z.im - z.im^3/7 := by
    have h : 0 < z.im^3*((1/6:ℝ)-1/7-z.im^2/120) :=
      mul_pos (pow_pos hv _) (by linarith)
    linarith only [h]
  have si := (sin_quintic hv.le).trans_lt gap
  have hi := congrArg Complex.im gz
  rw [im_G, Complex.zero_im] at hi
  have prod : z.im * Real.exp (-z.re) = q * Real.sin z.im := by
    rw [Real.exp_neg]
    apply (mul_inv_eq_iff_eq_mul₀ (Real.exp_pos z.re).ne').2
    linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hv (by linarith [iz.2, Real.pi_pos])
  have se := mul_lt_mul_of_pos_right h1 hs
  have expbound := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-z.re)) hv.le
  rw [prod] at expbound
  by_contra! bad
  nlinarith [mul_le_mul_of_nonneg_left bad hv.le]

theorem contour_two_relative {q : ℝ} (hq : 1/6<q) (h1 : q<1) {z : ℂ}
    (gz : G q z=0) (iz : z.im ∈ Ioo 0 (Real.pi/2)) (n : ℕ) :
    ‖deriv (G q) z‖ * ‖z‖^(n+1)/2 * ‖contour q n‖ ≤
      81*(7/9)^(n+1)*Real.sin (2*z.arg) := by
  obtain ⟨xp,xmax,r,_,d⟩ := principal_bounds hq h1 gz iz
  have b := contour_bound hq h1 n
  have v := iz.1
  have zn : 0 < ‖z‖ := norm_pos_iff.mpr (fun h ↦ v.ne' (by simp [h]))
  have hp : 0 < q := by linarith
  have k := principal_lower_re hp h1 gz iz
  have r9 : ‖z‖ ≤ 9*Real.cos z.arg := by
    rw [Complex.cos_arg (norm_pos_iff.mp zn), ←mul_div_assoc, le_div_iff₀ zn]
    have ns := Complex.norm_eq_sqrt_sq_add_sq z
    have sq : ‖z‖^2=z.re^2+z.im^2 := by rw [ns, Real.sq_sqrt (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr xmax) xp]
  have sine : 0 ≤ Real.sin z.arg := by rw [Complex.sin_arg]; positivity
  have cose : 0 ≤ Real.cos z.arg := by linarith
  have im : z.im = ‖z‖*Real.sin z.arg := by rw [Complex.sin_arg]; field_simp
  calc
    _ ≤ (2*z.im)*‖z‖^(n+1)/2*(18/(3:ℝ)^(n+1)) := by gcongr
    _ = 18*‖z‖*(‖z‖/3)^(n+1)*Real.sin z.arg := by rw [im, div_pow]; ring
    _ ≤ 18*(9*Real.cos z.arg)*(7/9)^(n+1)*Real.sin z.arg := by
      have : ‖z‖/3 ≤ 7/9 := by linarith
      gcongr
    _ = _ := by rw [Real.sin_two_mul]; ring

theorem relative_one_of_twenty {q : ℝ} (hq : 1/6<q) (h1 : q<1) {z : ℂ}
    (gz : G q z=0) (iz : z.im ∈ Ioo 0 (Real.pi/2)) {n : ℕ} (hn : 20≤n) :
    ‖deriv (G q) z‖ * ‖z‖^(n+1)/2 * ‖contour q n‖ ≤ Real.sin z.arg/4 := by
  have sine : 0 ≤ Real.sin z.arg := by rw [Complex.sin_arg]; exact div_nonneg iz.1.le (norm_nonneg _)
  have p : (7/9:ℝ)^(n+1) ≤ (7/9:ℝ)^21 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  apply (contour_relative hq h1 gz iz n).trans
  calc _ ≤ (42*(7/9:ℝ)^21)*Real.sin z.arg := by gcongr
       _ ≤ _ := by
         calc _ ≤ (1/4:ℝ)*Real.sin z.arg := mul_le_mul_of_nonneg_right (by norm_num) sine
              _ = _ := by ring

theorem relative_two_of_twentyfive {q : ℝ} (hq : 1/6<q) (h1 : q<1) {z : ℂ}
    (gz : G q z=0) (iz : z.im ∈ Ioo 0 (Real.pi/2)) {n : ℕ} (hn : 25≤n) :
    ‖deriv (G q) z‖ * ‖z‖^(n+1)/2 * ‖contour q n‖ ≤ Real.sin (2*z.arg)/8 := by
  have zn : z≠0 := fun h ↦ iz.1.ne' (by simp [h])
  have xp := (principal_bounds hq h1 gz iz).1
  have v := iz.1
  have sine : 0 ≤ Real.sin (2*z.arg) := by
    rw [Real.sin_two_mul, Complex.sin_arg, Complex.cos_arg zn]; positivity
  have p : (7/9:ℝ)^(n+1) ≤ (7/9:ℝ)^26 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  apply (contour_two_relative hq h1 gz iz n).trans
  calc _ ≤ (81*(7/9:ℝ)^26)*Real.sin (2*z.arg) := by gcongr
       _ ≤ _ := by
         calc _ ≤ (1/8:ℝ)*Real.sin (2*z.arg) := mul_le_mul_of_nonneg_right (by norm_num) sine
              _ = _ := by ring

end
end OrderedPartitions.TwoPole
