import OrderedPartitions.TwoPoleRectangle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Uniform norm bounds for the literal contour error, including the coalescence scale. -/
namespace OrderedPartitions.TwoPole
open Set Complex MeasureTheory
noncomputable section

/-- The positively oriented boundary integral, in Cartesian parametrizations. -/
def rectIntegral (f : ℂ → ℂ) : ℂ :=
  ((∫ x : ℝ in (-3)..3, f ⟨x,-Real.pi⟩) - (∫ x : ℝ in (-3)..3, f ⟨x,Real.pi⟩)) +
  I * ((∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨3,y⟩) - (∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨-3,y⟩))

/-- The residual integral after extracting the origin and conjugate principal poles. -/
def contour (q : ℝ) (n : ℕ) : ℂ :=
  rectIntegral (fun z ↦ (z^(n+1)*G q z)⁻¹) / (2*(Real.pi:ℂ)*I)

private theorem rect_norm (f : ℂ → ℂ) {c : ℝ}
    (horizontal : ∀ x : ℝ, ∀ y : ℝ, |y|=Real.pi → ‖f ⟨x,y⟩‖ ≤ c)
    (vertical : ∀ x : ℝ, |x|=3 → ∀ y : ℝ, |y|≤Real.pi → ‖f ⟨x,y⟩‖ ≤ c) :
    ‖rectIntegral f‖ ≤ (12+4*Real.pi)*c := by
  have h y (hy : |y|=Real.pi) :
      ‖∫ x : ℝ in (-3)..3, f ⟨x,y⟩‖ ≤ c*6 := by
    convert intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=-3) (b:=3) (fun x _ ↦ horizontal x y hy) using 1
    norm_num
  have v x (hx : |x|=3) :
      ‖∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨x,y⟩‖ ≤ c*(2*Real.pi) := by
    have e : |Real.pi - -Real.pi| = 2*Real.pi := by
      rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy ↦ vertical x hx y ?_)).trans
    · exact le_of_eq (by rw [e])
    · rw [uIoc_of_le (by linarith [Real.pi_pos])] at hy
      exact abs_le.2 ⟨hy.1.le, hy.2⟩
  have hi := h (-Real.pi) (by simp [abs_of_pos Real.pi_pos])
  have hj := h Real.pi (abs_of_pos Real.pi_pos)
  have vi := v 3 (by norm_num)
  have vj := v (-3) (by norm_num)
  unfold rectIntegral
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_I, one_mul]
  linarith [norm_sub_le (∫ x : ℝ in (-3)..3, f ⟨x,-Real.pi⟩) (∫ x : ℝ in (-3)..3, f ⟨x,Real.pi⟩),
    norm_sub_le (∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨3,y⟩) (∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨-3,y⟩)]

/-- Effective bound with no external residue or complex-integral assumption. -/
theorem contour_bound {q : ℝ} (hq : 1/6<q) (h1 : q<1) (n : ℕ) :
    ‖contour q n‖ ≤ 18/3^(n+1) := by
  let f (z : ℂ) := (z^(n+1)*G q z)⁻¹
  have atSide (z : ℂ) (r : 3≤‖z‖)
      (side : |z.im|=Real.pi ∨ z.re = -3 ∨ (z.re=3 ∧ |z.im|≤Real.pi)) :
      ‖f z‖ ≤ 4/3^(n+1) := by
    have g := rectangle_bound hq h1 z side
    have t := mul_le_mul (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) r (n+1)) g
      (by norm_num) (pow_nonneg (norm_nonneg z) _)
    change ‖(z^(n+1)*G q z)⁻¹‖ ≤ _
    rw [norm_inv, norm_mul, norm_pow]
    have pos : 0 < ‖z‖^(n+1)*‖G q z‖ := by positivity
    rw [inv_eq_one_div, div_le_div_iff₀ pos (by positivity)]
    linarith
  have b := rect_norm f (c:=4/3^(n+1))
    (fun x y hy ↦ atSide _ (by
      have e := Complex.abs_im_le_norm (⟨x,y⟩ : ℂ)
      change |y| ≤ _ at e
      linarith [Real.pi_gt_three]) (Or.inl hy))
    (fun x hx y hy ↦ atSide _ (by
      have e := Complex.abs_re_le_norm (⟨x,y⟩ : ℂ)
      change |x| ≤ _ at e
      linarith) (by
        rcases (abs_eq (by norm_num : (0:ℝ)≤3)).1 hx with h|h
        · exact Or.inr (Or.inr ⟨h,hy⟩)
        · exact Or.inr (Or.inl h)))
  unfold contour
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real,
    norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_div_iff₀ (by positivity) (by positivity)]
  change ‖rectIntegral f‖ * _ ≤ _
  have fact : ‖rectIntegral f‖ * (3:ℝ)^(n+1) ≤ (12+4*Real.pi)*4 := by
    apply (le_div_iff₀ (by positivity)).mp
    simpa [mul_div_assoc] using b
  linarith [Real.pi_gt_three]

/-- Dimensionless residual coefficient, small even relative to the one-step phase gap. -/
theorem contour_relative {q : ℝ} (hq : 1/6<q) (h1 : q<1) {z : ℂ} (gz : G q z=0)
    (iz : z.im ∈ Ioo 0 (Real.pi/2)) (n : ℕ) :
    ‖deriv (G q) z‖ * ‖z‖^(n+1)/2 * ‖contour q n‖ ≤
      42*(7/9)^(n+1)*Real.sin z.arg := by
  obtain ⟨_,_,r,_,d⟩ := principal_bounds hq h1 gz iz
  have b := contour_bound hq h1 n
  have zn : 0 < ‖z‖ := norm_pos_iff.mpr (fun h ↦ iz.1.ne' (by simp [h]))
  have zv : 0 < z.im := iz.1
  have sine : 0 ≤ Real.sin z.arg := by rw [Complex.sin_arg]; positivity
  have im : z.im = ‖z‖ * Real.sin z.arg := by rw [Complex.sin_arg]; field_simp
  have collapse : (2*z.im) * ‖z‖^(n+1)/2 * (18/(3:ℝ)^(n+1)) =
      18*‖z‖*(‖z‖/3)^(n+1)*Real.sin z.arg := by rw [im, div_pow]; ring
  calc
    _ ≤ (2*z.im) * ‖z‖^(n+1)/2 * (18/(3:ℝ)^(n+1)) := by gcongr
    _ = _ := collapse
    _ ≤ _ := by
      have a : 18*‖z‖ ≤ 42 := by linarith
      have c : ‖z‖/3 ≤ 7/9 := by linarith
      gcongr

end
end OrderedPartitions.TwoPole
