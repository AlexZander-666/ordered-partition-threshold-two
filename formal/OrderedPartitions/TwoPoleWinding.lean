import OrderedPartitions.TwoPoleRectangleFTC
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The Cartesian boundary integral of the Cauchy kernel, with its exact normalization. -/

namespace OrderedPartitions.TwoPole
open Set Complex MeasureTheory
noncomputable section

def RegularOnBoundary (f : ℂ → ℂ) : Prop := ∀ z, Boundary z → ContinuousAt f z

theorem rect_congr {f g : ℂ → ℂ} (e : ∀ z, Boundary z → f z = g z) :
    rectIntegral f = rectIntegral g := by
  have h y (hy : |y|=Real.pi) : (∫ x:ℝ in (-3)..3, f ⟨x,y⟩) =
      ∫ x:ℝ in (-3)..3, g ⟨x,y⟩ := intervalIntegral.integral_congr (fun _ hx ↦ e _ (in_hor hx hy))
  have v x (hx : |x|=3) : (∫ y:ℝ in (-Real.pi)..Real.pi, f ⟨x,y⟩) =
      ∫ y:ℝ in (-Real.pi)..Real.pi, g ⟨x,y⟩ :=
    intervalIntegral.integral_congr (fun _ hy ↦ e _ (in_vert hx hy))
  rw [rectIntegral,rectIntegral,h _ (by simp [abs_of_pos Real.pi_pos]),h _ (abs_of_pos Real.pi_pos),
    v _ (by norm_num), v _ (by norm_num)]

theorem boundary_integrable_h {f : ℂ → ℂ} (c : RegularOnBoundary f)
    {y : ℝ} (hy : |y|=Real.pi) : IntervalIntegrable (fun x:ℝ ↦ f ⟨x,y⟩) volume (-3) 3 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have g : ContinuousAt (fun t : ℝ ↦ (⟨t,y⟩:ℂ)) x := by
    simp only [Complex.mk_eq_add_mul_I]; fun_prop
  exact ((c _ (in_hor hx hy)).comp (f:=fun t : ℝ ↦ (⟨t,y⟩:ℂ)) g).continuousWithinAt

theorem boundary_integrable_v {f : ℂ → ℂ} (c : RegularOnBoundary f)
    {x : ℝ} (hx : |x|=3) : IntervalIntegrable (fun y:ℝ ↦ f ⟨x,y⟩) volume (-Real.pi) Real.pi := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have g : ContinuousAt (fun t : ℝ ↦ (⟨x,t⟩:ℂ)) y := by
    simp only [Complex.mk_eq_add_mul_I]; fun_prop
  exact ((c _ (in_vert hx hy)).comp (f:=fun t : ℝ ↦ (⟨x,t⟩:ℂ)) g).continuousWithinAt

theorem rect_sub {f g : ℂ → ℂ} (cf : RegularOnBoundary f) (cg : RegularOnBoundary g) :
    rectIntegral (fun z ↦ f z-g z) = rectIntegral f-rectIntegral g := by
  unfold rectIntegral
  simp only [intervalIntegral.integral_sub (boundary_integrable_h cf (y:=-Real.pi) (by simp [abs_of_pos Real.pi_pos]))
    (boundary_integrable_h cg (y:=-Real.pi) (by simp [abs_of_pos Real.pi_pos])),
    intervalIntegral.integral_sub (boundary_integrable_h cf (abs_of_pos Real.pi_pos))
    (boundary_integrable_h cg (abs_of_pos Real.pi_pos)),
    intervalIntegral.integral_sub (boundary_integrable_v cf (by norm_num : |(3:ℝ)|=3))
    (boundary_integrable_v cg (x:=3) (by norm_num)),
    intervalIntegral.integral_sub (boundary_integrable_v cf (by norm_num : |(-3:ℝ)|=3))
    (boundary_integrable_v cg (x:=-3) (by norm_num))]
  ring

theorem rect_scale (a : ℂ) (f : ℂ → ℂ) :
    rectIntegral (fun z ↦ a*f z) = a*rectIntegral f := by
  simp only [rectIntegral, intervalIntegral.integral_const_mul]
  ring

theorem boundary_ne_zero {z : ℂ} (h : Boundary z) : z ≠ 0 := by
  have := boundary_norm h
  intro e
  norm_num [e] at this

private theorem inv_horizontal (h x : ℝ) :
    (⟨x,-h⟩:ℂ)⁻¹ - (⟨x,h⟩:ℂ)⁻¹ = (2*I)*((h/(h^2+x^2):ℝ):ℂ) := by
  apply Complex.ext <;> simp only [Complex.sub_re, Complex.sub_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, div_eq_mul_inv] <;> ring_nf

private theorem inv_vertical (h x : ℝ) :
    (⟨h,x⟩:ℂ)⁻¹ - (⟨-h,x⟩:ℂ)⁻¹ = 2*((h/(h^2+x^2):ℝ):ℂ) := by
  apply Complex.ext <;> simp only [Complex.sub_re, Complex.sub_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, div_eq_mul_inv] <;> ring_nf

theorem winding_origin : rectIntegral (fun z : ℂ ↦ z⁻¹) = 2*(Real.pi:ℂ)*I := by
  have c : RegularOnBoundary (fun z : ℂ ↦ z⁻¹) := fun _ h ↦ continuousAt_id.inv₀ (boundary_ne_zero h)
  let pi := Real.pi
  have h : (∫ x : ℝ in (-3)..3, (⟨x,-pi⟩:ℂ)⁻¹) - (∫ x : ℝ in (-3)..3, (⟨x,pi⟩:ℂ)⁻¹) =
      (2*I)*((Real.arctan (3/pi)-Real.arctan (-3/pi):ℝ):ℂ) := by
    rw [← intervalIntegral.integral_sub (boundary_integrable_h c (y:=-pi) (by simp [pi,abs_of_pos Real.pi_pos]))
      (boundary_integrable_h c (abs_of_pos Real.pi_pos))]
    change (∫ x : ℝ in (-3)..3, (⟨x,-pi⟩:ℂ)⁻¹ - (⟨x,pi⟩:ℂ)⁻¹) = _
    simp only [inv_horizontal, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_div_sq_add_sq]
  have v : (∫ y : ℝ in (-pi)..pi, (⟨3,y⟩:ℂ)⁻¹) - (∫ y : ℝ in (-pi)..pi, (⟨-3,y⟩:ℂ)⁻¹) =
      2*((Real.arctan (pi/3)-Real.arctan (-pi/3):ℝ):ℂ) := by
    rw [← intervalIntegral.integral_sub (boundary_integrable_v c (by norm_num : |(3:ℝ)|=3))
      (boundary_integrable_v c (by norm_num))]
    simp only [inv_vertical, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_div_sq_add_sq]
    rfl
  rw [rectIntegral,h,v]
  have a := Real.arctan_inv_of_pos (show 0 < pi/3 by dsimp [pi]; positivity)
  rw [inv_div] at a
  simp only [neg_div, Real.arctan_neg, sub_neg_eq_add, Complex.ofReal_add]
  rw [a]
  push_cast
  ring

end
end OrderedPartitions.TwoPole
