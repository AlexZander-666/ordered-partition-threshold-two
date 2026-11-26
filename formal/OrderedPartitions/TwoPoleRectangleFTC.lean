import OrderedPartitions.TwoPoleContour
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Cartesian primitive rule and the winding integral of a rectangle. -/
namespace OrderedPartitions.TwoPole
open Set Complex
noncomputable section

/-- The four oriented sides; corners may belong to two sides. -/
def Boundary (z : ℂ) : Prop :=
  (|z.im| = Real.pi ∧ |z.re|≤3) ∨ (|z.re|=3 ∧ |z.im|≤Real.pi)

theorem boundary_norm {z : ℂ} (h : Boundary z) : 3≤‖z‖ := by
  rcases h with h|h
  · linarith [h.1, Complex.abs_im_le_norm z, Real.pi_gt_three]
  · linarith [h.1, Complex.abs_re_le_norm z]

theorem in_hor {x y : ℝ} (hx : x ∈ uIcc (-3) 3) (hy : |y|=Real.pi) :
    Boundary ⟨x,y⟩ := by
  rw [uIcc_of_le (by norm_num)] at hx
  exact Or.inl ⟨hy,abs_le.2 hx⟩

theorem in_vert {x y : ℝ} (hx : |x|=3) (hy : y ∈ uIcc (-Real.pi) Real.pi) :
    Boundary ⟨x,y⟩ := by
  rw [uIcc_of_le (by linarith [Real.pi_pos])] at hy
  exact Or.inr ⟨hx,abs_le.2 hy⟩

/-- The complex derivative is only required along the paths, as is continuity of its value. -/
theorem rect_primitive (F f : ℂ → ℂ) (d : ∀ z, Boundary z → HasDerivAt F (f z) z)
    (cont : ∀ z, Boundary z → ContinuousAt f z) : rectIntegral f = 0 := by
  have h y (hy : |y|=Real.pi) : (∫ x : ℝ in (-3)..3, f ⟨x,y⟩) = F ⟨3,y⟩-F ⟨-3,y⟩ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun x : ℝ ↦ F ⟨x,y⟩)
    · intro x hx
      have hd := d ⟨x,y⟩ (in_hor hx hy)
      rw [Complex.mk_eq_add_mul_I] at hd
      have g := (hd.comp (x:ℂ) ((hasDerivAt_id (x:ℂ)).add_const ((y:ℂ)*I))).comp_ofReal
      simpa [Complex.mk_eq_add_mul_I, Function.comp_def] using g
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      have c := cont _ (in_hor hx hy)
      have g : ContinuousAt (fun t : ℝ ↦ (⟨t,y⟩:ℂ)) x := by
        simp only [Complex.mk_eq_add_mul_I]; fun_prop
      exact (c.comp (f:=fun t : ℝ ↦ (⟨t,y⟩:ℂ)) g).continuousWithinAt
  have v x (hx : |x|=3) : I*(∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨x,y⟩) =
      F ⟨x,Real.pi⟩-F ⟨x,-Real.pi⟩ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun y : ℝ ↦ F ⟨x,y⟩)
    · intro y hy
      have hd := d ⟨x,y⟩ (in_vert hx hy)
      rw [Complex.mk_eq_add_mul_I] at hd
      have g := (hd.comp (y:ℂ) (((hasDerivAt_id (y:ℂ)).mul_const I).const_add (x:ℂ))).comp_ofReal
      simpa [Complex.mk_eq_add_mul_I, Function.comp_def, mul_comm] using g
    · apply ContinuousOn.intervalIntegrable
      intro y hy
      have c := cont _ (in_vert hx hy)
      have g : ContinuousAt (fun t : ℝ ↦ (⟨x,t⟩:ℂ)) y := by
        simp only [Complex.mk_eq_add_mul_I]; fun_prop
      exact (continuousAt_const.mul (c.comp (f:=fun t : ℝ ↦ (⟨x,t⟩:ℂ)) g)).continuousWithinAt
  rw [rectIntegral,h _ (by simp [abs_of_pos Real.pi_pos]),h _ (abs_of_pos Real.pi_pos),
    mul_sub,v _ (by norm_num), v _ (by norm_num)]
  ring

end
end OrderedPartitions.TwoPole
