import OrderedPartitions.TwoPoleCauchyKernel
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Cauchy's formula for every Taylor coefficient, on exactly the rectangle used in the bounds. -/

namespace OrderedPartitions.TwoPole
open Complex Set Filter Function
open scoped Topology
noncomputable section

def Strip : Set ℂ := {z | |z.im| < 2*Real.pi}

theorem strip_open : IsOpen Strip := isOpen_lt (continuous_im.abs) continuous_const

theorem strip_zero : (0:ℂ) ∈ Strip := by simp [Strip, Real.pi_pos]

theorem boundary_strip {z : ℂ} (h : Boundary z) : z ∈ Strip := by
  change |z.im| < 2*Real.pi
  rcases h with h | h <;> linarith [h.1,h.2,Real.pi_pos]

theorem regular_of_holo {f : ℂ → ℂ} (h : DifferentiableOn ℂ f Strip) : RegularOnBoundary f :=
  fun _ hb ↦ (h.differentiableAt (strip_open.mem_nhds (boundary_strip hb))).continuousAt

theorem rect_holo {f : ℂ → ℂ} (h : DifferentiableOn ℂ f Strip) : rectIntegral f=0 := by
  have b := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (⟨-3,-Real.pi⟩:ℂ) (⟨3,Real.pi⟩:ℂ) (h.mono (by
      intro z hz
      have hyp := hz.2
      change z.im ∈ uIcc (-Real.pi) Real.pi at hyp
      rw [uIcc_of_le (by linarith [Real.pi_pos])] at hyp
      exact (abs_le.2 hyp).trans_lt (by linarith [Real.pi_pos])))
  simpa [rectIntegral, Complex.mk_eq_add_mul_I, mul_sub, smul_eq_mul, sub_eq_add_neg, add_assoc, mul_add]
    using b

/-- Taylor coefficient extracted with iterated divided differences. -/
def taylor (n : ℕ) (f : ℂ → ℂ) : ℂ := (swap dslope 0)^[n] f 0

theorem taylor_of_series {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (h : HasFPowerSeriesAt f p 0) (n : ℕ) : taylor n f = p.coeff n := by
  have e := (h.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1
  change ((swap dslope 0)^[n] f 0) = p.coeff n
  rw [← e]
  change (FormalMultilinearSeries.fslope^[n] p).coeff 0 = _
  rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add]

theorem taylor_succ (n : ℕ) (f : ℂ → ℂ) : taylor (n+1) f=taylor n (dslope f 0) := rfl

theorem rect_taylor (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Strip) (n : ℕ) :
    rectIntegral (fun z : ℂ ↦ f z / z^(n+1)) = taylor n f * (2*(Real.pi:ℂ)*I) := by
  induction n generalizing f with
  | zero =>
    have hd := (Complex.differentiableOn_dslope (strip_open.mem_nhds strip_zero)).2 hf
    have cw : RegularOnBoundary (fun z : ℂ ↦ f 0*z⁻¹) := fun _ hb ↦
      continuousAt_const.mul (continuousAt_id.inv₀ (boundary_ne_zero hb))
    calc
      _ = rectIntegral (fun z : ℂ ↦ dslope f 0 z + f 0*z⁻¹) := by
        apply rect_congr
        intro z hb
        have zn := boundary_ne_zero hb
        have h := sub_smul_dslope f 0 z
        simp only [sub_zero, smul_eq_mul] at h
        simp only [zero_add,pow_one]
        field_simp
        linear_combination -h
      _ = _ := by rw [rect_add (regular_of_holo hd) cw,rect_holo hd,rect_scale,winding_origin,zero_add]; rfl
  | succ n ih =>
    have hd := (Complex.differentiableOn_dslope (strip_open.mem_nhds strip_zero)).2 hf
    have cw : RegularOnBoundary (fun z : ℂ ↦ f 0*(z^(n+2))⁻¹) := fun _ hb ↦
      continuousAt_const.mul ((continuousAt_id.pow _).inv₀ (pow_ne_zero _ (boundary_ne_zero hb)))
    have cs : RegularOnBoundary (fun z : ℂ ↦ dslope f 0 z / z^(n+1)) := fun _ hb ↦
      (regular_of_holo hd _ hb).div (continuousAt_id.pow _) (pow_ne_zero _ (boundary_ne_zero hb))
    calc
      _ = rectIntegral (fun z : ℂ ↦ dslope f 0 z / z^(n+1) + f 0*(z^(n+2))⁻¹) := by
        apply rect_congr
        intro z hb
        have zn := boundary_ne_zero hb
        have h := sub_smul_dslope f 0 z
        simp only [sub_zero, smul_eq_mul] at h
        rw [pow_succ z (n+1)]
        field_simp
        linear_combination -h
      _ = _ := by rw [rect_add cs cw, rect_scale,winding_higher,mul_zero,add_zero,ih _ hd,taylor_succ]

end
end OrderedPartitions.TwoPole
