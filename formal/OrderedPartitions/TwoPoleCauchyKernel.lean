import OrderedPartitions.TwoPoleWinding
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! Cauchy kernel identities on this rectangle, including exterior Taylor moments. -/

namespace OrderedPartitions.TwoPole
open Complex Set
noncomputable section

theorem rect_add {f g : ℂ → ℂ} (cf : RegularOnBoundary f) (cg : RegularOnBoundary g) :
    rectIntegral (fun z ↦ f z+g z)=rectIntegral f+rectIntegral g := by
  have eq := rect_sub (f:=fun z ↦ f z+g z) (g:=g) (fun z h ↦ (cf z h).add (cg z h)) cg
  simp only [add_sub_cancel_right] at eq
  linear_combination -eq

theorem boundary_sub_ne {a z : ℂ} (ha : ‖a‖<3) (h : Boundary z) : z-a≠0 :=
  sub_ne_zero.mpr (fun e ↦ (not_lt_of_ge (boundary_norm h)) (e ▸ ha))

theorem kernel_regular {a : ℂ} (ha : ‖a‖<3) : RegularOnBoundary (fun z : ℂ ↦ (z-a)⁻¹) :=
  fun _ h ↦ (continuousAt_id.sub continuousAt_const).inv₀ (boundary_sub_ne ha h)

theorem winding_small {a : ℂ} (ha : ‖a‖<3) :
    rectIntegral (fun z : ℂ ↦ (z-a)⁻¹) = 2*(Real.pi:ℂ)*I := by
  have c : RegularOnBoundary (fun z : ℂ ↦ z⁻¹) := fun _ h ↦ continuousAt_id.inv₀ (boundary_ne_zero h)
  have diff := rect_primitive (fun z : ℂ ↦ Complex.log (1-a/z))
    (fun z : ℂ ↦ (z-a)⁻¹-z⁻¹) (fun z h ↦ ?_)
    (fun z h ↦ (kernel_regular ha z h).sub (c z h))
  · rw [rect_sub (kernel_regular ha) c, winding_origin, sub_eq_zero] at diff
    exact diff
  have zn := boundary_ne_zero h
  have an : z-a≠0 := boundary_sub_ne ha h
  have nor : ‖a/z‖<1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr zn)]
    exact ha.trans_le (boundary_norm h)
  have slit : 1-a/z ∈ slitPlane := by
    simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one (z:=-(a/z)) (by simpa using nor)
  have hd := (Complex.hasDerivAt_log slit).comp z
    ((hasDerivAt_const z (1:ℂ)).sub ((hasDerivAt_const z a).div (hasDerivAt_id z) zn))
  convert! hd using 1
  simp only [id_eq]
  have non : 1-a/z≠0 := Complex.slitPlane_ne_zero slit
  field_simp
  ring

theorem winding_higher (n : ℕ) : rectIntegral (fun z : ℂ ↦ (z^(n+2))⁻¹) = 0 := by
  apply rect_primitive (fun z : ℂ ↦ -(z^(n+1))⁻¹ / (n+1:ℕ))
  · intro z h
    have zn := boundary_ne_zero h
    have pn : z^(n+1)≠0 := pow_ne_zero _ zn
    have hp := ((((hasDerivAt_id z).pow (n+1)).inv pn).neg.div_const ((n+1:ℕ):ℂ))
    convert! hp using 1
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one]
    have kn : (n:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [show n+2 = n+1+1 by omega, pow_succ, pow_succ]
    field_simp
  · intro z h
    exact (continuousAt_id.pow _).inv₀ (pow_ne_zero _ (boundary_ne_zero h))

theorem polar_integral_zero {a : ℂ} (ha : ‖a‖<3) (an : a≠0) (n : ℕ) :
    rectIntegral (fun z : ℂ ↦ (z-a)⁻¹ / z^(n+1))=0 := by
  have cr := kernel_regular ha
  have cz : ∀ m : ℕ, RegularOnBoundary (fun z : ℂ ↦ (z^m)⁻¹) :=
    fun m _ h ↦ (continuousAt_id.pow m).inv₀ (pow_ne_zero _ (boundary_ne_zero h))
  induction n with
  | zero =>
    have e := rect_sub cr (cz 1)
    simp only [pow_one] at e
    rw [winding_small ha, winding_origin, sub_self] at e
    calc
      _ = rectIntegral (fun z : ℂ ↦ a⁻¹*((z-a)⁻¹-z⁻¹)) := by
        apply rect_congr
        intro z h
        have zn := boundary_ne_zero h
        have hn := boundary_sub_ne ha h
        simp only [zero_add,pow_one]; field_simp; ring
      _ = 0 := by rw [rect_scale, e, mul_zero]
  | succ n ih =>
    have cf : RegularOnBoundary (fun z : ℂ ↦ (z-a)⁻¹ / z^(n+1)) :=
      fun _ h ↦ (cr _ h).div (continuousAt_id.pow _) (pow_ne_zero _ (boundary_ne_zero h))
    calc
      _ = rectIntegral (fun z : ℂ ↦ a⁻¹*((z-a)⁻¹/z^(n+1) - (z^(n+2))⁻¹)) := by
        apply rect_congr
        intro z h
        have zn := boundary_ne_zero h
        have hn := boundary_sub_ne ha h
        rw [pow_succ z (n+1)]
        field_simp
        ring
      _ = 0 := by rw [rect_scale,rect_sub cf (cz _),ih,winding_higher,sub_zero,mul_zero]

end
end OrderedPartitions.TwoPole
