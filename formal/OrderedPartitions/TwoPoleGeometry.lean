import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Complex denominator and positive-height parametrization for ordered nonsingleton blocks. -/

namespace OrderedPartitions.TwoPole
open Set
noncomputable section

/-- After the substitution t=-q/(1-q), the original analytic denominator times 1-q. -/
def G (q : ℝ) (z : ℂ) : ℂ := 1 - 2*(q : ℂ) - z + q*Complex.exp z

/-- Height of the upper pole is determined by this increasing real function. -/
def height (v : ℝ) : ℝ := Real.log (v / Real.sin v) - v*Real.cos v / Real.sin v

theorem re_G (q : ℝ) (z : ℂ) :
    (G q z).re = 1-2*q-z.re+q*Real.exp z.re*Real.cos z.im := by
  simp [G, Complex.exp_re, mul_assoc]

theorem im_G (q : ℝ) (z : ℂ) :
    (G q z).im = -z.im+q*Real.exp z.re*Real.sin z.im := by
  simp [G, Complex.exp_im, mul_assoc]

theorem derivative_G (q : ℝ) (z : ℂ) :
    HasDerivAt (G q) (-1+(q : ℂ)*Complex.exp z) z := by
  convert! ((hasDerivAt_const z (1-2*(q : ℂ))).sub (hasDerivAt_id z)).add
    ((Complex.hasDerivAt_exp z).const_mul (q : ℂ)) using 1
  simp

theorem derivative_at_zero {q : ℝ} {z : ℂ} (hz : G q z = 0) :
    HasDerivAt (G q) (z + 2*q - 2) z := by
  have e : -1+(q : ℂ)*Complex.exp z = z+2*q-2 := by
    unfold G at hz
    linear_combination hz
  rw [← e]
  exact derivative_G _ _

/-- A strip zero and the real height equation determine one another. -/
theorem zero_iff {q : ℝ} (hq : 0 < q) {z : ℂ} (hv : 0 < z.im) (hs : 0 < Real.sin z.im) :
    G q z = 0 ↔ z.re = 1-2*q + z.im * Real.cos z.im / Real.sin z.im ∧
      height z.im = Real.log q + (1-2*q) := by
  have sn := hs.ne'
  have qn := hq.ne'
  constructor
  · intro h
    have hR := congrArg Complex.re h
    have hI := congrArg Complex.im h
    rw [re_G] at hR
    rw [im_G] at hI
    simp only [Complex.zero_re, Complex.zero_im] at hR hI
    have he : z.im / Real.sin z.im = q * Real.exp z.re :=
      (div_eq_iff sn).2 (by linarith)
    have hx : z.re = 1-2*q + z.im * Real.cos z.im / Real.sin z.im := by
      calc
        _ = 1-2*q + (q * Real.exp z.re) * Real.cos z.im := by linarith
        _ = _ := by rw [← he]; ring
    refine ⟨hx, ?_⟩
    unfold height
    rw [he, Real.log_mul qn (Real.exp_pos _).ne', Real.log_exp]
    linarith
  · rintro ⟨hx, h⟩
    have hlog : Real.log (z.im / Real.sin z.im) = Real.log q + z.re := by
      unfold height at h
      linarith
    have he := congrArg Real.exp hlog
    rw [Real.exp_log (div_pos hv hs), Real.exp_add, Real.exp_log hq] at he
    apply Complex.ext
    · rw [re_G, ←he, Complex.zero_re]
      linear_combination -hx
    · rw [im_G, ←he, div_mul_cancel₀ _ sn, Complex.zero_im]
      ring

/-- Uniform exclusion of a real zero throughout the oscillatory range. -/
theorem real_axis {q : ℝ} (hq : 0 < q) (critical : -1 < Real.log q + (1-2*q)) (x : ℝ) :
    0 < (G q x).re := by
  rw [re_G]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Real.cos_zero, mul_one]
  have h := Real.add_one_le_exp (Real.log q + x)
  rw [Real.exp_add, Real.exp_log hq] at h
  linarith

/-- Exact differential identity for the height. -/
theorem height_deriv {v : ℝ} (hv : 0 < v) (hs : 0 < Real.sin v) :
    HasDerivAt height (((1-v*Real.cos v / Real.sin v)^2+v^2)/v) v := by
  have hz := hs.ne'
  have h := (((hasDerivAt_id v).div (Real.hasDerivAt_sin v) hz).log (div_ne_zero hv.ne' hz)).sub
    ((((hasDerivAt_id v).mul (Real.hasDerivAt_cos v)).div (Real.hasDerivAt_sin v) hz))
  convert! h using 1
  simp only [Pi.div_apply, Pi.mul_apply, id_eq]
  field_simp
  ring

theorem height_strictMono : StrictMonoOn height (Ioo 0 Real.pi) := by
  have d : ∀ v ∈ Ioo 0 Real.pi, HasDerivAt height
      (((1-v*Real.cos v / Real.sin v)^2+v^2)/v) v :=
    fun v hv ↦ height_deriv hv.1 (Real.sin_pos_of_pos_of_lt_pi hv.1 hv.2)
  apply strictMonoOn_of_deriv_pos (convex_Ioo ..) (fun v hv ↦ (d v hv).continuousAt.continuousWithinAt)
  intro v hv
  rw [interior_Ioo] at hv
  rw [(d v hv).deriv]
  have : 0 < v := hv.1
  positivity

/-- At most one upper zero has imaginary part below pi. -/
theorem upper_unique {q : ℝ} (hq : 0 < q) {z w : ℂ}
    (hz : G q z = 0) (hw : G q w = 0) (iz : z.im ∈ Ioo 0 Real.pi)
    (iw : w.im ∈ Ioo 0 Real.pi) : z = w := by
  obtain ⟨xz, kz⟩ := (zero_iff hq iz.1 (Real.sin_pos_of_pos_of_lt_pi iz.1 iz.2)).mp hz
  obtain ⟨xw, kw⟩ := (zero_iff hq iw.1 (Real.sin_pos_of_pos_of_lt_pi iw.1 iw.2)).mp hw
  have i := height_strictMono.injOn iz iw (kz.trans kw.symm)
  exact Complex.ext (by rw [xz, xw, i]) i

end
end OrderedPartitions.TwoPole
