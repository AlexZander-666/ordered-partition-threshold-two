import OrderedPartitions.TwoPoleSubtraction
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Constructions

/-! Exact coefficient extraction for the two poles and the previously bounded rectangular integral. -/
namespace OrderedPartitions.TwoPole
open Complex Set Filter
open scoped Topology ComplexConjugate
noncomputable section

private theorem pole_series (a A : ℂ) (an : a≠0) :
    HasFPowerSeriesAt (fun z : ℂ ↦ A*(z-a)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ -A/a^(m+1)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (norm_pos_iff.mpr an)] with z hz
  have lt : ‖z‖<‖a‖ := by simpa using hz
  have za : z - a ≠ 0 := sub_ne_zero.mpr (fun e ↦ lt.ne (congrArg norm e))
  have small : ‖z/a‖<1 := by rw [norm_div, div_lt_one (norm_pos_iff.mpr an)]; exact lt
  convert! (hasSum_geometric_of_norm_lt_one small).mul_left (-A/a) using 1
  · ext m
    rw [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, div_pow, pow_succ]
    field_simp
  · rw [zero_add, show 1-z/a = -(z-a)/a by field_simp; ring]
    field_simp

/-- Rectangular residue formula for a reciprocal with two simple poles. -/
theorem taylor_two_residues {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Strip) {a b : ℂ}
    (ha : a∈Strip) (hb : b∈Strip) (ar : ‖a‖<3) (br : ‖b‖<3) (an : a≠0) (bn : b≠0)
    (ab : a≠b) (ga : g a=0) (gb : g b=0) (da : deriv g a≠0) (db : deriv g b≠0)
    (onlyZeros : ∀ z∈Strip, g z=0 → z=a ∨ z=b) (n : ℕ) :
    taylor n (fun w : ℂ ↦ (g w)⁻¹) =
      rectIntegral (fun w : ℂ ↦ (w^(n+1)*g w)⁻¹)/(2*(Real.pi:ℂ)*I) -
        (deriv g a)⁻¹/a^(n+1) - (deriv g b)⁻¹/b^(n+1) := by
  obtain ⟨H,hH,split⟩ := remove_two hg ha hb ab ga gb da db onlyZeros
  let A := (deriv g a)⁻¹
  let B := (deriv g b)⁻¹
  let F (w : ℂ) := (g w)⁻¹
  have germ : (fun w : ℂ ↦ H w + A*(w-a)⁻¹ + B*(w-b)⁻¹) =ᶠ[𝓝 0] F := by
    filter_upwards [strip_open.mem_nhds strip_zero, isOpen_ne.mem_nhds an.symm,
      isOpen_ne.mem_nhds bn.symm] with z hs za zb
    exact (split z hs za zb).symm
  have anH : AnalyticAt ℂ H 0 := (hH.analyticAt (strip_open.mem_nhds strip_zero))
  obtain ⟨p,hp⟩ := anH
  have hP := ((hp.add (pole_series a A an)).add (pole_series b B bn)).congr germ
  have coeff := taylor_of_series hP n
  change taylor n F = p.coeff n +
    (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ -A/a^(m+1))).coeff n +
    (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ -B/b^(m+1))).coeff n at coeff
  rw [FormalMultilinearSeries.coeff_ofScalars, FormalMultilinearSeries.coeff_ofScalars,
    ←taylor_of_series hp n] at coeff
  let partH (w : ℂ) := H w / w^(n+1)
  let part (c R w : ℂ) := R*((w-c)⁻¹/w^(n+1))
  have cd : RegularOnBoundary partH := fun w hw ↦ (regular_of_holo hH _ hw).div
    (continuousAt_id.pow _) (pow_ne_zero _ (boundary_ne_zero hw))
  have cp c (cr : ‖c‖<3) R : RegularOnBoundary (part c R) := fun _ h ↦
    continuousAt_const.mul ((kernel_regular cr _ h).div (continuousAt_id.pow _)
      (pow_ne_zero _ (boundary_ne_zero h)))
  have eq := rect_congr (f:=fun w : ℂ ↦ (w^(n+1)*g w)⁻¹)
    (g:=fun w : ℂ ↦ partH w + part a A w + part b B w) (fun w hw ↦ ?_)
  · rw [rect_add (f:=fun z ↦ partH z+part a A z) (fun z h ↦ (cd z h).add (cp a ar A z h)) (cp b br B),
      rect_add cd (cp a ar A)] at eq
    have pa : rectIntegral (part a A)=0 := by
      dsimp only [part]; rw [rect_scale,polar_integral_zero ar an,mul_zero]
    have pb : rectIntegral (part b B)=0 := by
      dsimp only [part]; rw [rect_scale,polar_integral_zero br bn,mul_zero]
    rw [pa,pb,add_zero,add_zero] at eq
    change _ = rectIntegral (fun z : ℂ ↦ H z / z^(n+1)) at eq
    rw [rect_taylor H hH n] at eq
    have pi0 : (2*(Real.pi:ℂ)*I)≠0 := by
      have re : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      exact mul_ne_zero (mul_ne_zero (by norm_num) re) Complex.I_ne_zero
    rw [eq,mul_div_cancel_right₀ _ pi0]
    simpa [F,A,B,sub_eq_add_neg,neg_div] using coeff
  · have za := sub_ne_zero.mp (boundary_sub_ne ar hw)
    have zb := sub_ne_zero.mp (boundary_sub_ne br hw)
    rw [mul_inv_rev,split w (boundary_strip hw) za zb]
    dsimp [partH,part,A,B]; ring

/-- The coefficient of the reciprocal of the actual nonsingleton-block denominator. -/
theorem taylor_residues {q : ℝ} (hq : 0<q) (h1 : q<1) (crit : -1<Real.log q+(1-2*q))
    {z : ℂ} (gz : G q z=0) (iz : z.im∈Ioo 0 (Real.pi/2)) (n : ℕ) :
    taylor n (fun w : ℂ ↦ (G q w)⁻¹) = contour q n -
      (deriv (G q) z)⁻¹/z^(n+1) - (deriv (G q) (conj z))⁻¹/(conj z)^(n+1) := by
  have all := principal_bounds (sixth_lt_of_critical hq crit) h1 gz iz
  have rs : ‖z‖<3 := by linarith [all.2.2.1]
  have zs : z∈Strip := by change |z.im|<2*Real.pi; rw [abs_of_pos iz.1]; linarith [iz.2,Real.pi_pos]
  have zn : z≠0 := fun e ↦ iz.1.ne' (by simp [e])
  have ca : z≠conj z := by
    intro e
    have eq := congrArg Complex.im e
    simp only [Complex.conj_im] at eq
    linarith [iz.1]
  have gc : G q (conj z)=0 := by simp [G_conj,gz]
  have dc : deriv (G q) (conj z) ≠ 0 := by
    rw [(derivative_at_zero gc).deriv]
    intro e
    have eq := congrArg Complex.im e
    simp at eq
    linarith [iz.1]
  exact taylor_two_residues (fun w _ ↦ (derivative_G q w).differentiableAt.differentiableWithinAt)
    zs (by simpa [Strip] using zs) rs (by simpa using rs) zn (by simpa using zn) ca gz gc
    all.2.2.2.1 dc (fun _ hw gw ↦ zeros_in_strip hq crit gz iz hw gw) n

end
end OrderedPartitions.TwoPole
