import OrderedPartitions.TwoPoleAngles
import OrderedPartitions.TwoPoleOriginalTaylor
import OrderedPartitions.TwoPoleResidues
import OrderedPartitions.TwoPoleTwoSteps

/-! The real cosine model obtained from the conjugate principal residues. -/

noncomputable section
namespace OrderedPartitions.TwoPole
open Complex Polynomial
open scoped ComplexConjugate

/-- The common normalization in the contour error and the cosine amplitude. -/
def poleMass (n : ℕ) (q : ℝ) : ℝ :=
  ‖deriv (G q) (upperPole q)‖ * ‖upperPole q‖^(n+1) / 2

/-- The scale multiplying the true row. -/
def rowScale (n : ℕ) (q : ℝ) : ℝ :=
  poleMass n q / ((1-q)*(n.factorial:ℝ))

/-- The real part of the normalized contour remainder. -/
def realError (n : ℕ) (q : ℝ) : ℝ :=
  poleMass n q * (contour q n).re

private theorem upperPole_data {q : ℝ} (hq : 1/6 < q) (h1 : q < 1) (osc : -1 < level q) :
    upperPole q ≠ 0 ∧ deriv (G q) (upperPole q) ≠ 0 := by
  have sp := upperPole_spec (by linarith : 0 < q) osc
  refine ⟨fun z ↦ sp.2.1.ne' (by simp [z]), (principal_bounds hq h1 sp.1 sp.2).2.2.2.1⟩

private theorem poleMass_pos {q : ℝ} (hq : 1/6 < q) (h1 : q < 1) (osc : -1 < level q)
    (n : ℕ) : 0 < poleMass n q := by
  obtain ⟨z, d⟩ := upperPole_data hq h1 osc
  unfold poleMass
  exact div_pos (mul_pos (norm_pos_iff.mpr d) (pow_pos (norm_pos_iff.mpr z) _)) (by norm_num)

theorem rowScale_pos {q : ℝ} (hq : 1/6 < q) (h1 : q < 1) (osc : -1 < level q) (n : ℕ) :
    0 < rowScale n q := by
  apply div_pos (poleMass_pos hq h1 osc n)
  exact mul_pos (sub_pos.mpr h1) (by positivity)

private theorem inverse_product_re {w z : ℂ} (wn : w ≠ 0) (zn : z ≠ 0) (m : ℕ) :
    ((w*z^m)⁻¹).re =
      Real.cos ((m:ℝ)*z.arg+w.arg) / (‖w‖*‖z‖^m) := by
  let s := ‖w‖*‖z‖^m
  have sp : 0 < s := mul_pos (norm_pos_iff.mpr wn) (pow_pos (norm_pos_iff.mpr zn) _)
  have zp : z^m = (↑‖z‖:ℂ)^m * exp ((m:ℂ)*(↑z.arg*I)) := by
    rw [Complex.exp_nat_mul, ← mul_pow, Complex.norm_mul_exp_arg_mul_I]
  have polar : w*z^m = (s:ℂ)*exp (↑((m:ℝ)*z.arg+w.arg)*I) := by
    calc
      w*z^m = (↑‖w‖:ℂ) * exp (↑w.arg*I) *
          ((↑‖z‖:ℂ)^m * exp ((m:ℂ)*(↑z.arg*I))) := by
            rw [Complex.norm_mul_exp_arg_mul_I, zp]
      _ = _ := by
        simp only [s, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
          Complex.ofReal_natCast, add_mul, mul_assoc, Complex.exp_add]
        ring
  have re : (w*z^m).re = s * Real.cos ((m:ℝ)*z.arg+w.arg) := by
    rw [polar, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_re]
    simp
  have norm_eq : ‖w*z^m‖ = s := by rw [norm_mul, norm_pow]
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq, norm_eq, re]
  field_simp [sp.ne']
  dsimp [s]
  ring

private theorem conjugate_simple_pole {q : ℝ} {z : ℂ} (hz : G q z = 0) (n : ℕ) :
    (deriv (G q) (conj z))⁻¹ / (conj z)^(n+1) =
      conj ((deriv (G q) z)⁻¹ / z^(n+1)) := by
  have zero : G q (conj z) = 0 := by simp [G_conj, hz]
  rw [(derivative_at_zero zero).deriv, (derivative_at_zero hz).deriv]
  simp [map_ofNat]

/-- Taking the real part of the exact two-residue formula gives a normalized
cosine with a real residual, at the true negative polynomial argument. -/
theorem cosine_model_of_residues {q : ℝ} (hq : 1/6<q) (h1 : q<1) (osc : -1<level q) (n : ℕ)
    (residues : taylor n (fun z : ℂ ↦ (G q z)⁻¹) =
      contour q n - (deriv (G q) (upperPole q))⁻¹/(upperPole q)^(n+1) -
        (deriv (G q) (conj (upperPole q)))⁻¹/(conj (upperPole q))^(n+1)) :
    rowScale n q*(row n 2).eval (-q/(1-q)) = -Real.cos (phase n q)+realError n q := by
  let z := upperPole q
  let w := deriv (G q) z
  let s := ‖w‖ * ‖z‖^(n+1)
  obtain ⟨zn, wn⟩ := upperPole_data hq h1 osc
  have sp : 0 < s := mul_pos (norm_pos_iff.mpr wn) (pow_pos (norm_pos_iff.mpr zn) _)
  have gz : G q z = 0 := (upperPole_spec (by linarith : 0<q) osc).1
  have val : taylor n (fun z : ℂ ↦ (G q z)⁻¹) =
      ↑((row n 2).eval (-q/(1-q)) / ((1-q)*(n.factorial:ℝ))) := by
    change ((fun f : ℂ → ℂ ↦ dslope f 0)^[n] (fun z : ℂ ↦ (G q z)⁻¹)) 0 = _
    push_cast
    exact iterate_dslope_inv_G_at_zero h1 n
  rw [conjugate_simple_pole gz n, val] at residues
  have re := congrArg Complex.re residues
  have principal : (w⁻¹/z^(n+1)).re = Real.cos (phase n q)/s := by
    have warg : w.arg = beta q := by
      rw [show w = z + 2*(q:ℂ)-2 from (derivative_at_zero gz).deriv]
      rfl
    rw [div_eq_mul_inv, ← mul_inv, inverse_product_re wn zn, warg, phase, theta]
    push_cast
    rfl
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.conj_re] at re
  change _ = (contour q n).re - (w⁻¹/z^(n+1)).re - (w⁻¹/z^(n+1)).re at re
  rw [principal] at re
  unfold rowScale realError poleMass
  change s/2/((1-q)*(n.factorial:ℝ)) * (row n 2).eval (-q/(1-q)) =
    -Real.cos (phase n q) + s/2*(contour q n).re
  calc
    _ = s/2*((row n 2).eval (-q/(1-q))/((1-q)*(n.factorial:ℝ))) := by ring
    _ = _ := by rw [re]; field_simp [sp.ne']; ring

/-- The exact real model for every oscillatory parameter. -/
theorem cosine_model {q : ℝ} (hq : 1/6<q) (h1 : q<1) (osc : -1<level q) (n : ℕ) :
    rowScale n q*(row n 2).eval (-q/(1-q)) = -Real.cos (phase n q)+realError n q := by
  have nonneg : 0 < q := by linarith
  obtain ⟨hz, iz⟩ := upperPole_spec nonneg osc
  exact cosine_model_of_residues hq h1 osc n (taylor_residues nonneg h1 osc hz iz n)

private theorem error_le_contour {q : ℝ} (hq : 1/6<q) (h1 : q<1) (osc : -1<level q) (n : ℕ) :
    |realError n q| ≤ poleMass n q * ‖contour q n‖ := by
  rw [realError, abs_mul, abs_of_pos (poleMass_pos hq h1 osc n)]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (poleMass_pos hq h1 osc n).le

theorem realError_one {q : ℝ} (hq : 1/6<q) (h1 : q<1) (osc : -1<level q) {n : ℕ}
    (hn : 20≤n) : |realError n q| ≤ Real.sin (theta q)/4 := by
  have spec := upperPole_spec (by linarith : 0<q) osc
  exact (error_le_contour hq h1 osc n).trans
    (relative_one_of_twenty hq h1 spec.1 spec.2 hn)

theorem realError_two {q : ℝ} (hq : 1/6<q) (h1 : q<1) (osc : -1<level q) {n : ℕ}
    (hn : 25≤n) : |realError n q| ≤ Real.sin (2*theta q)/8 := by
  have spec := upperPole_spec (by linarith : 0<q) osc
  exact (error_le_contour hq h1 osc n).trans
    (relative_two_of_twentyfive hq h1 spec.1 spec.2 hn)

#print axioms rowScale_pos
#print axioms cosine_model_of_residues
#print axioms cosine_model
#print axioms realError_one
#print axioms realError_two

end OrderedPartitions.TwoPole
