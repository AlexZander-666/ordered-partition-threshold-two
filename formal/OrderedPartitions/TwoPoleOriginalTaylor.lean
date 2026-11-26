import OrderedPartitions.OriginalEGF
import OrderedPartitions.TwoPoleGeometry
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The analytic reciprocal at zero and the original ordered-partition rows. -/

noncomputable section
namespace OrderedPartitions.TwoPole
open Complex Polynomial Finset
open scoped Topology

private def taylorAtZero (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n ↦ iteratedDeriv n f 0 / n.factorial)

private theorem coeff_taylorAtZero (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (taylorAtZero f) = iteratedDeriv n f 0 / n.factorial := by
  simp [taylorAtZero]

private theorem taylor_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorAtZero (fun z ↦ f z * g z) = taylorAtZero f * taylorAtZero g := by
  ext n
  rw [coeff_taylorAtZero, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, sum_div]
  apply sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  simp only [coeff_taylorAtZero]
  rw [Nat.cast_choose ℂ hin]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

private theorem taylor_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) :
    taylorAtZero f = taylorAtZero g := by
  ext n
  simp only [coeff_taylorAtZero, h.iteratedDeriv_eq n]

private theorem taylor_const_one : taylorAtZero (fun _ ↦ 1) = 1 := by
  ext n
  cases n <;> simp [coeff_taylorAtZero, PowerSeries.coeff_one, iteratedDeriv_const]

private def denominator (q : ℝ) : PowerSeries ℂ :=
  PowerSeries.C (1-2*(q:ℂ)) - PowerSeries.X + PowerSeries.C (q:ℂ)*PowerSeries.exp ℂ

private theorem analytic_G (q : ℝ) : AnalyticAt ℂ (G q) 0 := by
  unfold G
  fun_prop

private theorem G_at_zero (q : ℝ) : G q 0 = 1-(q:ℂ) := by
  simp [G]
  ring

private theorem taylor_G (q : ℝ) : taylorAtZero (G q) = denominator q := by
  ext n
  rw [coeff_taylorAtZero]
  have expDeriv : iteratedDeriv n Complex.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp, Complex.exp_zero]
  have mulDeriv : iteratedDeriv n (fun z ↦ (q:ℂ)*Complex.exp z) 0 =
      (q:ℂ)*iteratedDeriv n Complex.exp 0 := iteratedDeriv_const_mul_field _ _
  unfold G
  rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_sub (by fun_prop) (by fun_prop), mulDeriv,
    iteratedDeriv_fun_id_zero, expDeriv]
  cases n with
  | zero =>
    simp [denominator]
  | succ n =>
    cases n with
    | zero =>
      simp [denominator, PowerSeries.coeff_X, PowerSeries.coeff_exp, iteratedDeriv_const]
    | succ n =>
      simp [denominator, PowerSeries.coeff_X, PowerSeries.coeff_exp, iteratedDeriv_const, div_eq_mul_inv]

private theorem denominator_constant (q : ℝ) :
    PowerSeries.constantCoeff (denominator q) = 1-(q:ℂ) := by
  rw [← taylor_G, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_taylorAtZero]
  simp [G_at_zero]

private theorem taylor_inv_G {q : ℝ} (hq : q < 1) :
    taylorAtZero (fun z ↦ (G q z)⁻¹) = (denominator q)⁻¹ := by
  have hn : (1:ℂ)-(q:ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hq.ne')
  refine (PowerSeries.eq_inv_iff_mul_eq_one ((denominator_constant q).trans_ne hn)).mpr ?_
  have an : AnalyticAt ℂ (fun z ↦ (G q z)⁻¹) 0 :=
    (analytic_G q).inv ((G_at_zero q).trans_ne hn)
  rw [← taylor_G, ← taylor_mul an (analytic_G q), ← taylor_const_one]
  apply taylor_congr
  filter_upwards [(analytic_G q).continuousAt.eventually_ne ((G_at_zero q).trans_ne hn)] with z nz
  exact inv_mul_cancel₀ nz

private theorem sizeSeries_two :
    sizeSeries 2 = PowerSeries.exp ℝ - 1 - PowerSeries.X := by
  ext n
  simp only [map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_one, PowerSeries.coeff_X,
    sizeSeries, PowerSeries.coeff_mk]
  rcases n with _ | _ | n <;> simp

private def mark (q : ℝ) : ℝ := -q/(1-q)

private def originalDenominator (q : ℝ) : PowerSeries ℝ :=
  2-PowerSeries.exp ℝ-PowerSeries.C (mark q-1)*sizeSeries 2

private theorem originalDenominator_constant (q : ℝ) :
    PowerSeries.constantCoeff (originalDenominator q) = 1 := by
  simp [originalDenominator, sizeSeries_two, show (2 : PowerSeries ℝ) = 1+1 by norm_num]

private theorem denominator_eq {q : ℝ} (hq : q < 1) :
    denominator q = PowerSeries.C (1-(q:ℂ)) *
      PowerSeries.map Complex.ofRealHom (originalDenominator q) := by
  have hfield : (1:ℂ)-(q:ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hq.ne')
  have shift : (1-(q:ℂ))*((mark q-1:ℝ):ℂ) = -1 := by
    push_cast [mark]
    field_simp [hfield]
    ring
  have mulC : PowerSeries.C (1-(q:ℂ)) * PowerSeries.C ((mark q-1:ℝ):ℂ) =
      (-1:PowerSeries ℂ) := by rw [← map_mul, shift, map_neg, map_one]
  have startC : PowerSeries.C (1-2*(q:ℂ)) = 1-2*PowerSeries.C (q:ℂ) := by
    rw [map_sub, map_mul, map_one, map_ofNat]
  simp only [map_sub, map_one, Complex.ofReal_sub, Complex.ofReal_one] at mulC
  simp only [denominator, originalDenominator, sizeSeries_two, map_sub, map_mul, map_one,
    map_ofNat, PowerSeries.map_C, PowerSeries.map_exp, PowerSeries.map_X,
    Complex.ofRealHom_eq_coe, startC]
  rw [mul_sub, ← mul_assoc, mulC]
  ring

private theorem inverse_eq_original {q : ℝ} (hq : q < 1) :
    (denominator q)⁻¹ = PowerSeries.C ((1-(q:ℂ))⁻¹) *
      PowerSeries.map Complex.ofRealHom (originalEGF 2 (mark q)) := by
  have hfield : (1:ℂ)-(q:ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hq.ne')
  apply ((PowerSeries.eq_inv_iff_mul_eq_one ((denominator_constant q).trans_ne hfield)).mpr ?_).symm
  have src : originalEGF 2 (mark q) = (originalDenominator q)⁻¹ :=
    original_egf (by decide) _
  have product : originalEGF 2 (mark q)*originalDenominator q = 1 :=
    (PowerSeries.eq_inv_iff_mul_eq_one
      ((originalDenominator_constant q).trans_ne one_ne_zero)).mp src
  rw [denominator_eq hq]
  calc
    _ = (PowerSeries.C ((1-(q:ℂ))⁻¹)*PowerSeries.C (1-(q:ℂ))) *
        (PowerSeries.map Complex.ofRealHom (originalEGF 2 (mark q)) *
          PowerSeries.map Complex.ofRealHom (originalDenominator q)) := by ring
    _ = 1 := by rw [← map_mul, ← map_mul, product, map_one, inv_mul_cancel₀ hfield, map_one, mul_one]

/-- The complex Taylor coefficient at the origin is the actual row with its
factorial and negative-axis normalization. -/
theorem iteratedDeriv_inv_G_at_zero {q : ℝ} (hq : q < 1) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ ↦ (G q z)⁻¹) 0 / (n.factorial:ℂ) =
      Complex.ofReal ((row n 2).eval (-q/(1-q))) / ((1-(q:ℂ))*(n.factorial:ℂ)) := by
  rw [← coeff_taylorAtZero, taylor_inv_G hq, inverse_eq_original hq,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  simp only [originalEGF, PowerSeries.coeff_mk, Complex.ofRealHom_eq_coe, Complex.ofReal_div,
    Complex.ofReal_natCast, mark]
  rw [div_mul_eq_div_div]
  ring

/-- An analytic power series with the source-exact row coefficients. -/
theorem inv_G_hasFPowerSeriesAt {q : ℝ} (hq : q < 1) :
    HasFPowerSeriesAt (fun z : ℂ ↦ (G q z)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦
        Complex.ofReal ((row n 2).eval (-q/(1-q))) / ((1-(q:ℂ))*(n.factorial:ℂ))) 0 := by
  have hfield : (1:ℂ)-(q:ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hq.ne')
  have an : AnalyticAt ℂ (fun z ↦ (G q z)⁻¹) 0 :=
    (analytic_G q).inv ((G_at_zero q).trans_ne hfield)
  simpa only [iteratedDeriv_inv_G_at_zero hq] using an.hasFPowerSeriesAt

/-- The same coefficient readout for iterated removal of the value at zero. -/
theorem iterate_dslope_inv_G_at_zero {q : ℝ} (hq : q < 1) (n : ℕ) :
    ((fun f : ℂ → ℂ ↦ dslope f 0)^[n] (fun z : ℂ ↦ (G q z)⁻¹)) 0 =
      Complex.ofReal ((row n 2).eval (-q/(1-q))) / ((1-(q:ℂ))*(n.factorial:ℂ)) := by
  have hs := (inv_G_hasFPowerSeriesAt hq).has_fpower_series_iterate_dslope_fslope n
  have val := (hs.coeff_zero 1).symm
  change _ = FormalMultilinearSeries.coeff _ 0 at val
  simpa only [FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
    FormalMultilinearSeries.coeff_ofScalars] using val

private theorem top_count_positive (n : ℕ) : 0 < count n 2 (n/2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases low : n < 2
    · rw [Nat.div_eq_of_lt low]
      exact count_zero_positive n (by decide)
    · have two : 2 ≤ n := by omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have index : (k+1)/2 - 1 = (k+1-2)/2 := by omega
      have dr : (k+1)/2 ≠ 0 := by omega
      have prev := ih (k+1-2) (by omega)
      rw [count_recurrence k (by decide)]
      apply lt_of_lt_of_le _ (single_le_sum (f := fun r ↦ (k+1).choose r *
        (if 2 ≤ r then (if (k+1)/2 = 0 then 0 else count (k+1-r) 2 ((k+1)/2-1))
          else count (k+1-r) 2 ((k+1)/2))) (fun _ _ ↦ Nat.zero_le _)
        (mem_Icc.mpr (by omega : 1 ≤ 2 ∧ 2 ≤ k+1)))
      simpa only [le_rfl, if_true, if_neg dr, index] using
        Nat.mul_pos (Nat.choose_pos two) prev

/-- Exact degree and positive leading and constant terms for every true row
with threshold two, including the constant ranks. -/
theorem original_shape (n : ℕ) :
    (row n 2).natDegree = n/2 ∧ 0 < (row n 2).leadingCoeff ∧ 0 < (row n 2).eval 0 := by
  have top : 0 < (row n 2).coeff (n/2) := by
    rw [coeff_row (by decide)]
    exact_mod_cast top_count_positive n
  have degree : (row n 2).natDegree = n/2 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ top.ne'
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_row (by decide), count_above_degree (by decide) (by omega), Nat.cast_zero]
  refine ⟨degree, by rwa [leadingCoeff, degree], ?_⟩
  rw [← coeff_zero_eq_eval_zero, coeff_row (by decide)]
  exact_mod_cast count_zero_positive n (by decide : 2≤2)

#print axioms iteratedDeriv_inv_G_at_zero
#print axioms inv_G_hasFPowerSeriesAt
#print axioms iterate_dslope_inv_G_at_zero
#print axioms original_shape

end OrderedPartitions.TwoPole
