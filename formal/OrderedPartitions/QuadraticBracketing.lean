import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! Exact tests for the first degree jump of a positive-coefficient sequence. -/

namespace OrderedPartitions

/-- The sign test on the coefficients is exactly the strict factorial-moment inequality. -/
theorem moment_gap_iff (u v a b c : ℝ) (hu : 0 < u) (hv : 0 < v)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    c / (a + b + c) <
        v / (u + v) * ((b + 2 * c) / (a + b + c) - v / (u + v)) ↔
      a * v ^ 2 - b * u * v + c * u ^ 2 < 0 := by
  have h₁ : 0 < u + v := by positivity
  have h₂ : 0 < a + b + c := by positivity
  let gap := v / (u + v) * ((b + 2*c)/(a + b + c) - v/(u + v)) - c/(a + b + c)
  have hprod : 0 < (u + v)^2 * (a + b + c) := by positivity
  have eqn : gap * ((u + v)^2 * (a + b + c)) = -(a*v^2 - b*u*v + c*u^2) := by
    dsimp [gap]
    field_simp
    ring
  rw [← sub_pos]
  change 0 < gap ↔ _
  rw [← mul_pos_iff_of_pos_right hprod, eqn]
  exact neg_pos

/-- Positive linear and quadratic rows strictly interlace exactly when the
quadratic is negative at the linear zero. The factorization accounts for both roots. -/
theorem first_jump_brackets_iff (u v a b c : ℝ) (hu : 0 < u) (hv : 0 < v)
    (ha : 0 < a) (hc : 0 < c) :
    a * v ^ 2 - b * u * v + c * u ^ 2 < 0 ↔
      ∃ l r : ℝ, l < -u/v ∧ -u/v < r ∧ r < 0 ∧
        ∀ t : ℝ, a + b*t + c*t^2 = c*(t-l)*(t-r) := by
  let x : ℝ := -u/v
  let q : ℝ → ℝ := fun t ↦ a + b*t + c*t^2
  have hx : x < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr hu) hv
  have heq : q x * v^2 = a*v^2 - b*u*v + c*u^2 := by
    dsimp [q,x]
    field_simp
    ring
  have hsign : q x * v^2 < 0 ↔ q x < 0 := by
    constructor
    · intro h
      by_contra! hq
      exact (not_lt_of_ge (mul_nonneg hq (sq_nonneg v))) h
    · exact fun h ↦ mul_neg_of_neg_of_pos h (sq_pos_of_pos hv)
  rw [← heq, hsign]
  change q x < 0 ↔ ∃ l r : ℝ, l < x ∧ x < r ∧ r < 0 ∧ ∀ t, q t = c*(t-l)*(t-r)
  constructor
  · intro h
    have q0 : 0 < q 0 := by simpa [q] using ha
    have cont : Continuous q := by dsimp [q]; fun_prop
    obtain ⟨r, hr, hz⟩ := intermediate_value_Icc hx.le cont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (q x) (q 0) from ⟨h.le, q0.le⟩)
    have hxr : x < r := lt_of_le_of_ne hr.1 (by rintro rfl; linarith)
    have hr0 : r < 0 := lt_of_le_of_ne hr.2 (by rintro rfl; linarith)
    let l : ℝ := -b/c-r
    have factor (t : ℝ) : q t = c*(t-l)*(t-r) := by
      dsimp [q] at hz
      dsimp [l,q]
      field_simp
      linear_combination hz
    refine ⟨l,r,?_,hxr,hr0,factor⟩
    by_contra! hxl
    rw [factor] at h
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hxl)) (sub_nonpos.mpr hxr.le))) h
  · rintro ⟨l,r,hl,hr,_,factor⟩
    rw [factor]
    exact mul_neg_of_pos_of_neg (mul_pos hc (sub_pos.mpr hl)) (sub_neg.mpr hr)

end OrderedPartitions

#print axioms OrderedPartitions.moment_gap_iff
#print axioms OrderedPartitions.first_jump_brackets_iff
