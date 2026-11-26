import OrderedPartitions.TwoPolePrincipal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
namespace OrderedPartitions.TwoPole
open Real Filter Set
open scoped Topology

def level (q : ℝ) := log q + (1-2*q)

theorem level_cont {q : ℝ} (hq : q≠0) : ContinuousAt level q :=
  (Real.continuousAt_log hq).add (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))

theorem level_deriv {q : ℝ} (hq : q≠0) : HasDerivAt level (q⁻¹-2) q := by
  unfold level
  convert! (Real.hasDerivAt_log hq).add ((hasDerivAt_const q (1:ℝ)).sub
    ((hasDerivAt_id q).const_mul 2)) using 1
  ring

theorem critical_exists : ∃ c : ℝ, 1/6 < c ∧ c < 1/2 ∧ level c = -1 ∧
    ∀ q ∈ Ioo c 1, -1 < level q := by
  have half : -1 < level (1/2) := by
    simp only [level,one_div,Real.log_inv]
    linarith [Real.log_two_lt_d9]
  have sixth : level (1/6) < -1 := by
    have s : log 6 = log 2 + log 3 := by rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)];norm_num
    simp only [level,one_div,Real.log_inv]
    linarith [Real.log_two_gt_d9,Real.log_three_gt_d9]
  have inc : StrictMonoOn level (Icc (1/6) (1/2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ..) (fun q h ↦ (level_cont (by linarith [h.1])).continuousWithinAt)
    intro q h
    rw [interior_Icc] at h
    have pos : 0 < q := by linarith [h.1]
    rw [(level_deriv pos.ne').deriv,sub_pos,lt_inv_comm₀ (by norm_num) pos]
    linarith [h.2]
  have dec : StrictAntiOn level (Icc (1/2) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ..) (fun q h ↦ (level_cont (by linarith [h.1])).continuousWithinAt)
    intro q h
    rw [interior_Icc] at h
    have pos : 0 < q := by linarith [h.1]
    rw [(level_deriv pos.ne').deriv,sub_neg,inv_lt_comm₀ pos (by norm_num)]
    linarith [h.1]
  obtain ⟨c,⟨cl,ch⟩,eq⟩ := intermediate_value_Ioo (by norm_num : (1/6:ℝ)≤1/2)
    (fun q h ↦ (level_cont (by linarith [h.1])).continuousWithinAt) (show (-1:ℝ)∈Ioo _ _ from ⟨sixth,half⟩)
  refine ⟨c,cl,ch,eq,?_⟩
  intro q h
  rcases le_total q (1/2) with small | big
  · exact eq ▸ inc ⟨cl.le,ch.le⟩ ⟨cl.le.trans h.1.le,small⟩ h.1
  · have ord := dec ⟨big,h.2.le⟩ (show (1:ℝ)∈Icc (1/2) 1 by norm_num) h.2
    have endpoint : level 1 = -1 := by norm_num [level]
    rwa [endpoint] at ord

def upperPole (q : ℝ) : ℂ :=
  if h : 0<q ∧ -1<level q then (principal_exists h.1 h.2).choose else 0

theorem upperPole_spec {q : ℝ} (hq : 0<q) (osc : -1<level q) :
    G q (upperPole q)=0 ∧ (upperPole q).im∈Ioo 0 (π/2) := by
  rw [upperPole,dif_pos ⟨hq,osc⟩]
  exact ⟨(principal_exists hq osc).choose_spec.1,(principal_exists hq osc).choose_spec.2.1⟩

theorem pole_height_eq {q : ℝ} (hq : 0<q) (osc : -1<level q) :
    height (upperPole q).im = level q := by
  obtain ⟨zero,iv⟩ := upperPole_spec hq osc
  exact ((zero_iff hq iv.1 (sin_pos_of_pos_of_lt_pi iv.1 (by linarith [iv.2,pi_pos]))).mp zero).2

#print axioms critical_exists
#print axioms upperPole_spec
end OrderedPartitions.TwoPole
