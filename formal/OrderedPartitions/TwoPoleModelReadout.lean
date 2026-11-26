import OrderedPartitions.TwoPolePhaseEndpoints
import OrderedPartitions.TwoPolePhaseLimits
import OrderedPartitions.TwoPoleOriginalTaylor
import OrderedPartitions.TwoPoleFiniteVerified

noncomputable section
namespace OrderedPartitions.TwoPole
open Real Set Filter Polynomial RootTracking TwoPolePhase
open scoped Topology

/-- An error estimate measured in the size of the intended phase shift. -/
def PhaseEstimate (m g : ℕ) (q : ℝ) : Prop :=
  ∃ s e : ℝ, 0<s ∧ |e|≤sin ((g:ℝ)*theta q)/4 ∧
    s*(row m 2).eval (negativeAxis q) = -cos (phase m q)+e

theorem shift_pos {q : ℝ} (lo : 1/6<q) (hi : q<1) (osc : -1<level q)
    {g : ℕ} (gap : g=1 ∨ g=2) : 0<sin ((g:ℝ)*theta q) := by
  obtain ⟨gz,iv⟩ := upperPole_spec (by linarith) osc
  have pos := (principal_bounds lo hi gz iv).1
  have nz : upperPole q ≠ 0 := by intro e;rw [e] at pos;simp at pos
  have S : 0<sin (theta q) := by rw [theta,Complex.sin_arg];exact div_pos iv.1 (norm_pos_iff.mpr nz)
  have C : 0<cos (theta q) := by rw [theta,Complex.cos_arg nz];exact div_pos pos (norm_pos_iff.mpr nz)
  rcases gap with rfl|rfl
  · simpa using S
  · simpa [sin_two_mul] using (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) S) C)

theorem original_pair_of_estimates (n g : ℕ) (gap : g=1 ∨ g=2)
    (est : ∀ q : ℝ, 1/6<q → q<1 → -1<level q → PhaseEstimate n g q ∧ PhaseEstimate (n+g) g q) :
    OrderedPair (n/2) (row n 2) (row (n+g) 2) := by
  obtain ⟨c,cl,ch,crit,osc⟩ := critical_exists
  have cpos : 0<c := by linarith
  have h (q : ℝ) (hq : q∈Ioo c 1) := est q (cl.trans hq.1) hq.2 (osc q hq)
  choose! s e hold using fun q hq ↦ (h q hq).1
  choose! t f hnew using fun q hq ↦ (h q hq).2
  obtain ⟨deg,lead,atz⟩ := original_shape n
  obtain ⟨deg',lead',atz'⟩ := original_shape (n+g)
  obtain ⟨left,right⟩ := phase_endpoints cl ch crit osc n
  have safe : 2*(n/2)≤n := by omega
  have half : 2*((n/2:ℕ):ℝ)≤n := by exact_mod_cast safe
  apply ordered_pair_of_parameter_limits (c:=c) (ψ:=phase n) (shift:=fun q ↦ (g:ℝ)*theta q)
    (scaleOld:=s) (E:=e) (scaleNew:=t) (F:=f)
    deg (leadingCoeff_ne_zero.mp lead.ne') (by omega) lead' atz' cpos.le (by linarith)
    (phase_continuous cpos osc n) right left
  · nlinarith [mul_nonneg (sub_nonneg.mpr half) pi_pos.le,pi_pos]
  · linarith [pi_pos]
  · exact hold
  · intro q hq
    obtain ⟨tp,fb,model⟩ := hnew q hq
    have eq : phase (n+g) q = phase n q + (g:ℝ)*theta q := by simp [phase];ring
    exact ⟨shift_pos (cl.trans hq.1) hq.2 (osc q hq) gap,tp,fb,eq ▸ model⟩

/-- The kernel-certified finite tables supply the full range below the analytic cutoff. -/
theorem original_all_of_estimates
    (est : ∀ n g : ℕ, (g=1 ∧ 20≤n) ∨ (g=2 ∧ 25≤n) →
      ∀ q : ℝ, 1/6<q → q<1 → -1<level q → PhaseEstimate n g q ∧ PhaseEstimate (n+g) g q)
    {n g : ℕ} (start : 2≤n) (gap : g=1 ∨ g=2) :
    OrderedPair (n/2) (row n 2) (row (n+g) 2) := by
  rcases gap with rfl|rfl
  · by_cases high : 20≤n
    · exact original_pair_of_estimates n 1 (by simp) (est n 1 (Or.inl ⟨rfl,high⟩))
    · exact TwoPoleFinite.original_gap1_finite n start (by omega)
  · by_cases high : 25≤n
    · exact original_pair_of_estimates n 2 (by simp) (est n 2 (Or.inr ⟨rfl,high⟩))
    · exact TwoPoleFinite.original_gap2_finite n start (by omega)

#print axioms original_pair_of_estimates
#print axioms original_all_of_estimates
end OrderedPartitions.TwoPole
