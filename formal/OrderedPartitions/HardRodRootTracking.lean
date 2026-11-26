import OrderedPartitions.HardRodResidue
import Mathlib.Data.Finset.Max

noncomputable section
namespace OrderedPartitions.RootTracking
open Polynomial Filter Set Topology

private theorem strict_bracket {p : ℝ[X]} {r ε : ℝ} (zero : p.eval r=0)
    (simple : p.derivative.eval r≠0) (pos : 0<ε) :
    ∃ a b, r-ε<a ∧ a<r ∧ r<b ∧ b<r+ε ∧ p.eval a*p.eval b<0 := by
  obtain ⟨g,fact⟩ := Polynomial.dvd_iff_isRoot.mpr zero
  have der : p.derivative.eval r=g.eval r := by
    rw [fact]
    simp [derivative_mul]
  have good : ∀ᶠ x in 𝓝 r, 0<g.eval x*g.eval r := by
    have h : Continuous (fun x ↦ g.eval x*g.eval r) := g.continuous.mul continuous_const
    apply (h.continuousAt (x:=r)).tendsto.eventually_const_lt
    exact mul_self_pos.mpr (der ▸ simple)
  obtain ⟨δ,δpos,within⟩ := Metric.eventually_nhds_iff.mp good
  let e := min δ ε/2
  have ep : 0<e := half_pos (lt_min δpos pos)
  have ed : e<δ := lt_of_lt_of_le (half_lt_self (lt_min δpos pos)) (min_le_left _ _)
  have ee : e<ε := lt_of_lt_of_le (half_lt_self (lt_min δpos pos)) (min_le_right _ _)
  have sl := within (y:=r-e) (by simpa [Real.dist_eq,abs_of_pos ep] using ed)
  have sr := within (y:=r+e) (by simpa [Real.dist_eq,abs_of_pos ep] using ed)
  have prod : 0<g.eval (r-e)*g.eval (r+e) := by
    rcases mul_pos_iff.mp sl with ⟨l,h⟩|⟨l,h⟩ <;> rcases mul_pos_iff.mp sr with ⟨r1,_⟩|⟨r1,_⟩
    · exact mul_pos l r1
    · linarith
    · linarith
    · exact mul_pos_of_neg_of_neg l r1
  refine ⟨r-e,r+e,by linarith,by linarith,by linarith,by linarith,?_⟩
  rw [fact]
  simp only [eval_mul,eval_sub,eval_X,eval_C,sub_sub_cancel_left,add_sub_cancel_left]
  calc _ = (-(e^2))*(g.eval (r-e)*g.eval (r+e)) := by ring
       _ < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos ep)) prod

private theorem open_ivt {p : ℝ[X]} {a b : ℝ} (lt : a<b) (neg : p.eval a*p.eval b<0) :
    ∃ z, a<z ∧ z<b ∧ p.eval z=0 := by
  rcases mul_neg_iff.mp neg with ⟨u,v⟩|⟨u,v⟩
  · obtain ⟨z,zmem,hz⟩ := intermediate_value_Ioo' lt.le p.continuous.continuousOn
      (show 0∈Ioo (p.eval b) (p.eval a) from ⟨v,u⟩)
    exact ⟨z,zmem.1,zmem.2,hz⟩
  · obtain ⟨z,zmem,hz⟩ := intermediate_value_Ioo lt.le p.continuous.continuousOn
      (show 0∈Ioo (p.eval a) (p.eval b) from ⟨u,v⟩)
    exact ⟨z,zmem.1,zmem.2,hz⟩

/-- Pointwise convergence gives a real root arbitrarily near a simple real limit root. -/
theorem eventually_near_root {P : ℕ→ℝ[X]} {p : ℝ[X]} {r ε : ℝ}
    (conv : ∀ x, Tendsto (fun n ↦ (P n).eval x) atTop (𝓝 (p.eval x)))
    (zero : p.eval r=0) (simple : p.derivative.eval r≠0) (pos : 0<ε) :
    ∀ᶠ n in atTop, ∃ z, (P n).eval z=0 ∧ dist z r<ε := by
  obtain ⟨a,b,al,ar,bl,br,h⟩ := strict_bracket zero simple pos
  filter_upwards [((conv a).mul (conv b)).eventually_lt_const h] with n hn
  obtain ⟨z,zl,zr,hz⟩ := open_ivt (ar.trans bl) hn
  exact ⟨z,hz,by rw [Real.dist_eq,abs_lt];constructor <;> linarith⟩

private noncomputable def closest (p : ℝ[X]) (r : ℝ) : ℝ := by
  classical
  exact if h : p.roots.toFinset.Nonempty then
    (p.roots.toFinset.exists_min_image (fun z ↦ dist z r) h).choose else r

private theorem closest_spec {p : ℝ[X]} {r z : ℝ} (hz : p.eval z=0) :
    p.eval (closest p r)=0 ∧ dist (closest p r) r ≤ dist z r := by
  classical
  by_cases eq : p=0
  · simp [eq,closest]
  have mem := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots eq).mpr hz)
  have ex : p.roots.toFinset.Nonempty := ⟨z,mem⟩
  simp only [closest,dif_pos ex]
  have spec := (p.roots.toFinset.exists_min_image (fun t ↦ dist t r) ex).choose_spec
  exact ⟨(Polynomial.mem_roots eq).mp (Multiset.mem_toFinset.mp spec.1), spec.2 z mem⟩

/-- One choice tracks a whole sequence, without requiring uniqueness near the
limit, global real-rootedness or degree conservation on the approximating row. -/
theorem simple_branch {P : ℕ→ℝ[X]} {p : ℝ[X]} {r : ℝ}
    (conv : ∀ x, Tendsto (fun n ↦ (P n).eval x) atTop (𝓝 (p.eval x)))
    (zero : p.eval r=0) (simple : p.derivative.eval r≠0) :
    ∃ z : ℕ→ℝ, Tendsto z atTop (𝓝 r) ∧ ∀ᶠ n in atTop, (P n).eval (z n)=0 := by
  refine ⟨fun n ↦ closest (P n) r,Metric.tendsto_nhds.mpr ?_,?_⟩
  · intro ε ep
    filter_upwards [eventually_near_root conv zero simple ep] with n hn
    obtain ⟨z,hz,dist⟩ := hn
    exact (closest_spec hz).2.trans_lt dist
  · filter_upwards [eventually_near_root conv zero simple zero_lt_one] with n hn
    obtain ⟨_,hz,_⟩ := hn
    exact (closest_spec hz).1

#print axioms simple_branch
end OrderedPartitions.RootTracking
