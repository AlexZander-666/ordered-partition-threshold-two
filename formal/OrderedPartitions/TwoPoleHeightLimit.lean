import OrderedPartitions.TwoPoleBranch

noncomputable section
namespace OrderedPartitions.TwoPole
open Real Filter Set
open scoped Topology

private theorem height_pos {v : ℝ} (iv : v ∈ Ioo 0 (π/2)) : -1 < height v := by
  have sinp := sin_pos_of_pos_of_lt_pi iv.1 (by linarith [iv.2,pi_pos])
  have cosp := cos_pos_of_mem_Ioo (show v∈Ioo (-(π/2)) (π/2) from ⟨by linarith [iv.1,pi_pos],iv.2⟩)
  have lc := log_pos ((one_lt_div sinp).mpr (sin_lt iv.1))
  have t := lt_tan iv.1 iv.2
  rw [tan_eq_sin_div_cos] at t
  have cot : v*cos v/sin v < 1 := (div_lt_one sinp).mpr ((lt_div_iff₀ cosp).mp t)
  unfold height
  linarith

private theorem widen {v : ℝ} (h : v∈Ioo 0 (π/2)) : v∈Ioo 0 π :=
  ⟨h.1,by linarith [h.2,pi_pos]⟩

theorem height_inverse_limit {α : Type*} {l : Filter α} {V : α→ℝ} {v : ℝ}
    (inside : ∀ᶠ i in l,V i∈Ioo 0 (π/2)) (iv : v∈Ioo 0 (π/2))
    (con : Tendsto (fun i ↦ height (V i)) l (𝓝 (height v))) :
    Tendsto V l (𝓝 v) := by
  apply tendsto_order.mpr
  constructor
  · intro a av
    obtain ⟨m,am,mv⟩ := exists_between (max_lt av iv.1)
    have mI : m∈Ioo 0 (π/2) := ⟨(le_max_right _ _).trans_lt am,mv.trans iv.2⟩
    have before := height_strictMono (widen mI) (widen iv) mv
    filter_upwards [inside,con.eventually_const_lt before] with i hi test
    exact ((le_max_left _ _).trans_lt am).trans ((height_strictMono.lt_iff_lt (widen mI) (widen hi)).mp test)
  · intro a va
    obtain ⟨m,vm,ma⟩ := exists_between (lt_min va iv.2)
    have mI : m∈Ioo 0 (π/2) := ⟨iv.1.trans vm,ma.trans_le (min_le_right _ _)⟩
    have beyond := height_strictMono (widen iv) (widen mI) vm
    filter_upwards [inside,con.eventually_lt_const beyond] with i hi test
    exact ((height_strictMono.lt_iff_lt (widen hi) (widen mI)).mp test).trans (ma.trans_le (min_le_left _ _))

theorem height_inverse_at_zero {α : Type*} {l : Filter α} {V : α→ℝ}
    (inside : ∀ᶠ i in l,V i∈Ioo 0 (π/2))
    (con : Tendsto (fun i ↦ height (V i)) l (𝓝 (-1))) :
    Tendsto V l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a neg
    exact inside.mono (fun i hi ↦ neg.trans hi.1)
  · intro a pos
    obtain ⟨m,mp,ma⟩ := exists_between (lt_min pos (half_pos pi_pos))
    have mI : m∈Ioo 0 (π/2) := ⟨mp,ma.trans_le (min_le_right _ _)⟩
    filter_upwards [inside,con.eventually_lt_const (height_pos mI)] with i hi test
    exact ((height_strictMono.lt_iff_lt (widen hi) (widen mI)).mp test).trans (ma.trans_le (min_le_left _ _))

/-- The imaginary part of the chosen pole is continuous through the interior
and tends to zero whenever the supercritical parameter reaches critical level. -/
theorem pole_height_continuous {c : ℝ} (cpos : 0 < c)
    (osc : ∀ q ∈ Ioo c 1, -1 < level q) :
    ContinuousOn (fun q ↦ (upperPole q).im) (Ioo c 1) := by
  intro q hq
  have domain : ∀ᶠ t in 𝓝[Ioo c 1] q, t∈Ioo c 1 := eventually_mem_nhdsWithin
  have hp := cpos.trans hq.1
  apply height_inverse_limit (domain.mono (fun t ht ↦ (upperPole_spec (cpos.trans ht.1) (osc t ht)).2))
    (upperPole_spec hp (osc q hq)).2
  rw [pole_height_eq hp (osc q hq)]
  exact (level_cont hp.ne').continuousWithinAt.tendsto.congr'
    (domain.mono (fun t ht ↦ (pole_height_eq (cpos.trans ht.1) (osc t ht)).symm))

theorem pole_height_vanish {α : Type*} {l : Filter α} {q : α→ℝ}
    (domain : ∀ᶠ i in l,0<q i ∧ -1<level (q i))
    (lim : Tendsto (fun i ↦ level (q i)) l (𝓝 (-1))) :
    Tendsto (fun i ↦ (upperPole (q i)).im) l (𝓝 0) := by
  apply height_inverse_at_zero (domain.mono (fun i hi ↦ (upperPole_spec hi.1 hi.2).2))
  exact lim.congr' (domain.mono (fun i hi ↦ (pole_height_eq hi.1 hi.2).symm))

#print axioms pole_height_continuous
#print axioms pole_height_vanish
end OrderedPartitions.TwoPole
