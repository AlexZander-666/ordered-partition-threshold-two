import OrderedPartitions.TwoPolePhaseReadout

/-! Phase traversal from limits at the ends of a negative half-line. -/

namespace OrderedPartitions.TwoPolePhase
open Real Set Polynomial Filter RootTracking
open scoped Topology

/-- The phase and model only need to be defined as specified below the upper
endpoint. The limit at each end supplies a compact interval with full coverage. -/
theorem ordered_pair_of_phase_limits {d : ℕ} {p q : ℝ[X]} {c L R : ℝ}
    {ψ shift E F scaleOld scaleNew : ℝ → ℝ}
    (p_degree : p.natDegree = d) (p_nonzero : p ≠ 0)
    (q_degree : q.natDegree = d ∨ q.natDegree = d+1)
    (q_leading : 0 < q.leadingCoeff) (q_at_zero : 0 < q.eval 0)
    (c_nonpos : c ≤ 0) (phase : ContinuousOn ψ (Iio c))
    (far_left : Tendsto ψ atBot (𝓝 L)) (near_right : Tendsto ψ (𝓝[<] c) (𝓝 R))
    (front : (d:ℝ)*π+(π-π/4) < L) (back : R < π+π/4)
    (old_model : ∀ x < c, 0 < scaleOld x ∧ |E x| ≤ sin (shift x)/4 ∧
      scaleOld x*p.eval x = -cos (ψ x)+E x)
    (new_model : ∀ x < c, 0 < sin (shift x) ∧ 0 < scaleNew x ∧
      |F x| ≤ sin (shift x)/4 ∧ scaleNew x*q.eval x = -cos (ψ x+shift x)+F x) :
    OrderedPair d p q := by
  have right := near_right.eventually (gt_mem_nhds back)
  have inside : ∀ᶠ x in 𝓝[<] c, x < c := eventually_mem_nhdsWithin
  obtain ⟨b, hb, low⟩ := (inside.and right).exists
  have left := far_left.eventually (lt_mem_nhds front)
  obtain ⟨a, ab, high⟩ := ((eventually_lt_atBot b).and left).exists
  have subset : Icc a b ⊆ Iio c := fun _ hx ↦ hx.2.trans_lt hb
  exact ordered_pair_of_phase p_degree p_nonzero q_degree q_leading q_at_zero
    ab (hb.trans_le c_nonpos) (phase.mono subset) high low
    (fun x hx ↦ old_model x (subset hx))
    (fun x hx ↦ new_model x (subset hx))

#print axioms ordered_pair_of_phase_limits

/-- The fractional linear map used both to parameterize and to recover the
original negative variable. -/
noncomputable def negativeAxis (x : ℝ) : ℝ := -x/(1-x)

private theorem negativeAxis_lt_one {x : ℝ} (hx : x < 1) : negativeAxis x < 1 := by
  apply (div_lt_iff₀ (by linarith : 0 < 1-x)).mpr
  linarith

private theorem negativeAxis_apply_apply {x : ℝ} (hx : x < 1) :
    negativeAxis (negativeAxis x) = x := by
  have h := negativeAxis_lt_one hx
  unfold negativeAxis at h ⊢
  field_simp [show 1-x ≠ 0 by linarith, show 1- -x/(1-x) ≠ 0 by linarith]
  ring

private theorem negativeAxis_lt {x y : ℝ} (lt : x < y) (hy : y < 1) :
    negativeAxis y < negativeAxis x := by
  apply (div_lt_div_iff₀ (by linarith : 0 < 1-y) (by linarith : 0 < 1-x)).mpr
  nlinarith only [lt]

/-- The same root readout in the oscillatory parameter, with the original
polynomial still evaluated at the corresponding negative real argument. -/
theorem ordered_pair_of_parameter_limits {d : ℕ} {p q : ℝ[X]} {c L R : ℝ}
    {ψ shift E F scaleOld scaleNew : ℝ → ℝ}
    (p_degree : p.natDegree = d) (p_nonzero : p ≠ 0)
    (q_degree : q.natDegree = d ∨ q.natDegree = d+1)
    (q_leading : 0 < q.leadingCoeff) (q_at_zero : 0 < q.eval 0)
    (c_nonneg : 0 ≤ c) (c_lt : c < 1) (phase : ContinuousOn ψ (Ioo c 1))
    (far_left : Tendsto ψ (𝓝[<] 1) (𝓝 L)) (near_right : Tendsto ψ (𝓝[>] c) (𝓝 R))
    (front : (d:ℝ)*π+(π-π/4) < L) (back : R < π+π/4)
    (old_model : ∀ u ∈ Ioo c 1, 0 < scaleOld u ∧ |E u| ≤ sin (shift u)/4 ∧
      scaleOld u*p.eval (negativeAxis u) = -cos (ψ u)+E u)
    (new_model : ∀ u ∈ Ioo c 1, 0 < sin (shift u) ∧ 0 < scaleNew u ∧
      |F u| ≤ sin (shift u)/4 ∧ scaleNew u*q.eval (negativeAxis u) =
        -cos (ψ u+shift u)+F u) :
    OrderedPair d p q := by
  have near_c : ∀ᶠ u in 𝓝[>] c, c < u := eventually_mem_nhdsWithin
  have below_one : ∀ᶠ u in 𝓝[>] c, u < 1 := nhdsWithin_le_nhds (gt_mem_nhds c_lt)
  obtain ⟨l, cl, l1, low⟩ :=
    (near_c.and (below_one.and (near_right.eventually (gt_mem_nhds back)))).exists
  have near_one : ∀ᶠ u in 𝓝[<] (1:ℝ), u < 1 := eventually_mem_nhdsWithin
  have above_l : ∀ᶠ u in 𝓝[<] (1:ℝ), l < u := nhdsWithin_le_nhds (lt_mem_nhds l1)
  obtain ⟨u, lu, u1, high⟩ :=
    (above_l.and (near_one.and (far_left.eventually (lt_mem_nhds front)))).exists
  let a := negativeAxis u
  let b := negativeAxis l
  have ab : a < b := negativeAxis_lt lu u1
  have bneg : b < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have below (x : ℝ) (hx : x ∈ Icc a b) : x < 1 := by linarith [hx.2]
  have mem (x : ℝ) (hx : x ∈ Icc a b) : negativeAxis x ∈ Ioo c 1 := by
    refine ⟨cl.trans_le ?_, negativeAxis_lt_one (below x hx)⟩
    rcases hx.2.lt_or_eq with lt | eq
    · exact ((negativeAxis_apply_apply l1).symm.trans_lt
        (negativeAxis_lt lt (negativeAxis_lt_one l1))).le
    · rw [eq, negativeAxis_apply_apply l1]
  have cont : ContinuousOn negativeAxis (Icc a b) := by
    apply continuousOn_id.neg.div (continuousOn_const.sub continuousOn_id)
    intro x hx
    change 1-x ≠ 0
    linarith [below x hx]
  refine ordered_pair_of_phase (ψ := fun x ↦ ψ (negativeAxis x))
    (shift := fun x ↦ shift (negativeAxis x)) (E := fun x ↦ E (negativeAxis x))
    (F := fun x ↦ F (negativeAxis x)) (scaleOld := fun x ↦ scaleOld (negativeAxis x))
    (scaleNew := fun x ↦ scaleNew (negativeAxis x))
    p_degree p_nonzero q_degree q_leading q_at_zero ab bneg (phase.comp cont mem) ?_ ?_ ?_ ?_
  · simpa only [a, negativeAxis_apply_apply u1] using high
  · simpa only [b, negativeAxis_apply_apply l1] using low
  · intro x hx
    simpa only [negativeAxis_apply_apply (below x hx)] using old_model _ (mem x hx)
  · intro x hx
    simpa only [negativeAxis_apply_apply (below x hx)] using new_model _ (mem x hx)

#print axioms ordered_pair_of_parameter_limits

end OrderedPartitions.TwoPolePhase
