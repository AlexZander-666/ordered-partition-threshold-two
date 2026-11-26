import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-! Ordered crossing intervals of a continuous phase. -/

namespace OrderedPartitions.TwoPolePhase
open Set

private theorem compact_fiber {a b : ℝ} {f : ℝ → ℝ} (h : ContinuousOn f (Icc a b))
    (v : ℝ) : IsCompact {x | x ∈ Icc a b ∧ f x = v} := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  have closed := isClosed_singleton (x := v) |>.preimage (continuousOn_iff_continuous_domRestrict.mp h)
  have compact := closed.isCompact.image continuous_subtype_val
  convert compact using 1
  ext x
  constructor
  · rintro ⟨hx, eq⟩
    exact ⟨⟨x, hx⟩, eq, rfl⟩
  · rintro ⟨⟨y, hy⟩, eq, rfl⟩
    exact ⟨hy, eq⟩

private theorem first_crossing {a b v : ℝ} {f : ℝ → ℝ} (ab : a < b)
    (h : ContinuousOn f (Icc a b)) (front : v < f a) (back : f b < v) :
    ∃ t, a < t ∧ t < b ∧ f t = v ∧ ∀ x ∈ Ico a t, v < f x := by
  let S := {x | x ∈ Icc a b ∧ f x = v}
  have comp : IsCompact S := compact_fiber h v
  have existsHit := intermediate_value_Ioo' ab.le h (show v ∈ Ioo (f b) (f a) from ⟨back, front⟩)
  obtain ⟨x, hx, eq⟩ := existsHit
  have mem : x ∈ S := ⟨Ioo_subset_Icc_self hx, eq⟩
  let t := sInf S
  have ht : t ∈ S := comp.sInf_mem ⟨x, mem⟩
  have atLeft : a < t := lt_of_le_of_ne ht.1.1 (by
    intro eq
    exact front.ne (eq ▸ ht.2.symm))
  have tb : t < b := (csInf_le comp.bddBelow mem).trans_lt hx.2
  refine ⟨t, atLeft, tb, ht.2, ?_⟩
  intro y hy
  by_contra! below
  have hit := intermediate_value_Icc' (a := a) (b := y) hy.1
    (h.mono (Icc_subset_Icc_right (hy.2.trans tb).le))
    (show v ∈ Icc (f y) (f a) from ⟨below, front.le⟩)
  obtain ⟨z, hz, fz⟩ := hit
  exact (csInf_le comp.bddBelow ⟨⟨hz.1, hz.2.trans (hy.2.trans tb).le⟩, fz⟩).not_gt
    (hz.2.trans_lt hy.2)

private theorem last_crossing {a b v : ℝ} {f : ℝ → ℝ} (ab : a < b)
    (h : ContinuousOn f (Icc a b)) (front : v < f a) (back : f b < v) :
    ∃ L, a < L ∧ L < b ∧ f L = v ∧
      (∀ x ∈ Ioc L b, f x < v) ∧ ∀ x ∈ Icc a b, f x = v → x ≤ L := by
  let S := {x | x ∈ Icc a b ∧ f x = v}
  have comp : IsCompact S := compact_fiber h v
  obtain ⟨x, hx, eq⟩ :=
    intermediate_value_Ioo' ab.le h (show v ∈ Ioo (f b) (f a) from ⟨back, front⟩)
  have mem : x ∈ S := ⟨Ioo_subset_Icc_self hx, eq⟩
  let L := sSup S
  have hL : L ∈ S := comp.sSup_mem ⟨x, mem⟩
  have aL : a < L := hx.1.trans_le (le_csSup comp.bddAbove mem)
  have Lb : L < b := lt_of_le_of_ne hL.1.2 (by
    intro eq
    exact back.ne (eq ▸ hL.2))
  have maximal : ∀ y ∈ Icc a b, f y = v → y ≤ L := fun y hy e ↦
    le_csSup comp.bddAbove ⟨hy, e⟩
  refine ⟨L, aL, Lb, hL.2, ?_, maximal⟩
  intro y hy
  by_contra! above
  obtain ⟨z, hz, fz⟩ := intermediate_value_Icc' (a := y) (b := b) hy.2
    (h.mono (Icc_subset_Icc_left (aL.trans hy.1).le))
    (show v ∈ Icc (f b) (f y) from ⟨back.le, above⟩)
  exact (maximal z ⟨aL.le.trans (hy.1.le.trans hz.1), hz.2⟩ fz).not_gt (hy.1.trans_le hz.1)

/-- The phase descends through each specified strip on disjoint, ordered time
intervals. The phase can have arbitrary continuous excursions. -/
theorem strips_of_endpoints {d : ℕ} {a b : ℝ} {f : ℝ → ℝ} {lo hi : Fin d → ℝ}
    (ab : a < b) (h : ContinuousOn f (Icc a b))
    (strip : ∀ i, lo i < hi i) (ordered : ∀ i j, i < j → hi j < lo i)
    (front : ∀ i, hi i < f a) (back : ∀ i, f b < lo i) :
    ∃ l r : Fin d → ℝ,
      (∀ i, a < l i ∧ l i < r i ∧ r i < b ∧ f (l i) = hi i ∧ f (r i) = lo i ∧
        MapsTo f (Icc (l i) (r i)) (Icc (lo i) (hi i))) ∧
      (∀ i j, i < j → r i < l j) := by
  choose r hrs using fun i ↦ first_crossing ab h ((strip i).trans (front i)) (back i)
  have rA (i) : a < r i := (hrs i).1
  have rB (i) : r i < b := (hrs i).2.1
  have rEq (i) : f (r i) = lo i := (hrs i).2.2.1
  have hlo (i) : ContinuousOn f (Icc a (r i)) :=
    h.mono (Icc_subset_Icc_right (rB i).le)
  choose l hls using fun i ↦
    last_crossing (rA i) (hlo i) (front i) ((rEq i).trans_lt (strip i))
  refine ⟨l, r, ?_, ?_⟩
  · intro i
    obtain ⟨al, lr, at_hi, after, _⟩ := hls i
    refine ⟨al, lr, rB i, at_hi, rEq i, ?_⟩
    intro x hx
    obtain ⟨le, right⟩ := hx
    refine ⟨?_, ?_⟩
    · rcases right.lt_or_eq with lt | eq
      · exact ((hrs i).2.2.2 x ⟨al.le.trans le, lt⟩).le
      · rw [eq, rEq i]
    · rcases le.lt_or_eq with lt | eq
      · exact (after x ⟨lt, right⟩).le
      · rw [← eq, at_hi]
  · intro i j ij
    have early : r i < r j := by
      by_contra! hge
      rcases hge.lt_or_eq with lt | eq
      · have val := (hrs i).2.2.2 (r j) ⟨(rA j).le, lt⟩
        rw [rEq j] at val
        exact ((strip j).trans (ordered i j ij)).not_gt val
      · exact ((strip j).trans (ordered i j ij)).ne ((rEq j).symm.trans
          ((congrArg f eq).trans (rEq i)))
    have high : hi j < f (r i) := (ordered i j ij).trans_le (rEq i).ge
    obtain ⟨z, hz, fz⟩ := intermediate_value_Ioo' early.le
      ((hlo j).mono (Icc_subset_Icc_left (rA i).le))
      (show hi j ∈ Ioo (f (r j)) (f (r i)) from ⟨(rEq j).trans_lt (strip j), high⟩)
    exact hz.1.trans_le ((hls j).2.2.2.2 z ⟨(rA i).le.trans hz.1.le, hz.2.le⟩ fz)

#print axioms strips_of_endpoints

end OrderedPartitions.TwoPolePhase
