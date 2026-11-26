import OrderedPartitions.FirstJumpRows
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

noncomputable section
open Finset
namespace OrderedPartitions

/-- Reindex the surviving labels after deleting the specified last block. -/
def remainingLabels {n : ℕ} (s : Finset (Fin n)) : Fin (n-s.card) ≃ ↥sᶜ :=
  (sᶜ.orderIsoOfFin (k := n-s.card) (by rw [Finset.card_compl, Fintype.card_fin])).toEquiv

/-- Append a specified last block and preserve all earlier block positions. -/
def appendLast {n b : ℕ} (s : Finset (Fin n)) (g : Fin (n-s.card) → Fin b)
    (x : Fin n) : Fin (b+1) :=
  if hx : x ∈ s then Fin.last b else
    (g ((remainingLabels s).symm ⟨x, mem_compl.mpr hx⟩)).castSucc

theorem block_append_last {n b : ℕ} (s : Finset (Fin n)) (g : Fin (n-s.card) → Fin b) :
    block (appendLast s g) (Fin.last b) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [block, appendLast, hx, Fin.ne_of_lt, Fin.castSucc_lt_last]

private def remainingEmbedding {n : ℕ} (s : Finset (Fin n)) : Fin (n-s.card) ↪ Fin n :=
  (remainingLabels s).toEmbedding.trans (Function.Embedding.subtype _)

theorem block_append_earlier {n b : ℕ} (s : Finset (Fin n)) (g : Fin (n-s.card) → Fin b)
    (i : Fin b) :
    block (appendLast s g) i.castSucc = (block g i).map (remainingEmbedding s) := by
  ext x
  constructor
  · intro hx
    have hval := (mem_filter.mp hx).2
    by_cases hs : x ∈ s
    · simp [appendLast, hs, Ne.symm (Fin.ne_of_lt (Fin.castSucc_lt_last i))] at hval
    · let x' : ↥sᶜ := ⟨x, mem_compl.mpr hs⟩
      refine mem_map.mpr ⟨(remainingLabels s).symm x', ?_, ?_⟩
      · simpa [x', block, appendLast, hs] using hval
      · change ((remainingLabels s) ((remainingLabels s).symm x')).val = x
        simp [x']
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    let x' := remainingLabels s y
    have hs : x'.val ∉ s := mem_compl.mp x'.property
    change x'.val ∈ block (appendLast s g) i.castSucc
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [appendLast, dif_neg hs]
    simpa [x'] using (mem_filter.mp hy).2

theorem large_append_card {n b : ℕ} (s : Finset (Fin n)) (g : Fin (n-s.card) → Fin b)
    (j : ℕ) : (large (appendLast s g) j).card =
      (large g j).card + (if j ≤ s.card then 1 else 0) := by
  simp only [large, card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [block_append_last, block_append_earlier]

theorem append_surjective {n b : ℕ} {s : Finset (Fin n)} {g : Fin (n-s.card) → Fin b}
    (hs : s.Nonempty) (hg : Function.Surjective g) : Function.Surjective (appendLast s g) := by
  intro i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · obtain ⟨x,hx⟩ := hs
    exact ⟨x, by simp [appendLast, hx]⟩
  · obtain ⟨y,rfl⟩ := hg i
    let x' := remainingLabels s y
    have hx : x'.val ∉ s := mem_compl.mp x'.property
    exact ⟨x'.val, by simp [appendLast, hx, x']⟩

def Onto (n b : ℕ) := {f : Fin n → Fin b // Function.Surjective f}

instance (n b : ℕ) : Fintype (Onto n b) := by classical unfold Onto; infer_instance

private def removeLast {n b : ℕ} (f : Fin n → Fin (b+1)) (s : Finset (Fin n))
    (hs : block f (Fin.last b) = s) (y : Fin (n-s.card)) : Fin b :=
  let x := remainingLabels s y
  ⟨(f x.val).val, by
    have hnot : f x.val ≠ Fin.last b := by
      intro heq
      have : x.val ∈ block f (Fin.last b) := mem_filter.mpr ⟨mem_univ _, heq⟩
      rw [hs] at this
      exact mem_compl.mp x.property this
    have hlt := (f x.val).isLt
    have hval : (f x.val).val ≠ b := fun h ↦ hnot (Fin.ext h)
    omega⟩

private theorem append_remove {n b : ℕ} (f : Fin n → Fin (b+1)) (s : Finset (Fin n))
    (hs : block f (Fin.last b) = s) : appendLast s (removeLast f s hs) = f := by
  funext x
  by_cases hx : x ∈ s
  · have hm : x ∈ block f (Fin.last b) := hs ▸ hx
    simpa [appendLast,hx] using (mem_filter.mp hm).2.symm
  · apply Fin.ext
    simp [appendLast, hx, removeLast]

private theorem remove_surjective {n b : ℕ} (f : Onto n (b+1)) (s : Finset (Fin n))
    (hs : block f.val (Fin.last b) = s) : Function.Surjective (removeLast f.val s hs) := by
  intro i
  obtain ⟨x,hx⟩ := f.property i.castSucc
  have hn : x ∉ s := by
    rw [← hs]
    simp [block, hx, Fin.ne_of_lt (Fin.castSucc_lt_last i)]
  let y : ↥sᶜ := ⟨x, mem_compl.mpr hn⟩
  refine ⟨(remainingLabels s).symm y, Fin.ext ?_⟩
  simpa [removeLast, y] using congrArg Fin.val hx

abbrev LastData (n b : ℕ) :=
  Σ s : {s : Finset (Fin n) // s.Nonempty}, Onto (n-s.val.card) b

def assemble {n b : ℕ} (v : LastData n b) : Onto n (b+1) :=
  ⟨appendLast v.1.val v.2.val, append_surjective v.1.property v.2.property⟩

/-- Bijection choosing the nonempty last block and the ordered partition on its complement. -/
def lastBlockEquiv (n b : ℕ) : LastData n b ≃ Onto n (b+1) :=
  Equiv.ofBijective assemble (by
    constructor
    · rintro ⟨s,g⟩ ⟨t,h⟩ heq
      have he : appendLast s.val g.val = appendLast t.val h.val := congrArg Subtype.val heq
      have hst : s = t := Subtype.ext (by
        have hc := congrArg (fun f ↦ block f (Fin.last b)) he
        simpa [block_append_last] using hc)
      subst t
      congr 1
      apply Subtype.ext
      funext y
      let x' := remainingLabels s.val y
      have hn : x'.val ∉ s.val := mem_compl.mp x'.property
      have hy := congrFun he x'.val
      simpa [appendLast, hn, x'] using hy
    · intro f
      let s := block f.val (Fin.last b)
      have hs : s.Nonempty := card_pos.mp (block_positive f.property _)
      refine ⟨⟨⟨s,hs⟩, ⟨removeLast f.val s rfl, remove_surjective f s rfl⟩⟩, ?_⟩
      exact Subtype.ext (append_remove f.val s rfl))

open Polynomial

/-- Weighted sum for a prescribed number of ordered nonempty blocks. -/
def blockRow (n b j : ℕ) : ℝ[X] := ∑ f : Onto n b, X ^ (large f.val j).card

theorem blockRow_last (n b j : ℕ) : blockRow n (b+1) j =
    ∑ s : {s : Finset (Fin n) // s.Nonempty},
      blockRow (n-s.val.card) b j * X^(if j ≤ s.val.card then 1 else 0) := by
  classical
  unfold blockRow
  rw [← (lastBlockEquiv n b).sum_comp]
  rw [Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro s
  rw [sum_mul]
  apply Fintype.sum_congr
  intro g
  change X ^ (large (appendLast s.val g.val) j).card = _
  rw [large_append_card, pow_add]

#print axioms large_append_card
#print axioms lastBlockEquiv
#print axioms blockRow_last

end OrderedPartitions
