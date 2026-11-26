import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-! Ordered set partitions are equivalently surjections from the labels to the
ordered set of block positions. Fibers are unordered sets of original labels. -/

noncomputable section
open Finset
namespace OrderedPartitions

def block {n b : ℕ} (f : Fin n → Fin b) (i : Fin b) : Finset (Fin n) :=
  univ.filter fun x ↦ f x = i

def large {n b : ℕ} (f : Fin n → Fin b) (j : ℕ) : Finset (Fin b) :=
  univ.filter fun i ↦ j ≤ (block f i).card

def Layer (n b j d : ℕ) := {f : Fin n → Fin b // Function.Surjective f ∧ (large f j).card = d}

instance (n b j d : ℕ) : Fintype (Layer n b j d) := by classical unfold Layer; infer_instance

/-- The exact number of ordered labeled set partitions with exactly d large blocks. -/
def count (n j d : ℕ) : ℕ := ∑ b ∈ range (n+1), Fintype.card (Layer n b j d)

theorem total_sizes {n b : ℕ} (f : Fin n → Fin b) : ∑ i, (block f i).card = n := by
  simpa [block] using
    (card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := f) (fun _ _ ↦ mem_univ _)).symm

theorem block_positive {n b : ℕ} {f : Fin n → Fin b} (hf : Function.Surjective f) (i : Fin b) :
    0 < (block f i).card := by
  obtain ⟨x, hx⟩ := hf i
  exact card_pos.mpr ⟨x, by simp [block, hx]⟩

theorem capacity {n b j : ℕ} (hj : 1 ≤ j) {f : Fin n → Fin b} (hf : Function.Surjective f) :
    b + (large f j).card * (j-1) ≤ n := by
  have point (i : Fin b) : 1 + (if i ∈ large f j then j-1 else 0) ≤ (block f i).card := by
    split_ifs with h
    · have hi : j ≤ (block f i).card := (mem_filter.mp h).2
      omega
    · exact block_positive hf i
  calc
    _ = ∑ i : Fin b, (1 + (if i ∈ large f j then j-1 else 0)) := by
      simp [sum_add_distrib, sum_ite_mem]
    _ ≤ ∑ i : Fin b, (block f i).card := sum_le_sum fun i _ ↦ point i
    _ = _ := total_sizes _

theorem first_jump_two_blocks {b j : ℕ} (hj : 1 ≤ j) (f : Layer (2*j) b j 2) : b = 2 := by
  have h := capacity hj f.property.1
  have h' := card_le_univ (large f.val j)
  rw [f.property.2] at h h'
  simp only [Fintype.card_fin] at h'
  omega

/-- At the first jump both blocks have exactly the cutoff size. -/
theorem two_sizes {j : ℕ} (f : Layer (2*j) 2 j 2) (i : Fin 2) :
    (block f.val i).card = j := by
  have all := eq_univ_of_card (s := large f.val j) (by simpa using f.property.2)
  have big (i : Fin 2) : j ≤ (block f.val i).card :=
    (mem_filter.mp (all ▸ mem_univ i : i ∈ large f.val j)).2
  have total := total_sizes f.val
  rw [Fin.sum_univ_two] at total
  have h0 := big 0
  have h1 := big 1
  rcases (show i=0 ∨ i=1 by omega) with rfl | rfl <;> omega

private def splitSet {j : ℕ} (s : Finset (Fin (2*j))) (x : Fin (2*j)) : Fin 2 :=
  if x ∈ s then 0 else 1

private theorem split_zero {j : ℕ} (s : Finset (Fin (2*j))) : block (splitSet s) 0 = s := by
  ext x
  by_cases h : x ∈ s <;> simp [block, splitSet, h]

private theorem split_one {j : ℕ} (s : Finset (Fin (2*j))) : block (splitSet s) 1 = sᶜ := by
  ext x
  by_cases h : x ∈ s <;> simp [block, splitSet, h]

private def fromSet {j : ℕ} (hj : 1 ≤ j)
    (s : ↥((univ : Finset (Fin (2*j))).powersetCard j)) : Layer (2*j) 2 j 2 := by
  have hs := (mem_powersetCard.mp s.property).2
  have hc : s.valᶜ.card = j := by rw [card_compl, Fintype.card_fin, hs]; omega
  have sizes (i : Fin 2) : (block (splitSet s.val) i).card = j := by
    rcases (show i=0 ∨ i=1 by omega) with rfl | rfl
    · simpa only [split_zero] using hs
    · simpa only [split_one] using hc
  refine ⟨splitSet s.val, ?_, ?_⟩
  · intro i
    have hpos : 0 < (block (splitSet s.val) i).card := by rw [sizes]; omega
    obtain ⟨x,hx⟩ := card_pos.mp hpos
    exact ⟨x,(mem_filter.mp hx).2⟩
  · have : large (splitSet s.val) j = univ := by ext i; simp [large, sizes]
    simp [this]

/-- A first-jump partition is determined by the j labels in its first block.
The second block is the complement; swapping these blocks is a different partition. -/
def firstJumpEquiv {j : ℕ} (hj : 1 ≤ j) :
    Layer (2*j) 2 j 2 ≃ ↥((univ : Finset (Fin (2*j))).powersetCard j) where
  toFun f := ⟨block f.val 0, mem_powersetCard.mpr ⟨subset_univ _, two_sizes f 0⟩⟩
  invFun := fromSet hj
  left_inv f := by
    apply Subtype.ext
    funext x
    change splitSet (block f.val 0) x = f.val x
    by_cases h : f.val x = 0
    · simp [splitSet, block, h]
    · have h' : f.val x = 1 := by omega
      simp [splitSet, block, h']
  right_inv s := Subtype.ext (split_zero s.val)

theorem first_jump_count {j : ℕ} (hj : 1 ≤ j) : count (2*j) j 2 = (2*j).choose j := by
  unfold count
  rw [sum_eq_single_of_mem 2 (mem_range.mpr (by omega))]
  · rw [Fintype.card_congr (firstJumpEquiv hj), Fintype.card_coe, card_powersetCard,
      card_univ, Fintype.card_fin]
  · intro b _ hb
    exact Fintype.card_eq_zero_iff.mpr ⟨fun f ↦ hb (first_jump_two_blocks hj f)⟩

/-- d large blocks require at least d*j labels. -/
theorem labels_needed {n b j d : ℕ} (hj : 1 ≤ j) (f : Layer n b j d) : d*j ≤ n := by
  have cap := capacity hj f.property.1
  rw [f.property.2] at cap
  have db := card_le_univ (large f.val j)
  rw [f.property.2, Fintype.card_fin] at db
  calc
    d*j = d+d*(j-1) := by nth_rw 1 [show j=(j-1)+1 by omega]; ring
    _ ≤ b+d*(j-1) := Nat.add_le_add_right db _
    _ ≤ _ := cap

theorem count_above_degree {n j d : ℕ} (hj : 1 ≤ j) (h : n < d*j) : count n j d = 0 := by
  apply sum_eq_zero
  intro b _
  exact Fintype.card_eq_zero_iff.mpr ⟨fun f ↦ (Nat.not_lt_of_ge (labels_needed hj f)) h⟩

private theorem count_pos_of_layer {n b j d : ℕ} (hb : b ≤ n) (f : Layer n b j d) :
    0 < count n j d := by
  have positive : 0 < Fintype.card (Layer n b j d) := Fintype.card_pos_iff.mpr ⟨f⟩
  exact positive.trans_le (single_le_sum (f := fun b ↦ Fintype.card (Layer n b j d))
    (fun _ _ ↦ Nat.zero_le _) (mem_range.mpr (by omega)))

theorem count_zero_positive (n : ℕ) {j : ℕ} (hj : 2 ≤ j) : 0 < count n j 0 := by
  apply count_pos_of_layer (b := n) (le_refl _)
  refine ⟨id, Function.surjective_id, ?_⟩
  have sizes (i : Fin n) : block id i = {i} := by ext x; simp [block]
  have h : large (id : Fin n → Fin n) j = ∅ := by
    ext i
    simp [large, sizes, show ¬ j ≤ 1 by omega]
  rw [h, card_empty]

theorem count_one_positive {n j : ℕ} (hj : 1 ≤ j) (hn : j ≤ n) : 0 < count n j 1 := by
  apply count_pos_of_layer (b := 1) (by omega)
  let f : Fin n → Fin 1 := fun _ ↦ 0
  have sz (i : Fin 1) : (block f i).card = n := by
    have hi : i=0 := Subsingleton.elim _ _
    simp [block, f, hi]
  refine ⟨f, fun i ↦ ⟨⟨0, by omega⟩, Subsingleton.elim _ _⟩, ?_⟩
  have h : large f j = univ := by ext i; simp [large, sz, hn]
  rw [h, card_univ, Fintype.card_fin]

#print axioms count_above_degree
#print axioms count_zero_positive
#print axioms count_one_positive
#print axioms capacity
#print axioms first_jump_two_blocks
#print axioms firstJumpEquiv
#print axioms first_jump_count

end OrderedPartitions
