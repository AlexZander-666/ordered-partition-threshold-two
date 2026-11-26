import OrderedPartitions.HardRodRootTracking

noncomputable section
namespace OrderedPartitions.RootTracking
open Polynomial InterlacingStep

/-- Equal-degree orientation: each new root is immediately to the right
of its corresponding old root. -/
def RightInterlaces {d : ℕ} (xs zs : Fin d→ℝ) : Prop :=
  (∀ i, xs i < zs i) ∧ ∀ i j, i<j → zs i < xs j

/-- The two possible row orders when the upper degree stays fixed or increases by one. -/
def OrderedPair (d : ℕ) (p q : ℝ[X]) : Prop :=
  ∃ xs : Fin d→ℝ, RootArray p xs ∧
  ((∃ zs : Fin d→ℝ, RootArray q zs ∧ RightInterlaces xs zs) ∨
   (∃ zs : Fin (d+1)→ℝ, RootArray q zs ∧ Interlaces xs zs))

private theorem open_root {p : ℝ[X]} {a b : ℝ} (lt : a<b) (neg : p.eval a*p.eval b<0) :
    ∃ z, a<z ∧ z<b ∧ p.eval z=0 := by
  rcases mul_neg_iff.mp neg with ⟨u,v⟩|⟨u,v⟩
  · obtain ⟨z,⟨u',v'⟩,hz⟩ := intermediate_value_Ioo' lt.le p.continuous.continuousOn
      (show 0∈Set.Ioo (p.eval b) (p.eval a) from ⟨v,u⟩)
    exact ⟨z,u',v',hz⟩
  · obtain ⟨z,⟨u',v'⟩,hz⟩ := intermediate_value_Ioo lt.le p.continuous.continuousOn
      (show 0∈Set.Ioo (p.eval a) (p.eval b) from ⟨u,v⟩)
    exact ⟨z,u',v',hz⟩

theorem equal_of_alternating_sign {d : ℕ} {q : ℝ[X]} {xs : Fin d→ℝ}
    (mono : StrictMono xs) (negative : ∀i,xs i<0) (at_zero : 0<q.eval 0)
    (degree : q.natDegree=d) (sign : ∀i,0<(-1:ℝ)^(d-i.val)*q.eval (xs i)) :
    ∃ zs : Fin d→ℝ, RootArray q zs ∧ RightInterlaces xs zs := by
  let grid : Fin (d+1) → ℝ := Fin.snoc xs (0:ℝ)
  have gneg (i : Fin (d+1)) : grid i≤0 := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [grid]
    · simpa [grid] using (negative j).le
  have gm : StrictMono grid := by
    intro i j hij
    let k : Fin d := ⟨i.val,lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
    have eq : k.castSucc=i := Fin.ext rfl
    rw [← eq] at hij ⊢
    refine Fin.lastCases (motive:=fun j ↦ k.castSucc < j → grid k.castSucc < grid j) ?_ ?_ j hij
    · intro _;simpa [grid] using negative k
    · intro l h;simpa [grid] using mono (show k<l from h)
  have sg (i : Fin (d+1)) : 0<(-1:ℝ)^(d-i.val)*q.eval (grid i) := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [grid] using at_zero
    · simpa [grid] using sign j
  have interval (i : Fin d) : ∃u,grid i.castSucc < u ∧ u<grid i.succ ∧ q.eval u=0 := by
    apply open_root (gm Fin.castSucc_lt_succ)
    have l := sg i.castSucc
    have r := sg i.succ
    simp only [Fin.val_castSucc] at l
    simp only [Fin.val_succ] at r
    have e : d-i.val=(d-(i.val+1))+1 := by omega
    rw [e,pow_succ] at l
    rcases neg_one_pow_eq_or ℝ (d-(i.val+1)) with h|h <;> rw [h] at l r
    · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  choose zs bd using interval
  have gap {i j : Fin d} (ij : i<j) : zs i<xs j := by
    have le : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact ij
    exact (bd i).2.1.trans_le (by simpa [grid] using gm.monotone le)
  have xl (i : Fin d) : xs i<zs i := by simpa [grid] using (bd i).1
  exact ⟨zs,⟨fun i j ij ↦ (gap ij).trans (xl j),fun i ↦ (bd i).2.1.trans_le (gneg _),
    fun h ↦ at_zero.ne' (by simp [h]),degree,fun i ↦ (bd i).2.2⟩,xl,fun _ _ ij ↦ gap ij⟩

#print axioms equal_of_alternating_sign
end OrderedPartitions.RootTracking
