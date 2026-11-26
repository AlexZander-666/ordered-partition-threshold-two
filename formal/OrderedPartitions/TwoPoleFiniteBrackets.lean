import OrderedPartitions.TwoPoleFiniteRows
import OrderedPartitions.HardRodRightBrackets

namespace OrderedPartitions.TwoPoleFinite
open Finset Polynomial InterlacingStep RootTracking

def ratEval (T : Table) (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ range (n+1), (cell T n k:ℚ)*x^k

theorem ratEval_cast {T : Table} {n N : ℕ} (hT : checkTable T 2 N=true) (hn : n≤N) (x : ℚ) :
    (ratEval T n x:ℝ) = (row n 2).eval (x:ℝ) := by
  rw [← tablePoly_original (by decide : 1≤2) hT hn,tablePoly,eval_finsetSum]
  simp only [eval_mul,eval_C,eval_pow,eval_X,ratEval,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_natCast]

abbrev Boxes := List (ℚ×ℚ)
def box (B : Boxes) (i : ℕ) := B[i]?.getD (0,0)

def validBoxes (T : Table) (n d : ℕ) (B : Boxes) : Prop :=
  0 < cell T n d ∧ ∀ i : Fin d,
    (box B i).1 < (box B i).2 ∧ (box B i).2 ≤ 0 ∧
    ratEval T n (box B i).1 * ratEval T n (box B i).2 < 0 ∧
    ∀ k : Fin d, i<k → (box B i).2 ≤ (box B k).1

instance (T : Table) (n d : ℕ) (B : Boxes) : Decidable (validBoxes T n d B) := by
  unfold validBoxes
  infer_instance

private theorem boxed_root {p : ℝ[X]} {a b : ℝ} (ab : a < b) (bad : p.eval a*p.eval b<0) :
    ∃ x, a < x ∧ x < b ∧ p.eval x=0 := by
  rcases mul_neg_iff.mp bad with ⟨apos,bneg⟩ | ⟨aneg,bpos⟩
  · obtain ⟨x,⟨l,r⟩,eq⟩ := intermediate_value_Ioo' ab.le p.continuous.continuousOn
      (show 0 ∈ Set.Ioo (p.eval b) (p.eval a) from ⟨bneg,apos⟩)
    exact ⟨x,l,r,eq⟩
  · obtain ⟨x,⟨l,r⟩,eq⟩ := intermediate_value_Ioo ab.le p.continuous.continuousOn
      (show 0 ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨aneg,bpos⟩)
    exact ⟨x,l,r,eq⟩

theorem original_in_boxes {T : Table} {n N d : ℕ} {B : Boxes} (hT : checkTable T 2 N=true)
    (hn : n≤N) (dval : d=n/2) (cert : validBoxes T n d B) :
    ∃ xs : Fin d→ℝ, RootArray (row n 2) xs ∧
      ∀ i : Fin d, ((box B i).1:ℝ)<xs i ∧ xs i<((box B i).2:ℝ) := by
  obtain ⟨top,points⟩ := cert
  have probe (i : Fin d) := points i
  have each (i : Fin d) : ∃ x : ℝ, ((box B i).1:ℝ)<x ∧ x<((box B i).2:ℝ) ∧ (row n 2).eval x=0 := by
    apply boxed_root (by exact_mod_cast (probe i).1)
    rw [← ratEval_cast hT hn,← ratEval_cast hT hn]
    exact_mod_cast (probe i).2.2.1
  choose xs lo hi zeros using each
  have pos : 0<(row n 2).coeff d := by
    rw [coeff_row (by decide : 1≤2),← table_sound (by decide : 1≤2) hT hn (by omega : d≤N)]
    exact_mod_cast top
  have degree : (row n 2).natDegree=d := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ pos.ne'
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro h high
    simp [coeff_row (by decide : 1≤2),count_above_degree (j:=2) (by decide) (by omega : n<h*2)]
  refine ⟨xs,⟨?_,?_,?_,degree,zeros⟩,fun i ↦ ⟨lo i,hi i⟩⟩
  · intro i k lt
    exact (hi i).trans_le ((by exact_mod_cast (probe i).2.2.2 k lt : ((box B i).2:ℝ)≤((box B k).1:ℝ)).trans (lo k).le)
  · intro i
    exact (hi i).trans_le (by exact_mod_cast (probe i).2.1)
  · intro hz
    simp [hz] at pos

def stays (d : ℕ) (B C : Boxes) : Prop :=
  (∀ i : Fin d, (box B i).2 ≤ (box C i).1) ∧
  (∀ i k : Fin d, i<k → (box C i).2 ≤ (box B k).1)

def rises (d : ℕ) (B C : Boxes) : Prop :=
  ∀ i : Fin d, (box C i).2 ≤ (box B i).1 ∧ (box B i).2 ≤ (box C (i.val+1)).1

instance (d : ℕ) (B C : Boxes) : Decidable (stays d B C) := by unfold stays;infer_instance
instance (d : ℕ) (B C : Boxes) : Decidable (rises d B C) := by unfold rises;infer_instance

theorem stay_pair {T : Table} {N n m d : ℕ} {B C : Boxes} (hT : checkTable T 2 N=true)
    (hn : n≤N) (hm : m≤N) (dn : d=n/2) (dm : d=m/2)
    (p : validBoxes T n d B) (q : validBoxes T m d C) (ord : stays d B C) :
    OrderedPair d (row n 2) (row m 2) := by
  obtain ⟨xs,hx,xb⟩ := original_in_boxes hT hn dn p
  obtain ⟨ys,hy,yb⟩ := original_in_boxes hT hm dm q
  refine ⟨xs,hx,Or.inl ⟨ys,hy,fun i ↦ ?_,fun i k lt ↦ ?_⟩⟩
  · exact (xb i).2.trans_le ((by exact_mod_cast ord.1 i : ((box B i).2:ℝ)≤((box C i).1:ℝ)).trans (yb i).1.le)
  · exact (yb i).2.trans_le ((by exact_mod_cast ord.2 i k lt : ((box C i).2:ℝ)≤((box B k).1:ℝ)).trans (xb k).1.le)

theorem rise_pair {T : Table} {N n m d : ℕ} {B C : Boxes} (hT : checkTable T 2 N=true)
    (hn : n≤N) (hm : m≤N) (dn : d=n/2) (dm : d+1=m/2)
    (p : validBoxes T n d B) (q : validBoxes T m (d+1) C) (ord : rises d B C) :
    OrderedPair d (row n 2) (row m 2) := by
  obtain ⟨xs,hx,xb⟩ := original_in_boxes hT hn dn p
  obtain ⟨ys,hy,yb⟩ := original_in_boxes hT hm dm q
  refine ⟨xs,hx,Or.inr ⟨ys,hy,fun i ↦ ⟨?_,?_⟩⟩⟩
  · exact (yb i.castSucc).2.trans_le ((by exact_mod_cast (ord i).1 : ((box C i).2:ℝ)≤((box B i).1:ℝ)).trans (xb i).1.le)
  · exact (xb i).2.trans_le ((by exact_mod_cast (ord i).2 : ((box B i).2:ℝ)≤((box C (i.val+1)).1:ℝ)).trans (yb i.succ).1.le)

#print axioms original_in_boxes
#print axioms stay_pair
#print axioms rise_pair
end OrderedPartitions.TwoPoleFinite
