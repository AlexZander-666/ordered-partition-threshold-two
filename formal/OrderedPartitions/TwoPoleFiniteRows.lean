import OrderedPartitions.QuadraticExactRows

/-! Finite natural-number certificates for arbitrary-degree original rows. -/
namespace OrderedPartitions.TwoPoleFinite
open Finset Polynomial
abbrev Table := List (List ℕ)
def cell (T : Table) (n d : ℕ) := ((T[n]?.getD [])[d]?).getD 0

def nextCell (T : Table) (j n d : ℕ) :=
  ∑ r ∈ Icc 1 n, QuadraticExact.binomial n r *
    (if j≤r then if d=0 then 0 else cell T (n-r) (d-1) else cell T (n-r) d)

def checkTable (T : Table) (j N : ℕ) : Bool :=
  (List.range (N+1)).all fun n ↦ (List.range (N+1)).all fun d ↦
    cell T n d == (if n=0 then if d=0 then 1 else 0 else nextCell T j n d)

theorem table_sound {T : Table} {j N : ℕ} (hj : 1≤j) (ht : checkTable T j N=true)
    {n d : ℕ} (hn : n≤N) (hd : d≤N) : cell T n d = count n j d := by
  have valid (i k : ℕ) (hi : i≤N) (hk : k≤N) :
      cell T i k = (if i=0 then if k=0 then 1 else 0 else nextCell T j i k) := by
    have test := List.all_eq_true.mp (List.all_eq_true.mp ht i (List.mem_range.mpr (by omega)))
      k (List.mem_range.mpr (by omega))
    exact beq_iff_eq.mp test
  induction n using Nat.strong_induction_on generalizing d with
  | h n ih =>
    rw [valid n d hn hd]
    cases n with
    | zero =>
      have eqn := coeff_row hj d (n:=0)
      rw [row_zero hj,coeff_one] at eqn
      simp only [if_true] 
      by_cases hz : d=0 <;> simp [hz] at eqn ⊢ <;> exact_mod_cast eqn
    | succ n =>
      rw [if_neg (Nat.succ_ne_zero _),nextCell,count_recurrence n hj d]
      apply sum_congr rfl
      intro r hr
      have bounds := mem_Icc.mp hr
      rw [QuadraticExact.binomial_eq bounds.2]
      have earlier : n+1-r < n+1 := by omega
      apply congrArg ((n+1).choose r * ·)
      split_ifs
      · rfl
      · exact ih _ earlier (by omega) (by omega)
      · exact ih _ earlier (by omega) hd

noncomputable def tablePoly (T : Table) (n : ℕ) : ℝ[X] :=
  ∑ d ∈ range (n+1), C (cell T n d : ℝ)*X^d

theorem tablePoly_original {T : Table} {j N n : ℕ} (hj : 1≤j)
    (ht : checkTable T j N=true) (hn : n≤N) : tablePoly T n = row n j := by
  unfold tablePoly row
  apply sum_congr rfl
  intro d hd
  rw [table_sound hj ht hn ((Nat.le_of_lt_succ (mem_range.mp hd)).trans hn)]

#print axioms table_sound
#print axioms tablePoly_original
end OrderedPartitions.TwoPoleFinite
