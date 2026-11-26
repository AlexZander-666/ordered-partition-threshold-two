import OrderedPartitions.HardRodPolynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas

noncomputable section
namespace OrderedPartitions.HardRod
open Finset Polynomial

theorem phi_coeff (N h : ℕ) (x : ℝ) : (phi N x).coeff h=if h≤N then rodCoeff h x else 0 := by
  simp [phi,finsetSum_coeff,coeff_monomial,mem_range]

theorem phi_one {x : ℝ} (hx : x≤1) (N : ℕ) : phi N x=1 := by
  apply Polynomial.funext
  intro y
  simp [history_eval hx]

theorem phi_stable {x : ℝ} {N K : ℕ} (hN : x≤(N:ℝ)+1) (hK : x≤(K:ℝ)+1) :
    phi N x=phi K x := by
  ext h
  rw [phi_coeff,phi_coeff]
  split_ifs with a b b
  · rfl
  · apply rodCoeff_dead (by omega)
    have p : (K:ℝ)+1≤h := by exact_mod_cast (by omega : K+1≤h)
    linarith
  · symm
    apply rodCoeff_dead (by omega)
    have p : (N:ℝ)+1≤h := by exact_mod_cast (by omega : N+1≤h)
    linarith
  · rfl

/-- At an integer x=d+1 the term of order d+1 still vanishes. -/
theorem phi_shape {N d : ℕ} {x : ℝ} (dN : d≤N) (lo : (d:ℝ)<x) (hi : x≤(d:ℝ)+1) :
    (phi N x).natDegree=d ∧ 0<(phi N x).leadingCoeff ∧ (phi N x).eval 0=1 := by
  have c : 0<(phi N x).coeff d := by
    rw [phi_coeff,if_pos dN,rodCoeff,max_eq_left (sub_nonneg.mpr lo.le)]
    positivity
  have deg : (phi N x).natDegree=d := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ c.ne'
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro h dh
    rw [phi_coeff]
    split_ifs
    · apply rodCoeff_dead (by omega)
      have p : (d:ℝ)+1≤h := by exact_mod_cast (show d+1≤h by omega)
      linarith
    · rfl
  refine ⟨deg,by simpa [leadingCoeff,deg] using c,?_⟩
  rw [← coeff_zero_eq_eval_zero,phi_coeff,if_pos (Nat.zero_le _),rodCoeff_zero]

theorem phi_first_root {N : ℕ} {x : ℝ} (lo : 1<x) (hi : x≤2) (N1 : 1≤N) :
    (phi N x).eval (-(x-1)⁻¹)=0 := by
  have le : (1:ℝ)≤N := by exact_mod_cast N1
  rw [phi_stable (K:=1) (by linarith) (by norm_num;exact hi),phi_eval]
  simp [Finset.sum_range_succ,rodCoeff,max_eq_left (sub_nonneg.mpr lo.le),
    sub_ne_zero.mpr (ne_of_gt lo)]

#print axioms phi_stable
#print axioms phi_shape
end OrderedPartitions.HardRod
