import OrderedPartitions.HardRodDelay
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The positive-part divided powers for the finite interval hard-rod partition polynomial. -/
noncomputable section
namespace OrderedPartitions.HardRod
open Set Filter Polynomial Finset Topology

def rodCoeff (h : ℕ) (x : ℝ) : ℝ := (max (x-h) 0)^h / h.factorial

/-- Activity polynomial truncated to N. On x ≤ N+1 all omitted terms vanish. -/
def phi (N : ℕ) (x : ℝ) : ℝ[X] :=
  ∑ h ∈ range (N+1), Polynomial.monomial h (rodCoeff h x)

@[simp] theorem rodCoeff_zero (x : ℝ) : rodCoeff 0 x=1 := by simp [rodCoeff]

theorem rodCoeff_dead {h : ℕ} (hh : 0<h) {x : ℝ} (hx : x≤h) : rodCoeff h x=0 := by
  simp [rodCoeff,max_eq_right (sub_nonpos.mpr hx),zero_pow hh.ne']

theorem phi_eval (N : ℕ) (x y : ℝ) :
    (phi N x).eval y = ∑ h ∈ range (N+1), rodCoeff h x*y^h := by
  simp [phi,eval_finsetSum,eval_monomial]

theorem cont_eval (N : ℕ) (y : ℝ) : Continuous (fun x ↦ (phi N x).eval y) := by
  simp_rw [phi_eval,rodCoeff]
  fun_prop

theorem history_eval {x : ℝ} (hx : x≤1) (N : ℕ) (y : ℝ) : (phi N x).eval y=1 := by
  rw [phi_eval,sum_range_succ']
  have e : ∀ i : ℕ, rodCoeff (i+1) x=0 := fun i ↦ rodCoeff_dead (by omega) (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) i])
  simp [e]

set_option backward.isDefEq.respectTransparency false in
private theorem pospart_power (h : ℕ) (b x : ℝ) (smooth : 1<h ∨ b<x) :
    HasDerivAt (fun z : ℝ ↦ (max (z-b) 0)^h) ((h:ℝ)*(max (x-b) 0)^(h-1)) x := by
  have usual : HasDerivAt (fun t : ℝ ↦ (t-b)^h) ((h:ℝ)*(x-b)^(h-1)) x := by
    convert ((hasDerivAt_id x).sub_const b).pow h using 1 <;> first | rfl | simp
  rcases lt_trichotomy x b with l|eqn|r
  · have hh : h≠0 := by rcases smooth with _|g;omega; linarith
    have hd : h-1≠0 := by rcases smooth with _|g;omega; linarith
    rw [max_eq_right (sub_nonpos.mpr l.le),zero_pow hd,mul_zero]
    apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds l] with z hz
    simp [max_eq_right (sub_nonpos.mpr hz.le),zero_pow hh]
  · subst x
    have h2 : 1<h := smooth.resolve_right (lt_irrefl _)
    have hh : h≠0 := by omega
    have hd : h-1≠0 := by omega
    simp only [sub_self,max_self,zero_pow hd,mul_zero]
    have right : HasDerivWithinAt (fun z : ℝ ↦ (max (z-b) 0)^h) 0 (Ici b) b := by
      have phys : HasDerivAt (fun z : ℝ ↦ (z-b)^h) 0 b := by
        simpa [sub_self,zero_pow hd] using usual
      exact phys.hasDerivWithinAt.congr_of_mem (fun z hz ↦ by rw [max_eq_left (sub_nonneg.mpr (mem_Ici.mp hz))]) (by simp)
    have left : HasDerivWithinAt (fun z : ℝ ↦ (max (z-b) 0)^h) 0 (Iic b) b :=
      (hasDerivAt_const b (0:ℝ)).hasDerivWithinAt.congr_of_mem
        (fun z hz ↦ by simp [max_eq_right (sub_nonpos.mpr (mem_Iic.mp hz)),zero_pow hh]) (by simp)
    exact hasDerivWithinAt_univ.mp (Iic_union_Ici (a:=b) ▸ left.union right)
  · rw [max_eq_left (sub_nonneg.mpr r.le)]
    apply (show HasDerivAt (fun z : ℝ ↦ (z-b)^h) _ x from by simpa using usual).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds r] with z hz
    simp [max_eq_left (sub_nonneg.mpr hz.le)]

theorem coeff_deriv (h : ℕ) {x : ℝ} (hx : 1<x) :
    HasDerivAt (rodCoeff (h+1)) (rodCoeff h (x-1)) x := by
  have smooth : 1<h+1 ∨ ((h+1:ℕ):ℝ)<x := by by_cases e:h=0;subst h;simp [hx];exact Or.inl (by omega)
  have der := (pospart_power (h+1) (h+1) x (by exact_mod_cast smooth)).div_const ((h+1).factorial:ℝ)
  unfold rodCoeff
  change HasDerivAt (fun z : ℝ ↦ (max (z-((h+1:ℕ):ℝ)) 0)^(h+1) / ((h+1).factorial:ℝ)) _ x
  convert der using 1 <;> try rfl
  · funext z
    push_cast
    rfl
  · rw [Nat.factorial_succ];push_cast
    rw [show x-1-h=x-(h+1) by ring]
    field_simp

/-- Up to its exact truncation horizon the true finite partition polynomial
satisfies the delay equation, including all integral lengths strictly above one. -/
theorem phi_delay (N : ℕ) {x : ℝ} (hx : 1<x) (xN : x≤(N:ℝ)+1) (y : ℝ) :
    HasDerivAt (fun z ↦ (phi N z).eval y) (y*(phi N (x-1)).eval y) x := by
  have pn : 0<N := by
    by_contra! h
    have nR : (N:ℝ)≤0 := by exact_mod_cast h
    linarith
  have last : rodCoeff N (x-1)=0 := rodCoeff_dead pn (by linarith)
  have sh (z : ℝ) : (phi N z).eval y=1+∑ i ∈ range N,rodCoeff (i+1) z*y^(i+1) := by
    rw [phi_eval,sum_range_succ'];simp [add_comm]
  simp_rw [sh]
  have sumder := HasDerivAt.fun_sum (u:=range N)
    (fun i _ ↦ (coeff_deriv i hx).mul_const (y^(i+1)))
  convert (hasDerivAt_const x (1:ℝ)).add sumder using 1 <;> try rfl
  rw [← sh,phi_eval,sum_range_succ,last,zero_mul,add_zero,mul_sum,zero_add]
  apply sum_congr rfl
  intro i _
  rw [pow_succ];ring

theorem phi_sturm {N : ℕ} {s y : ℝ} (hy : y<0) (bound : s+1≤(N:ℝ)+1)
    (zero : (phi N s).eval y=0) :
    (phi N (s-1)).eval y*(phi N (s+1)).eval y<0 :=
  delay_sturm_sign hy (cont_eval N y) (fun t ht ↦ by rw [history_eval ht];norm_num)
    (fun _ ht hN ↦ phi_delay N ht hN y) bound zero

#print axioms coeff_deriv
#print axioms phi_delay
#print axioms phi_sturm
end OrderedPartitions.HardRod
