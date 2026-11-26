import OrderedPartitions.HardRodRightBrackets
import OrderedPartitions.TwoPolePhase
import OrderedPartitions.TwoPolePhaseStrips

/-! Full polynomial root counts and interlacing from a phase traversal. -/

namespace OrderedPartitions.TwoPolePhase
open Real Set Polynomial InterlacingStep RootTracking

private theorem quarter_bound : (1/4 : ℝ) < cos (π/4) := by
  rw [cos_pi_div_four]
  have sq := Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))
  have ps := Real.sqrt_nonneg 2
  by_contra! h
  nlinarith

private theorem sin_in_strip {k : ℕ} {ψ : ℝ}
    (lo : (k:ℝ)*π+π/4 ≤ ψ) (hi : ψ ≤ (k:ℝ)*π+(π-π/4)) :
    0 < (-1:ℝ)^k * sin ψ := by
  let α := ψ - (k:ℝ)*π
  have abs_phase : 0 < sin α := sin_pos_of_pos_of_lt_pi
    (by dsimp [α]; linarith [pi_pos]) (by dsimp [α]; linarith [pi_pos])
  have trig := sin_add_nat_mul_pi α k
  have cancel : α+(k:ℝ)*π=ψ := by dsimp [α]; ring
  rw [cancel] at trig
  rw [trig]
  rcases neg_one_pow_eq_or ℝ k with parity | parity <;> rw [parity] <;> simpa using abs_phase

private theorem open_root {p : ℝ[X]} {a b : ℝ} (order : a < b)
    (sign : p.eval a * p.eval b < 0) : ∃ x, x ∈ Ioo a b ∧ p.eval x = 0 := by
  rcases mul_neg_iff.mp sign with ⟨apos, bneg⟩ | ⟨aneg, bpos⟩
  · exact intermediate_value_Ioo' order.le p.continuous.continuousOn
      (show 0 ∈ Ioo (p.eval b) (p.eval a) from ⟨bneg, apos⟩)
  · exact intermediate_value_Ioo order.le p.continuous.continuousOn
      (show 0 ∈ Ioo (p.eval a) (p.eval b) from ⟨aneg, bpos⟩)

private theorem root_in_strip {p : ℝ[X]} {k : ℕ} {l r A B E F : ℝ} (lt : l < r)
    (posA : 0 < A) (posB : 0 < B) (errE : |E| ≤ 1/4) (errF : |F| ≤ 1/4)
    (at_l : A*p.eval l = -cos ((k:ℝ)*π+(π-π/4))+E)
    (at_r : B*p.eval r = -cos ((k:ℝ)*π+π/4)+F) :
    ∃ x, x ∈ Ioo l r ∧ p.eval x = 0 := by
  rw [add_comm ((k:ℝ)*π), cos_add_nat_mul_pi, cos_pi_sub] at at_l
  rw [add_comm ((k:ℝ)*π), cos_add_nat_mul_pi] at at_r
  obtain ⟨El, Er⟩ := abs_le.mp errE
  obtain ⟨Fl, Fr⟩ := abs_le.mp errF
  have normOpp : (A*p.eval l)*(B*p.eval r) < 0 := by
    rcases neg_one_pow_eq_or ℝ k with parity | parity <;> rw [parity] at at_l at_r
    · exact mul_neg_of_pos_of_neg (by linarith [quarter_bound]) (by linarith [quarter_bound])
    · exact mul_neg_of_neg_of_pos (by linarith [quarter_bound]) (by linarith [quarter_bound])
  rw [show (A*p.eval l)*(B*p.eval r) = (A*B)*(p.eval l*p.eval r) by ring] at normOpp
  exact open_root lt (neg_of_mul_neg_right normOpp (mul_pos posA posB).le)

/-- A continuous phase whose endpoint values cover the quarter-offset strips
locates all roots of the old row and specifies the sign of the sine at each root.
The domain is the original negative variable, oriented from left to right. -/
theorem root_array_of_phase {d : ℕ} {p : ℝ[X]} {a b : ℝ} {ψ E scale : ℝ → ℝ}
    (p_degree : p.natDegree = d) (p_nonzero : p ≠ 0) (ab : a < b) (b_neg : b < 0)
    (phase : ContinuousOn ψ (Icc a b))
    (front : (d:ℝ)*π+(π-π/4) < ψ a) (back : ψ b < π+π/4)
    (model : ∀ x ∈ Icc a b, 0 < scale x ∧ |E x| ≤ 1/4 ∧
      scale x*p.eval x = -cos (ψ x)+E x) :
    ∃ xs : Fin d → ℝ, RootArray p xs ∧
      ∀ i, xs i ∈ Icc a b ∧ 0 < (-1:ℝ)^(d-i.val)*sin (ψ (xs i)) := by
  let k := fun i : Fin d ↦ d-i.val
  let lo := fun i : Fin d ↦ (k i:ℝ)*π+π/4
  let hi := fun i : Fin d ↦ (k i:ℝ)*π+(π-π/4)
  have strip (i : Fin d) : lo i < hi i := by dsimp [lo, hi]; linarith [pi_pos]
  have rank (i : Fin d) : (1:ℝ) ≤ k i ∧ (k i:ℝ) ≤ d := by
    constructor <;> exact_mod_cast (by dsimp [k]; have := i.isLt; omega)
  have ordered (i j : Fin d) (ij : i < j) : hi j < lo i := by
    have hNat : k j+1 ≤ k i := by
      dsimp [k]
      have one := i.isLt
      have two := j.isLt
      have order : i.val < j.val := ij
      omega
    have h : (k j:ℝ)+1 ≤ (k i:ℝ) := by exact_mod_cast hNat
    have steps := mul_le_mul_of_nonneg_right h pi_pos.le
    dsimp [hi, lo]
    linarith [pi_pos]
  have left (i : Fin d) : hi i < ψ a := by
    have bnd := mul_le_mul_of_nonneg_right (rank i).2 pi_pos.le
    dsimp [hi]
    linarith
  have right (i : Fin d) : ψ b < lo i := by
    have bnd := mul_le_mul_of_nonneg_right (rank i).1 pi_pos.le
    dsimp [lo]
    linarith
  obtain ⟨l, r, good, disjoint⟩ := strips_of_endpoints ab phase strip ordered left right
  have point (i : Fin d) : ∃ x, x ∈ Ioo (l i) (r i) ∧ p.eval x = 0 := by
    obtain ⟨al, lr, rb, fl, fr, _⟩ := good i
    obtain ⟨pl, el, ml⟩ := model (l i) ⟨al.le, (lr.trans rb).le⟩
    obtain ⟨pr, er, mr⟩ := model (r i) ⟨(al.trans lr).le, rb.le⟩
    rw [fl] at ml
    rw [fr] at mr
    exact root_in_strip lr pl pr el er ml mr
  choose xs hxs using point
  have inside (i : Fin d) : xs i ∈ Icc a b :=
    ⟨((good i).1.trans (hxs i).1.1).le, ((hxs i).1.2.trans (good i).2.2.1).le⟩
  refine ⟨xs, ⟨?_, fun i ↦ (inside i).2.trans_lt b_neg, p_nonzero, p_degree,
    fun i ↦ (hxs i).2⟩, ?_⟩
  · intro i j ij
    exact (hxs i).1.2.trans ((disjoint i j ij).trans (hxs j).1.1)
  · intro i
    have loc := (good i).2.2.2.2.2 (Ioo_subset_Icc_self (hxs i).1)
    exact ⟨inside i, sin_in_strip loc.1 loc.2⟩

/-- A full degree count plus sign transfer gives the exact interlacing order.
Only the sine of the phase increment is required to be positive. -/
theorem ordered_pair_of_phase {d : ℕ} {p q : ℝ[X]} {a b : ℝ}
    {ψ shift E F scaleOld scaleNew : ℝ → ℝ}
    (p_degree : p.natDegree = d) (p_nonzero : p ≠ 0)
    (q_degree : q.natDegree = d ∨ q.natDegree = d+1)
    (q_leading : 0 < q.leadingCoeff) (q_at_zero : 0 < q.eval 0)
    (ab : a < b) (b_neg : b < 0) (phase : ContinuousOn ψ (Icc a b))
    (front : (d:ℝ)*π+(π-π/4) < ψ a) (back : ψ b < π+π/4)
    (old_model : ∀ x ∈ Icc a b, 0 < scaleOld x ∧ |E x| ≤ sin (shift x)/4 ∧
      scaleOld x*p.eval x = -cos (ψ x)+E x)
    (new_model : ∀ x ∈ Icc a b, 0 < sin (shift x) ∧ 0 < scaleNew x ∧
      |F x| ≤ sin (shift x)/4 ∧ scaleNew x*q.eval x = -cos (ψ x+shift x)+F x) :
    OrderedPair d p q := by
  obtain ⟨xs, old, parity⟩ :=
    root_array_of_phase p_degree p_nonzero ab b_neg phase front back (E := E)
      (scale := scaleOld) (fun x hx ↦ by
        obtain ⟨pos, err, model⟩ := old_model x hx
        exact ⟨pos, by linarith [sin_le_one (shift x)], model⟩)
  have newSign (i : Fin d) : 0 < (-1:ℝ)^(d-i.val)*q.eval (xs i) := by
    obtain ⟨loc, sine⟩ := parity i
    obtain ⟨_, eo, before⟩ := old_model (xs i) loc
    obtain ⟨posShift, posScale, en, after⟩ := new_model (xs i) loc
    have zero : cos (ψ (xs i)) = E (xs i) := by rw [old.zeros i] at before; linarith
    have sg := next_sign posShift zero eo en
    rw [← after] at sg
    have product : 0 < ((-1:ℝ)^(d-i.val)*sin (ψ (xs i))) *
        (scaleNew (xs i)*((-1:ℝ)^(d-i.val)*q.eval (xs i))) := by
      rcases neg_one_pow_eq_or ℝ (d-i.val) with e | e <;> rw [e] <;> linarith only [sg]
    exact pos_of_mul_pos_right (pos_of_mul_pos_right product sine.le) posScale.le
  refine ⟨xs, old, ?_⟩
  rcases q_degree with h | h
  · exact Or.inl (equal_of_alternating_sign old.ordered old.negative q_at_zero h newSign)
  · exact Or.inr (rise_of_alternating_sign old.ordered old.negative q_leading q_at_zero h newSign)

#print axioms root_array_of_phase
#print axioms ordered_pair_of_phase

end OrderedPartitions.TwoPolePhase
