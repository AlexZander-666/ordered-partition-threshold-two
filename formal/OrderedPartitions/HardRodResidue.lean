import OrderedPartitions.HardRodInterlacing

noncomputable section
namespace OrderedPartitions.HardRod
open Polynomial InterlacingStep

private theorem derivative_at_root {d : ℕ} {q : ℝ[X]} {ys : Fin (d+1)→ℝ}
    (hq : RootArray q ys) (i : Fin (d+1)) :
    q.derivative.eval (ys i) = q.leadingCoeff*∏ j : Fin d, (ys i-ys (i.succAbove j)) := by
  have fac : q = C q.leadingCoeff * ∏ j, (X-C (ys j)) := by
    simpa only [List.map_ofFn,List.prod_ofFn,Function.comp_apply] using hq.exact.factor
  have fac' : q = C q.leadingCoeff * ((X-C (ys i)) * ∏ j : Fin d, (X-C (ys (i.succAbove j)))) := by
    simpa only [Fin.prod_univ_succAbove (fun j ↦ X-C (ys j)) i] using fac
  conv_lhs => rw [fac']
  simp [Polynomial.derivative_mul,Polynomial.eval_prod]

/-- For a strictly interlacing lower row the residues in p/q are all positive. -/
theorem positive_residue {d : ℕ} {p q : ℝ[X]} {xs : Fin d→ℝ} {ys : Fin (d+1)→ℝ}
    (hp : RootArray p xs) (hq : RootArray q ys) (ord : Interlaces xs ys)
    (lp : 0<p.leadingCoeff) (lq : 0<q.leadingCoeff) (i : Fin (d+1)) :
    0<p.eval (ys i)/q.derivative.eval (ys i) := by
  apply div_pos_iff.mpr
  apply mul_pos_iff.mp
  rw [hp.eval_prod,derivative_at_root hq]
  have pairs (j : Fin d) : 0 < (ys i-xs j)*(ys i-ys (i.succAbove j)) := by
    by_cases h : j.castSucc < i
    · have h' : j.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp h
      rw [Fin.succAbove_of_castSucc_lt _ _ h]
      exact mul_pos (sub_pos.mpr ((ord j).2.trans_le (hq.ordered.monotone h'))) (sub_pos.mpr (hq.ordered h))
    · have h' := le_of_not_gt h
      rw [Fin.succAbove_of_le_castSucc _ _ h']
      exact mul_pos_of_neg_of_neg (sub_neg.mpr ((hq.ordered.monotone h').trans_lt (ord j).1))
        (sub_neg.mpr (hq.ordered (h'.trans_lt Fin.castSucc_lt_succ)))
  have pos := mul_pos (mul_pos lp lq) (Finset.prod_pos (s:=Finset.univ) (fun j _ ↦ pairs j))
  rw [Finset.prod_mul_distrib] at pos
  linarith only [pos,show p.leadingCoeff*q.leadingCoeff*
    ((∏ j, (ys i-xs j))*(∏ j : Fin d, (ys i-ys (i.succAbove j)))) =
    (p.leadingCoeff*∏ j, (ys i-xs j))*(q.leadingCoeff*∏ j : Fin d, (ys i-ys (i.succAbove j))) by ring]

theorem phi_residue (d : ℕ) {N : ℕ} (dN : d+1≤N) {x r : ℝ}
    (lo : (d:ℝ)+1<x) (hi : x≤(d:ℝ)+2) (zero : (phi N x).eval r=0) :
    0 < (phi N (x-1)).eval r / (phi N x).derivative.eval r := by
  obtain ⟨a,b,ha,hb,ord⟩ := unit_interlacing d dN lo hi
  have mem := (Polynomial.mem_roots hb.ne_zero).mpr zero
  rw [hb.exact.roots] at mem
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (show r ∈ List.ofFn b from mem)
  have sa := phi_shape (N:=N) (d:=d) (x:=x-1) (by omega) (by linarith) (by linarith)
  have sb := phi_shape (N:=N) (d:=d+1) (x:=x) dN (by push_cast;linarith) (by push_cast;linarith)
  exact positive_residue ha hb ord sa.2.1 sb.2.1 i

/-- Every shift up to one unit gives the sign opposite to the activity derivative
at every old root; both polynomials are evaluated at the same real activity. -/
theorem phi_shift_at_root (d : ℕ) {N : ℕ} (dN : d+1≤N) {x r h : ℝ}
    (lo : (d:ℝ)+1<x) (hi : x≤(d:ℝ)+2) (zero : (phi N x).eval r=0)
    (pos : 0<h) (win : h≤1) (bound : x+h≤(N:ℝ)+1) :
    (phi N x).derivative.eval r * (phi N (x+h)).eval r < 0 := by
  obtain ⟨_,b,_,hb,_⟩ := unit_interlacing d dN lo hi
  have mem := (Polynomial.mem_roots hb.ne_zero).mpr zero
  rw [hb.exact.roots] at mem
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (show r ∈ List.ofFn b from mem)
  have ratio := phi_residue d dN lo hi zero
  have opposite := phi_window_sign (hb.negative i) pos win bound zero
  rcases div_pos_iff.mp ratio with ⟨pl,ql⟩|⟨pl,ql⟩
  · exact mul_neg_of_pos_of_neg ql ((mul_neg_iff.mp opposite).resolve_right (fun w ↦ (not_lt_of_ge pl.le) w.1)).2
  · exact mul_neg_of_neg_of_pos ql ((mul_neg_iff.mp opposite).resolve_left (fun w ↦ (not_lt_of_ge pl.le) w.1)).2

#print axioms phi_shift_at_root
#print axioms positive_residue
#print axioms phi_residue
end OrderedPartitions.HardRod
