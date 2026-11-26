import OrderedPartitions.QuadraticRootOrder
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Order.Fin.Tuple

/-! Exact root arrays and the degree-increasing Sturm step for real polynomials. -/

open Polynomial Filter

namespace OrderedPartitions.InterlacingStep

/-- An increasing array of negative roots that accounts for the whole degree. -/
structure RootArray {d : ℕ} (p : ℝ[X]) (xs : Fin d → ℝ) : Prop where
  ordered : StrictMono xs
  negative : ∀ i, xs i < 0
  ne_zero : p ≠ 0
  degree : p.natDegree = d
  zeros : ∀ i, p.eval (xs i) = 0

/-- At a degree increase, the new roots lie on both sides of each old root. -/
def Interlaces {d : ℕ} (xs : Fin d → ℝ) (ys : Fin (d+1) → ℝ) : Prop :=
  ∀ i, ys i.castSucc < xs i ∧ xs i < ys i.succ

/-- The indexed roots give the exact multiset and the full real factorization. -/
theorem RootArray.exact {d : ℕ} {p : ℝ[X]} {xs : Fin d → ℝ} (h : RootArray p xs) :
    QuadraticOrder.ExactRoots p (List.ofFn xs) := by
  classical
  let L := List.ofFn xs
  have nodup : L.Nodup := List.nodup_ofFn.mpr h.ordered.injective
  have card : p.natDegree ≤ L.toFinset.card := by
    rw [List.toFinset_card_of_nodup nodup, h.degree, List.length_ofFn]
  have roots := roots_eq_of_natDegree_le_card_of_ne_zero (S := L.toFinset)
    (fun x hx ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hx)
      exact h.zeros i) card h.ne_zero
  have eq : p.roots = (L : Multiset ℝ) := by
    rw [roots, List.toFinset_val, List.dedup_eq_self.mpr nodup]
  have split : p.Splits := splits_iff_card_roots.mpr (by simp [eq, L, h.degree])
  exact ⟨eq, by simpa [eq, L] using split.eq_prod_roots⟩

theorem RootArray.eval_prod {d : ℕ} {p : ℝ[X]} {xs : Fin d → ℝ} (h : RootArray p xs)
    (x : ℝ) : p.eval x = p.leadingCoeff * ∏ i, (x - xs i) := by
  have fac := congrArg (Polynomial.eval x) h.exact.factor
  simpa only [eval_mul, eval_C, List.map_ofFn, List.prod_ofFn, Polynomial.eval_prod,
    Function.comp_apply, eval_sub, eval_X] using fac

/-- All roots in the complete factorization have multiplicity one. -/
theorem RootArray.roots_nodup {d : ℕ} {p : ℝ[X]} {xs : Fin d → ℝ} (h : RootArray p xs) :
    p.roots.Nodup := by
  rw [h.exact.roots]
  exact List.nodup_ofFn.mpr h.ordered.injective

private theorem left_probe {p : ℝ[X]} {d : ℕ} (degree : p.natDegree = d) (hd : 0 < d)
    (lead : 0 < p.leadingCoeff) (a : ℝ) : ∃ x < a, 0 < (-1) ^ d * p.eval x := by
  let reflected := p.comp (-X)
  have deg : 0 < reflected.degree := natDegree_pos_iff_degree_pos.mp (by
    simpa [reflected, natDegree_comp, degree] using hd)
  have coeff : reflected.leadingCoeff = p.leadingCoeff * (-1) ^ d := by
    simp [reflected, leadingCoeff_comp (show (-X : ℝ[X]).natDegree ≠ 0 by simp), degree]
  have at_neg (y : ℝ) : reflected.eval y = p.eval (-y) := by simp [reflected, eval_comp]
  rcases Nat.even_or_odd d with even | odd
  · have h : 0 ≤ reflected.leadingCoeff := by rw [coeff, even.neg_one_pow, mul_one]; exact lead.le
    have ev := (reflected.tendsto_atTop_of_leadingCoeff_nonneg deg h).eventually (eventually_gt_atTop (0 : ℝ))
    obtain ⟨y, hy, pos⟩ := ((eventually_gt_atTop (-a)).and ev).exists
    exact ⟨-y, by linarith, by simpa [even.neg_one_pow, ← at_neg] using pos⟩
  · have h : reflected.leadingCoeff ≤ 0 := by rw [coeff, odd.neg_one_pow, mul_neg_one]; linarith
    have ev := (reflected.tendsto_atBot_of_leadingCoeff_nonpos deg h).eventually (eventually_lt_atBot (0 : ℝ))
    obtain ⟨y, hy, neg⟩ := ((eventually_gt_atTop (-a)).and ev).exists
    exact ⟨-y, by linarith, by simpa [odd.neg_one_pow, ← at_neg] using neg⟩

private theorem between {p : ℝ[X]} {a b : ℝ} (order : a < b)
    (sign : p.eval a * p.eval b < 0) : ∃ x, a < x ∧ x < b ∧ p.eval x = 0 := by
  rcases mul_neg_iff.mp sign with ⟨apos, bneg⟩ | ⟨aneg, bpos⟩
  · obtain ⟨x, ⟨left, right⟩, hz⟩ := intermediate_value_Ioo' order.le p.continuous.continuousOn
      (show 0 ∈ Set.Ioo (p.eval b) (p.eval a) from ⟨bneg, apos⟩)
    exact ⟨x, left, right, hz⟩
  · obtain ⟨x, ⟨left, right⟩, hz⟩ := intermediate_value_Ioo order.le p.continuous.continuousOn
      (show 0 ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨aneg, bpos⟩)
    exact ⟨x, left, right, hz⟩

private theorem alternate {a b : ℝ} {k : ℕ}
    (ha : 0 < (-1 : ℝ) ^ (k+1) * a) (hb : 0 < (-1 : ℝ) ^ k * b) : a*b < 0 := by
  rcases neg_one_pow_eq_or ℝ k with sign | sign
  · rw [pow_succ, sign] at ha
    rw [sign] at hb
    simpa using mul_neg_of_neg_of_pos (by simpa using ha : a < 0) (by simpa using hb : 0 < b)
  · rw [pow_succ, sign] at ha
    rw [sign] at hb
    simpa using mul_neg_of_pos_of_neg (by simpa using ha : 0 < a) (by simpa using hb : b < 0)

/-- Alternating strict signs, with the last test negative, locate all roots of the new row.
The empty list of tests is allowed and gives the first linear root. -/
theorem rise_of_alternating_sign {d : ℕ} {r : ℝ[X]} {ys : Fin d → ℝ}
    (ordered : StrictMono ys) (negative : ∀ i, ys i < 0) (lead : 0 < r.leadingCoeff)
    (at_zero : 0 < r.eval 0) (degree : r.natDegree = d+1)
    (sign : ∀ i : Fin d, 0 < (-1 : ℝ) ^ (d-i.val) * r.eval (ys i)) :
    ∃ zs : Fin (d+1) → ℝ, RootArray r zs ∧ Interlaces ys zs := by
  let tail : Fin (d+1) → ℝ := Fin.snoc ys 0
  have tail_nonpos (i : Fin (d+1)) : tail i ≤ 0 := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [tail]
    · simpa [tail] using (negative j).le
  have tail_ordered : StrictMono tail := by
    intro i j hij
    let k : Fin d := ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
    have cast : k.castSucc = i := Fin.ext rfl
    have hkj : k.castSucc < j := by rwa [cast]
    rw [← cast]
    refine Fin.lastCases (motive := fun j ↦ k.castSucc < j → tail k.castSucc < tail j) ?_ ?_ j hkj
    · intro _
      simpa [tail] using negative k
    · intro l hkl
      simpa [tail] using ordered (show k < l from hkl)
  let anchor := Finset.univ.inf' Finset.univ_nonempty tail
  obtain ⟨l, lt_anchor, at_left⟩ := left_probe degree (Nat.succ_pos d) lead anchor
  let grid : Fin (d+2) → ℝ := Fin.cons l tail
  have grid_ordered : StrictMono grid := Fin.strictMono_cons.mpr
    ⟨fun i ↦ lt_anchor.trans_le (Finset.inf'_le tail (Finset.mem_univ i)), tail_ordered⟩
  have grid_sign (i : Fin (d+2)) : 0 < (-1 : ℝ) ^ (d+1-i.val) * r.eval (grid i) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [grid] using at_left
    · refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · simpa [grid, tail] using at_zero
      · have exponent : d+1-(k.val+1) = d-k.val := by omega
        simpa [grid, tail, exponent] using sign k
  have interval (i : Fin (d+1)) : ∃ x, grid i.castSucc < x ∧ x < grid i.succ ∧ r.eval x = 0 := by
    apply between (grid_ordered Fin.castSucc_lt_succ)
    apply alternate (k := d-i.val) _ _
    · have exponent : d+1-i.val = d-i.val+1 := by omega
      simpa [exponent] using grid_sign i.castSucc
    · have exponent : d+1-(i.val+1) = d-i.val := by omega
      simpa [exponent] using grid_sign i.succ
  choose zs bounds using interval
  refine ⟨zs, ⟨?_, ?_, fun h ↦ at_zero.ne' (by simp [h]), degree, fun i ↦ (bounds i).2.2⟩, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact (bounds i.castSucc).2.1.trans (by simpa only [Fin.castSucc_succ] using (bounds i.succ).1)
  · intro i
    exact (bounds i).2.1.trans_le (by simpa [grid] using tail_nonpos i)
  · intro i
    have left : zs i.castSucc < ys i := by simpa [grid, tail] using (bounds i.castSucc).2.1
    have right : ys i < zs i.succ := by
      simpa [Fin.castSucc_succ, grid, tail] using (bounds i.succ).1
    exact ⟨left, right⟩

private theorem product_gap {d : ℕ} (k : ℕ) (hk : k ≤ d) (f : Fin d → ℝ)
    (positive : ∀ j, j.val < k → 0 < f j) (negative : ∀ j, k ≤ j.val → f j < 0) :
    0 < (-1 : ℝ) ^ (d-k) * ∏ j, f j := by
  induction d generalizing k with
  | zero =>
    have h : k = 0 := by omega
    simp [h]
  | succ d ih =>
    rw [Fin.prod_univ_succ]
    cases k with
    | zero =>
      have tail := ih 0 (Nat.zero_le d) (fun j ↦ f j.succ)
        (fun j h ↦ (Nat.not_lt_zero j.val h).elim) (fun j _ ↦ negative j.succ (Nat.zero_le _))
      have head := negative 0 (Nat.zero_le _)
      rw [Nat.sub_zero, pow_succ]
      simp only [Nat.sub_zero] at tail
      calc
        0 < (-f 0) * ((-1) ^ d * ∏ j : Fin d, f j.succ) := mul_pos (neg_pos.mpr head) tail
        _ = (-1) ^ d * -1 * (f 0 * ∏ j : Fin d, f j.succ) := by ring
    | succ k =>
      have tail := ih k (Nat.le_of_succ_le_succ hk) (fun j ↦ f j.succ)
        (fun j h ↦ positive j.succ (Nat.succ_lt_succ h))
        (fun j h ↦ negative j.succ (Nat.succ_le_succ h))
      have head := positive 0 (Nat.zero_lt_succ k)
      rw [Nat.succ_sub_succ_eq_sub, mul_left_comm]
      exact mul_pos head tail

/-- With positive leading coefficient, the sign at each separator is the sign
of the factors from roots strictly to its right. -/
theorem eval_between_sign {d : ℕ} {p : ℝ[X]} {xs : Fin d → ℝ} {ys : Fin (d+1) → ℝ}
    (hp : RootArray p xs) (ordered : StrictMono ys) (order : Interlaces xs ys)
    (lead : 0 < p.leadingCoeff) (i : Fin (d+1)) :
    0 < (-1 : ℝ) ^ (d-i.val) * p.eval (ys i) := by
  have factors := product_gap i.val (Nat.le_of_lt_succ i.isLt) (fun j ↦ ys i-xs j)
    (fun j h ↦ sub_pos.mpr ((order j).2.trans_le (ordered.monotone (show j.succ ≤ i by
      rw [Fin.le_def, Fin.val_succ]
      omega))))
    (fun j h ↦ sub_neg.mpr ((ordered.monotone (show i ≤ j.castSucc from h)).trans_lt (order j).1))
  rw [hp.eval_prod, mul_left_comm]
  exact mul_pos lead factors

/-- The signs of the adjacent rows at the middle roots determine the next
degree-increasing step. The conclusion supplies all new roots and their order. -/
theorem rise_of_opposite {d : ℕ} {p q r : ℝ[X]} {xs : Fin d → ℝ} {ys : Fin (d+1) → ℝ}
    (hp : RootArray p xs) (hq : RootArray q ys) (order : Interlaces xs ys)
    (plead : 0 < p.leadingCoeff) (rlead : 0 < r.leadingCoeff) (rzero : 0 < r.eval 0)
    (rdegree : r.natDegree = d+2) (sign : ∀ i, p.eval (ys i) * r.eval (ys i) < 0) :
    ∃ zs : Fin (d+2) → ℝ, RootArray r zs ∧ Interlaces ys zs := by
  apply rise_of_alternating_sign hq.ordered hq.negative rlead rzero rdegree
  intro i
  have previous := eval_between_sign hp hq.ordered order plead i
  have exponent : d+1-i.val = (d-i.val)+1 := by omega
  rw [exponent, pow_succ]
  rcases neg_one_pow_eq_or ℝ (d-i.val) with parity | parity
  · have pos : 0 < p.eval (ys i) := by simpa [parity] using previous
    have neg := ((mul_neg_iff.mp (sign i)).resolve_right fun h ↦ (not_lt_of_ge pos.le) h.1).2
    simpa [parity] using neg
  · have neg : p.eval (ys i) < 0 := by simpa [parity] using previous
    have pos := ((mul_neg_iff.mp (sign i)).resolve_left fun h ↦ (not_lt_of_ge neg.le) h.1).2
    simpa [parity] using pos

#print axioms RootArray.exact
#print axioms RootArray.eval_prod
#print axioms RootArray.roots_nodup
#print axioms rise_of_alternating_sign
#print axioms eval_between_sign
#print axioms rise_of_opposite

end OrderedPartitions.InterlacingStep
