import OrderedPartitions.QuadraticBracketing
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.ComputeDegree

/-! Strict adjacent root orders with exact real factorizations and multiplicities. -/

open Polynomial

namespace OrderedPartitions.QuadraticOrder

/-- A complete real factorization together with its exact root multiset. -/
structure ExactRoots (p : ℝ[X]) (xs : List ℝ) : Prop where
  roots : p.roots = (xs : Multiset ℝ)
  factor : p = C p.leadingCoeff * (xs.map fun x ↦ X - C x).prod

def TwoToTwo (p q : ℝ[X]) : Prop :=
  ∃ r₁ s₁ r₂ s₂ : ℝ,
    r₁ < s₁ ∧ s₁ < r₂ ∧ r₂ < s₂ ∧ s₂ < 0 ∧ ExactRoots p [r₁, r₂] ∧ ExactRoots q [s₁, s₂]

def TwoToThree (p q : ℝ[X]) : Prop :=
  ∃ s₁ r₁ s₂ r₂ s₃ : ℝ,
    s₁ < r₁ ∧ r₁ < s₂ ∧ s₂ < r₂ ∧ r₂ < s₃ ∧ s₃ < 0 ∧
      ExactRoots p [r₁, r₂] ∧ ExactRoots q [s₁, s₂, s₃]

/-- The jump proposition determines which exact root order holds. -/
def Adjacent (p q : ℝ[X]) (jump : Prop) : Prop :=
  (jump ∧ TwoToThree p q) ∨ (¬jump ∧ TwoToTwo p q)

private theorem exactRoots_of_list {p : ℝ[X]} {xs : List ℝ} (hp : p ≠ 0)
    (hlist : xs.Nodup) (hdegree : p.natDegree ≤ xs.length)
    (hzeros : ∀ x ∈ xs, p.eval x = 0) : ExactRoots p xs := by
  classical
  have hcard : xs.toFinset.card = xs.length := List.toFinset_card_of_nodup hlist
  have hroots := roots_eq_of_natDegree_le_card_of_ne_zero (S := xs.toFinset)
    (fun x hx ↦ hzeros x (List.mem_toFinset.mp hx)) (by rwa [hcard]) hp
  have heq : p.roots = (xs : Multiset ℝ) := by
    rw [hroots, List.toFinset_val, List.dedup_eq_self.mpr hlist]
  have hsplit : p.Splits := splits_iff_card_roots.mpr
    (le_antisymm p.card_roots' (by simpa [heq] using hdegree))
  exact ⟨heq, by simpa [heq] using hsplit.eq_prod_roots⟩

noncomputable def quadratic (a b c : ℝ) : ℝ[X] := C a + C b * X + C c * X^2

noncomputable def cubic (d e f g : ℝ) : ℝ[X] := quadratic d e f + C g * X^3

@[simp] theorem eval_quadratic (a b c x : ℝ) : (quadratic a b c).eval x = a+b*x+c*x^2 := by
  simp [quadratic]

@[simp] theorem eval_cubic (d e f g x : ℝ) : (cubic d e f g).eval x = d+e*x+f*x^2+g*x^3 := by
  simp [cubic]

private theorem quadratic_degree (a b c : ℝ) : (quadratic a b c).natDegree ≤ 2 := by
  unfold quadratic
  compute_degree!

private theorem cubic_degree (d e f g : ℝ) : (cubic d e f g).natDegree ≤ 3 := by
  unfold cubic quadratic
  compute_degree!

private theorem root_between {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) : ∃ x, a < x ∧ x < b ∧ p.eval x = 0 := by
  have h := intermediate_value_Ioo hab.le p.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨ha, hb⟩)
  obtain ⟨x, hx, hz⟩ := h
  exact ⟨x, hx.1, hx.2, hz⟩

private theorem root_between_descending {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : 0 < p.eval a) (hb : p.eval b < 0) : ∃ x, a < x ∧ x < b ∧ p.eval x = 0 := by
  have h := intermediate_value_Ioo' hab.le p.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a) from ⟨hb, ha⟩)
  obtain ⟨x, hx, hz⟩ := h
  exact ⟨x, hx.1, hx.2, hz⟩


/-- A positive cubic coefficient gives a negative value strictly left of any given point. -/
private theorem cubic_left_negative (d e f g l : ℝ) (hg : 0 < g) :
    ∃ x < l, (cubic d e f g).eval x < 0 := by
  let k := |d| + |e| + |f|
  have hk : 0 ≤ k := by dsimp [k]; positivity
  let m := 1 + |l| + k/g
  have hdiv : 0 ≤ k/g := div_nonneg hk hg.le
  have hm : 1 ≤ m := by dsimp [m]; linarith [abs_nonneg l]
  have hm0 : 0 < m := by linarith
  have hm2 : m ≤ m^2 := by nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr hm)]
  have hm21 : 1 ≤ m^2 := hm.trans hm2
  have hgM : k < g*m := by
    have eq : k = g*(k/g) := by field_simp
    calc
      k = g*(k/g) := eq
      _ < g*m := mul_lt_mul_of_pos_left (by dsimp [m]; linarith [abs_nonneg l]) hg
  have hd : d ≤ |d| *m^2 :=
    (le_abs_self d).trans (by simpa using mul_le_mul_of_nonneg_left hm21 (abs_nonneg d))
  have he : (-e)*m ≤ |e| *m^2 :=
    (mul_le_mul_of_nonneg_right (neg_le_abs e) hm0.le).trans
      (mul_le_mul_of_nonneg_left hm2 (abs_nonneg e))
  have hf : f*m^2 ≤ |f| *m^2 := mul_le_mul_of_nonneg_right (le_abs_self f) (sq_nonneg _)
  refine ⟨-m, by dsimp [m]; linarith [neg_abs_le l], ?_⟩
  calc
    (cubic d e f g).eval (-m) = d + (-e)*m + f*m^2 - (g*m)*m^2 := by rw [eval_cubic]; ring
    _ ≤ k*m^2 - (g*m)*m^2 := by dsimp [k]; nlinarith only [hd, he, hf]
    _ < 0 := sub_neg.mpr (mul_lt_mul_of_pos_right hgM (sq_pos_of_pos hm0))

/-- Opposite signs at the two quadratic roots locate all roots of the upper row. -/
theorem adjacent_of_signs {a b c d e f g l r : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hg : 0 ≤ g)
    (hlr : l < r) (hr0 : r < 0)
    (hpl : (quadratic a b c).eval l = 0) (hpr : (quadratic a b c).eval r = 0)
    (hql : 0 < (cubic d e f g).eval l) (hqr : (cubic d e f g).eval r < 0) :
    Adjacent (quadratic a b c) (cubic d e f g) (0 < g) := by
  let p := quadratic a b c
  let q := cubic d e f g
  have hp0 : 0 < p.eval 0 := by simpa [p] using ha
  have hq0 : 0 < q.eval 0 := by simpa [q] using hd
  have hp : p ≠ 0 := fun h ↦ (ne_of_gt hp0) (by simp [h])
  have hq : q ≠ 0 := fun h ↦ (ne_of_gt hq0) (by simp [h])
  have hleft : ExactRoots p [l, r] := by
    apply exactRoots_of_list hp (by simp [ne_of_lt hlr])
      (by simpa [p] using quadratic_degree a b c)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact hpl
    · exact hpr
  obtain ⟨s, hls, hsr, hs⟩ := root_between_descending hlr hql hqr
  obtain ⟨t, hrt, ht0, ht⟩ := root_between hr0 hqr hq0
  have hst := hsr.trans hrt
  by_cases hzero : g = 0
  · right
    refine ⟨by simp [hzero], l, s, r, t, hls, hsr, hrt, ht0, hleft, ?_⟩
    apply exactRoots_of_list hq (by simp [ne_of_lt hst])
      (by simpa [q, cubic, hzero] using quadratic_degree d e f)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact hs
    · exact ht
  · left
    have hpos : 0 < g := lt_of_le_of_ne hg (Ne.symm hzero)
    obtain ⟨x, hxl, hxq⟩ := cubic_left_negative d e f g l hpos
    obtain ⟨z, _, hzl, hz⟩ := root_between hxl hxq hql
    have hzs := hzl.trans hls
    have hzt := hzs.trans hst
    refine ⟨hpos, z, l, s, r, t, hzl, hls, hsr, hrt, ht0, hleft, ?_⟩
    apply exactRoots_of_list hq (by simp [ne_of_lt hzs, ne_of_lt hzt, ne_of_lt hst])
      (by simpa [q] using cubic_degree d e f g)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hz
    · exact hs
    · exact ht


private theorem quadratic_bracket {a b c u v : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hu : 0 < u) (hv : 0 < v) (h : a*v^2-b*u*v+c*u^2 < 0) :
    ∃ l r : ℝ, l < -u/v ∧ -u/v < r ∧ r < 0 ∧
      (quadratic a b c).eval l = 0 ∧ (quadratic a b c).eval r = 0 := by
  obtain ⟨l, r, hl, hr, hr0, factor⟩ := (first_jump_brackets_iff u v a b c hu hv ha hc).mp h
  exact ⟨l, r, hl, hr, hr0, by simpa using factor l, by simpa using factor r⟩

def remainderSlope (a b c e f g : ℝ) : ℝ := c*c*e-c*g*a-(c*f-g*b)*b

def remainderIntercept (a b c d f g : ℝ) : ℝ := c*c*d-(c*f-g*b)*a

private theorem remainder_eval (a b c d e f g x : ℝ) :
    c^2 * (cubic d e f g).eval x =
      (c*g*x+(c*f-g*b)) * (quadratic a b c).eval x +
        remainderSlope a b c e f g*x + remainderIntercept a b c d f g := by
  simp only [eval_cubic, eval_quadratic, remainderSlope, remainderIntercept]
  ring

/-- A signed linear remainder and a negative test value give exact adjacent root orders. -/
theorem adjacent_of_remainder {a b c d e f g : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hg : 0 ≤ g) :
    let u := remainderSlope a b c e f g
    let v := remainderIntercept a b c d f g
    u < 0 → a*u^2-b*u*v+c*v^2 < 0 → Adjacent (quadratic a b c) (cubic d e f g) (0 < g) := by
  intro u v hu htest
  have hv : v < 0 := by
    by_contra! h
    have hprod := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hb.le hu.le) h
    have ha' := mul_nonneg ha.le (sq_nonneg u)
    have hc' := mul_nonneg hc.le (sq_nonneg v)
    linarith
  have hdet : a*(-u)^2-b*(-v)*(-u)+c*(-v)^2 < 0 := by
    convert htest using 1
    ring
  obtain ⟨l, r, hl, hr, hr0, hpl, hpr⟩ :=
    quadratic_bracket ha hc (neg_pos.mpr hv) (neg_pos.mpr hu) hdet
  have hlineL : 0 < u*l+v := by
    have h := (lt_div_iff₀ (neg_pos.mpr hu)).mp hl
    nlinarith only [h]
  have hlineR : u*r+v < 0 := by
    have h := (div_lt_iff₀ (neg_pos.mpr hu)).mp hr
    nlinarith only [h]
  have hql : 0 < (cubic d e f g).eval l := by
    apply (mul_pos_iff_of_pos_left (sq_pos_of_pos hc)).mp
    rw [remainder_eval, hpl, mul_zero, zero_add]
    exact hlineL
  have hqr : (cubic d e f g).eval r < 0 := by
    have hprod : c^2 * (cubic d e f g).eval r < 0 := by
      rw [remainder_eval, hpr, mul_zero, zero_add]
      exact hlineR
    by_contra! h
    exact (not_lt_of_ge (mul_nonneg (sq_nonneg c) h)) hprod
  exact adjacent_of_signs ha hd hg (hl.trans hr) hr0 hpl hpr hql hqr

/-- The additive criterion for normalized rows gives the same two adjacent root orders. -/
theorem normalized_adjacent {a b δa δb g : ℝ} (hb : 0 < b) (hg : 0 ≤ g) :
    let s := δa-g/b
    let t := δb-g*a/b
    0 < s → 0 < t → t/s+b*s/t < a →
      Adjacent (quadratic 1 a b) (cubic 1 (a+δa) (b+δb) g) (0 < g) := by
  intro s t hs ht hsep
  have hmul := mul_lt_mul_of_pos_right hsep (mul_pos hs ht)
  have heq : (t/s+b*s/t)*(s*t) = t^2+b*s^2 := by field_simp
  rw [heq] at hmul
  have hdet : 1*t^2-a*s*t+b*s^2 < 0 := by nlinarith only [hmul]
  obtain ⟨l, r, hl, hr, hr0, hpl, hpr⟩ :=
    quadratic_bracket zero_lt_one hb hs ht hdet
  have hpos (x : ℝ) :
      (cubic 1 (a+δa) (b+δb) g).eval x =
      (1+(g/b)*x)*(quadratic 1 a b).eval x + x*(s+t*x) := by
    simp only [eval_cubic, eval_quadratic]
    dsimp [s, t]
    field_simp
    ring
  have hsl : s+t*l < 0 := by nlinarith only [(lt_div_iff₀ ht).mp hl]
  have hsr : 0 < s+t*r := by nlinarith only [(div_lt_iff₀ ht).mp hr]
  have hql : 0 < (cubic 1 (a+δa) (b+δb) g).eval l := by
    rw [hpos l, hpl, mul_zero, zero_add]
    exact mul_pos_of_neg_of_neg (hl.trans (hr.trans hr0)) hsl
  have hqr : (cubic 1 (a+δa) (b+δb) g).eval r < 0 := by
    rw [hpos r, hpr, mul_zero, zero_add]
    exact mul_neg_of_neg_of_pos hr0 hsr
  exact adjacent_of_signs zero_lt_one zero_lt_one hg (hl.trans hr) hr0 hpl hpr hql hqr

#print axioms adjacent_of_signs
#print axioms adjacent_of_remainder
#print axioms normalized_adjacent

end OrderedPartitions.QuadraticOrder
