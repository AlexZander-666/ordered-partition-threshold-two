import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! A zero-spacing and two-sided Sturm sign theorem for a unit-delay equation.
Only the initial history and the portion of the solution up to the stated horizon are used. -/
namespace OrderedPartitions.HardRod
open Set

private theorem pull_back {F : ℝ→ℝ} {a bound : ℝ} (ha : a≠0) (cont : Continuous F)
    (history : ∀s, s≤1 → F s≠0)
    (delay : ∀s,1<s → s≤bound → HasDerivAt F (a*F (s-1)) s)
    {s t : ℝ} (lt : s<t) (tb : t≤bound) (zs : F s=0) (zt : F t=0) :
    ∃z, s-1<z ∧ z<t-1 ∧ F z=0 := by
  have s1 : 1<s := lt_of_not_ge fun h ↦ (history s h) zs
  obtain ⟨p,hp,zero⟩ := exists_hasDerivAt_eq_zero (f':=fun p ↦ a*F (p-1))
    lt cont.continuousOn (zs.trans zt.symm) (fun z hz ↦ delay z (s1.trans hz.1) (hz.2.le.trans tb))
  exact ⟨p-1,by linarith [hp.1],by linarith [hp.2],(mul_eq_zero.mp zero).resolve_left ha⟩

/-- Two applications of Rolle lower the larger of two hypothetical close zeros
by more than one time unit. This proves the strict separation without any
assumption that zeros are finite or pre-isolated. -/
theorem delay_zero_spacing {F : ℝ→ℝ} {a bound : ℝ} (ha : a≠0) (cont : Continuous F)
    (history : ∀s, s≤1 → F s≠0)
    (delay : ∀s,1<s → s≤bound → HasDerivAt F (a*F (s-1)) s)
    {s t : ℝ} (lt : s<t) (tb : t≤bound) (zs : F s=0) (zt : F t=0) : s+1<t := by
  have aux (N : ℕ) : ∀ {u v : ℝ}, v≤(N:ℝ) → u<v → v≤bound → F u=0 → F v=0 → u+1<v := by
    induction N with
    | zero =>
      intro u v lim _ _ _ zv
      exact ((history v (by push_cast at lim;linarith)) zv).elim
    | succ N ih =>
      intro u v lim uv vb zu zv
      by_contra! near
      obtain ⟨z,zlo,zhi,zz⟩ := pull_back ha cont history delay uv vb zu zv
      have zu' : z<u := by linarith
      obtain ⟨w,_,whi,zw⟩ := pull_back ha cont history delay zu' (uv.le.trans vb) zz zu
      have wz : w<z := by linarith
      have step := ih (u:=w) (v:=z) (by push_cast at lim;linarith) wz
        (by linarith) zw zz
      linarith
  obtain ⟨N,hN⟩ := exists_nat_ge t
  exact aux N hN lt tb zs zt

private theorem same_sign {F : ℝ→ℝ} (cont : Continuous F) {a b : ℝ}
    (h : a≤b) (non : ∀t ∈ Icc a b, F t≠0) : 0<F a*F b := by
  have na := non a ⟨le_rfl,h⟩
  have nb := non b ⟨h,le_rfl⟩
  rcases lt_or_gt_of_ne na with an|ap <;> rcases lt_or_gt_of_ne nb with bn|bp
  · exact mul_pos_of_neg_of_neg an bn
  · obtain ⟨t,mem,zero⟩ := intermediate_value_Icc h cont.continuousOn ⟨an.le,bp.le⟩
    exact (non t mem zero).elim
  · obtain ⟨t,mem,zero⟩ := intermediate_value_Icc' h cont.continuousOn ⟨bn.le,ap.le⟩
    exact (non t mem zero).elim
  · exact mul_pos ap bp

/-- At a zero of the middle time slice the two neighboring time slices have
opposite strict signs. This is the Sturm evaluation on the activity axis. -/
theorem delay_sturm_sign {F : ℝ→ℝ} {a bound : ℝ} (ha : a<0) (cont : Continuous F)
    (history : ∀s, s≤1 → F s≠0)
    (delay : ∀s,1<s → s≤bound → HasDerivAt F (a*F (s-1)) s)
    {s : ℝ} (sb : s+1≤bound) (zs : F s=0) : F (s-1)*F (s+1)<0 := by
  have s1 : 1<s := lt_of_not_ge fun h ↦ (history s h) zs
  obtain ⟨t,ht,der⟩ := exists_hasDerivAt_eq_slope F (fun p ↦ a*F (p-1))
    (show s<s+1 by linarith) cont.continuousOn (fun p hp ↦ delay p (s1.trans hp.1) (hp.2.le.trans sb))
  have sig := same_sign cont (a:=s-1) (b:=t-1) (by linarith [ht.1]) (by
    intro u hu zu
    have h := delay_zero_spacing ha.ne cont history delay (s:=u) (t:=s)
      (by linarith [hu.2,ht.2]) (by linarith) zu zs
    linarith [hu.1])
  have val : F (s+1)=a*F (t-1) := by simpa [zs] using der.symm
  rw [val,← mul_left_comm]
  exact mul_neg_of_neg_of_pos ha sig

#print axioms delay_zero_spacing
#print axioms delay_sturm_sign
end OrderedPartitions.HardRod
