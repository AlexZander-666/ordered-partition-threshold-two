import OrderedPartitions.HardRodDegree

noncomputable section
namespace OrderedPartitions.HardRod
open Set Polynomial

/-- At any real negative activity, the sign just after a time zero persists
up to and including one whole unit later. -/
theorem phi_window_sign {N : ℕ} {s y h : ℝ} (hy : y<0) (pos : 0<h) (win : h≤1)
    (bound : s+h≤(N:ℝ)+1) (zero : (phi N s).eval y=0) :
    (phi N (s-1)).eval y * (phi N (s+h)).eval y<0 := by
  let F : ℝ → ℝ := fun t ↦ (phi N t).eval y
  have cF : Continuous F := cont_eval N y
  have hist (z : ℝ) (hz : z≤1) : F z≠0 := by simp [F,history_eval hz]
  have de (z : ℝ) (hz : 1<z) (zN : z≤(N:ℝ)+1) : HasDerivAt F (y*F (z-1)) z :=
    phi_delay N hz zN y
  have zs : F s=0 := zero
  have s1 : 1<s := lt_of_not_ge fun le ↦ hist s le zs
  obtain ⟨t,ht,der⟩ := exists_hasDerivAt_eq_slope F (fun z ↦ y*F (z-1))
    (show s<s+h by linarith) cF.continuousOn (fun z hz ↦ de z (s1.trans hz.1) (hz.2.le.trans bound))
  have nz (z : ℝ) (hz : z∈Icc (s-1) (t-1)) : F z≠0 := by
    intro z0
    have gap := delay_zero_spacing hy.ne cF hist de (s:=z) (t:=s)
      (by linarith [hz.2,ht.2]) (by linarith) z0 zs
    linarith [hz.1]
  have sign : 0<F (s-1)*F (t-1) := by
    have st : s-1≤t-1 := by linarith [ht.1]
    have a := nz (s-1) ⟨le_rfl,st⟩
    have b := nz (t-1) ⟨st,le_rfl⟩
    rcases lt_or_gt_of_ne a with a|a <;> rcases lt_or_gt_of_ne b with b|b
    · exact mul_pos_of_neg_of_neg a b
    · obtain ⟨z,hz,zz⟩ := intermediate_value_Icc st cF.continuousOn ⟨a.le,b.le⟩
      exact (nz z hz zz).elim
    · obtain ⟨z,hz,zz⟩ := intermediate_value_Icc' st cF.continuousOn ⟨b.le,a.le⟩
      exact (nz z hz zz).elim
    · exact mul_pos a b
  have val : F (s+h) = (y * F (t-1))*h := by
    apply (div_eq_iff pos.ne').mp
    simpa [zs] using der.symm
  change F (s-1)*F (s+h)<0
  rw [val]
  calc F (s-1)*(y*F (t-1)*h) = (y*h)*(F (s-1)*F (t-1)) := by ring
       _ < 0 := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hy pos) sign

#print axioms phi_window_sign
end OrderedPartitions.HardRod
