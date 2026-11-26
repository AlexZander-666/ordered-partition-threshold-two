import OrderedPartitions.TwoPoleAngles

noncomputable section
namespace OrderedPartitions.TwoPole
open Real Set Filter
open scoped Topology

private theorem lift_complex {α : Type*} {l : Filter α} {Z : α→ℂ} {u v : ℝ}
    (re : Tendsto (fun i ↦ (Z i).re) l (𝓝 u)) (im : Tendsto (fun i ↦ (Z i).im) l (𝓝 v)) :
    Tendsto Z l (𝓝 ((u:ℂ)+(v:ℂ)*Complex.I)) := by
  have t := (tendsto_ofReal_iff.mpr re).add ((tendsto_ofReal_iff.mpr im).mul_const Complex.I)
  simpa only [Complex.re_add_im] using t

theorem pole_continuousOn {c : ℝ} (cp : 0<c) (osc : ∀ q∈Ioo c 1,-1<level q) :
    ContinuousOn upperPole (Ioo c 1) := by
  intro q hq
  have domain : ∀ᶠ t in 𝓝[Ioo c 1] q,t∈Ioo c 1 := eventually_mem_nhdsWithin
  have h := pole_height_continuous cp osc q hq
  have v := (upperPole_spec (cp.trans hq.1) (osc q hq)).2
  have sv : sinc (upperPole q).im ≠ 0 := by
    rw [sinc_of_ne_zero v.1.ne']
    exact div_ne_zero (sin_pos_of_pos_of_lt_pi v.1 (by linarith [v.2,pi_pos])).ne' v.1.ne'
  have re : Tendsto (fun u ↦ (upperPole u).re) (𝓝[Ioo c 1] q) (𝓝 (upperPole q).re) := by
    rw [pole_real (cp.trans hq.1) (osc q hq)]
    have idlim : Tendsto (fun u : ℝ ↦ u) (𝓝[Ioo c 1] q) (𝓝 q) := nhdsWithin_le_nhds
    have z := ((tendsto_const_nhds (x:=(1:ℝ))).sub (idlim.const_mul 2)).add
      ((continuous_cos.continuousAt.tendsto.comp h).div (continuous_sinc.continuousAt.tendsto.comp h) sv)
    exact z.congr' (domain.mono (fun t ht ↦ (pole_real (cp.trans ht.1) (osc t ht)).symm))
  change Tendsto upperPole (𝓝[Ioo c 1] q) (𝓝 (upperPole q))
  simpa only [Complex.re_add_im] using lift_complex re h

theorem phase_continuous {c : ℝ} (cp : 0<c) (osc : ∀ q∈Ioo c 1,-1<level q) (n : ℕ) :
    ContinuousOn (phase n) (Ioo c 1) := by
  have poles := pole_continuousOn cp osc
  intro q hq
  have hp := (upperPole_spec (cp.trans hq.1) (osc q hq)).2.1
  have thet := (Complex.continuousAt_arg (Or.inr hp.ne')).comp_continuousWithinAt (poles q hq)
  have sl : (upperPole q+2*(q:ℂ)-2).im≠0 := by simpa using hp.ne'
  have zc : ContinuousWithinAt (fun u ↦ upperPole u+2*(u:ℂ)-2) (Ioo c 1) q := by
    exact ((poles q hq).add (continuousWithinAt_const.mul Complex.continuous_ofReal.continuousWithinAt)).sub continuousWithinAt_const
  have bet : ContinuousWithinAt beta (Ioo c 1) q :=
    (Complex.continuousAt_arg (Or.inr sl)).comp_continuousWithinAt (f:=fun u ↦ upperPole u+2*(u:ℂ)-2) zc
  change ContinuousWithinAt (fun u ↦ ((n:ℝ)+1)*(upperPole u).arg+beta u) (Ioo c 1) q
  exact (continuousWithinAt_const.mul thet).add bet

theorem phase_endpoints {c : ℝ} (cl : 1/6<c) (ch : c<1/2) (crit : level c = -1)
    (osc : ∀ q∈Ioo c 1,-1<level q) (n : ℕ) :
    Tendsto (phase n) (𝓝[>] c) (𝓝 (π/2)) ∧
    Tendsto (phase n) (𝓝[<] 1) (𝓝 (((n:ℝ)+2)*(π/2))) := by
  have cp : 0<c := by linarith
  have c1 : c<1 := by linarith
  have lc : ∀ᶠ q in 𝓝[>] c,q∈Ioo c 1 :=
    (eventually_mem_nhdsWithin : ∀ᶠ q in 𝓝[>] c,c<q).and (nhdsWithin_le_nhds (gt_mem_nhds c1))
  have rc : ∀ᶠ q in 𝓝[<] (1:ℝ),q∈Ioo c 1 :=
    (show ∀ᶠ q in 𝓝[<] (1:ℝ), c<q from nhdsWithin_le_nhds (lt_mem_nhds c1)).and eventually_mem_nhdsWithin
  have dom (q) (h : q∈Ioo c 1) := And.intro (cp.trans h.1) (osc q h)
  have lv := pole_height_vanish (lc.mono dom)
    (show Tendsto level (𝓝[>] c) (𝓝 (-1)) by rw [← crit];exact (level_cont cp.ne').continuousWithinAt)
  have rv := pole_height_vanish (rc.mono dom)
    (show Tendsto level (𝓝[<] (1:ℝ)) (𝓝 (-1)) by
      have at_one : level 1 = -1 := by norm_num [level]
      rw [← at_one];exact (level_cont (by norm_num : (1:ℝ)≠0)).continuousWithinAt)
  constructor
  · have idlim : Tendsto (fun q : ℝ ↦ q) (𝓝[>] c) (𝓝 c) := nhdsWithin_le_nhds
    have xr : Tendsto (fun q ↦ (upperPole q).re) (𝓝[>] c) (𝓝 (1-2*c+1)) := by
      have v0 := ((tendsto_const_nhds (x:=(1:ℝ))).sub (idlim.const_mul 2)).add
        ((continuous_cos.continuousAt.tendsto.comp lv).div (continuous_sinc.continuousAt.tendsto.comp lv)
          (by simp : sinc 0≠0))
      simp only [cos_zero,sinc_zero,div_one] at v0
      exact v0.congr' (lc.mono (fun q h ↦ (pole_real (cp.trans h.1) (osc q h)).symm))
    have x0 : 0<1-2*c+1 := by linarith
    have zz : Tendsto upperPole (𝓝[>] c) (𝓝 ((1-2*c+1:ℝ):ℂ)) := by simpa using lift_complex xr lv
    have arg := (Complex.continuousAt_arg (show ((1-2*c+1:ℝ):ℂ)∈Complex.slitPlane from Or.inl x0)).tendsto.comp zz
    have a0 : (((1-2*c+1:ℝ):ℂ)).arg=0 := Complex.arg_eq_zero_iff.mpr ⟨x0.le,rfl⟩
    rw [a0] at arg
    unfold phase theta
    simpa [Function.comp_def] using (arg.const_mul ((n:ℝ)+1)).add (beta_limit (lc.mono dom) lv)
  · have near : ∀ᶠ q in 𝓝[<] (1:ℝ),3/4 ≤ q := nhdsWithin_le_nhds (le_mem_nhds (by norm_num))
    have small := rv.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
    have lim := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun q ↦ 4*(upperPole q).im) (𝓝[<] (1:ℝ)) (𝓝 0) by simpa using rv.const_mul 4)
      ((rc.and (near.and small)).mono (fun q h ↦ (pole_right_ratio_bound h.2.1 h.1.2 (osc q h.1) h.2.2.le).1))
      ((rc.and (near.and small)).mono (fun q h ↦ (pole_right_ratio_bound h.2.1 h.1.2 (osc q h.1) h.2.2.le).2))
    have thet := arg_vertical_limit (Z:=upperPole) (rc.mono (fun q h ↦ (upperPole_spec (cp.trans h.1) (osc q h)).2.1)) lim
    unfold phase theta
    have value : ((n:ℝ)+2)*(π/2) = ((n:ℝ)+1)*(π/2)+(π/2) := by ring
    rw [value]
    exact (thet.const_mul ((n:ℝ)+1)).add (beta_limit (rc.mono dom) rv)

#print axioms phase_continuous
#print axioms phase_endpoints
end OrderedPartitions.TwoPole
