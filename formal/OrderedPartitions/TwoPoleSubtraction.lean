import OrderedPartitions.TwoPoleTaylor

/-! Removal of two specified simple poles on an open strip, with both residues computed from derivatives. -/
namespace OrderedPartitions.TwoPole
open Complex Set Filter
open scoped Topology ComplexConjugate
noncomputable section

private theorem slope_mul (f : ℂ → ℂ) (a z : ℂ) : (z-a)*dslope f a z = f z-f a :=
  sub_smul_dslope f a z

/-- Linear interpolation extracts both residues while keeping the remaining function holomorphic. -/
theorem remove_two {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Strip) {a b : ℂ}
    (ha : a ∈ Strip) (hb : b ∈ Strip) (ab : a≠b) (ga : g a=0) (gb : g b=0)
    (da : deriv g a≠0) (db : deriv g b≠0) (onlyZeros : ∀ z∈Strip, g z=0 → z=a ∨ z=b) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Strip ∧
      ∀ z∈Strip, z≠a → z≠b → (g z)⁻¹ =
        H z + (deriv g a)⁻¹*(z-a)⁻¹ + (deriv g b)⁻¹*(z-b)⁻¹ := by
  let D := dslope (dslope g a) b
  have HD : DifferentiableOn ℂ D Strip := (Complex.differentiableOn_dslope
    (strip_open.mem_nhds hb)).2 ((Complex.differentiableOn_dslope (strip_open.mem_nhds ha)).2 hg)
  have ab' : b-a≠0 := sub_ne_zero.mpr ab.symm
  have ba' : a-b≠0 := sub_ne_zero.mpr ab
  have bg : dslope g a b = 0 := by
    rw [dslope_of_ne _ ab.symm, slope_def_field, ga, gb, sub_self, zero_div]
  have factor (z : ℂ) : g z = (z-a)*(z-b)*D z := by
    have e := slope_mul (dslope g a) b z
    rw [bg,sub_zero] at e
    have d := slope_mul g a z
    rw [ga,sub_zero] at d
    change _ = _*dslope (dslope g a) b z
    rw [mul_assoc,e,d]
  have derivative (w : ℂ) (hw : w ∈ Strip) :
      deriv g w = ((w-a)+(w-b))*D w+(w-a)*(w-b)*deriv D w := by
    have g' := ((((hasDerivAt_id w).sub_const a).mul ((hasDerivAt_id w).sub_const b)).mul
      (HD.differentiableAt (strip_open.mem_nhds hw)).hasDerivAt).deriv
    rw [funext factor]
    convert! g' using 1
    simp only [id_eq, one_mul, mul_one, Pi.mul_apply]
    ring
  have RA : deriv g a = (a-b)*D a := by simpa using derivative a ha
  have RB : deriv g b = (b-a)*D b := by simpa using derivative b hb
  have nd z (hz : z∈Strip) : D z≠0 := by
    intro ez
    have gz : g z=0 := by rw [factor, ez, mul_zero]
    rcases onlyZeros z hz gz with rfl|rfl
    · simp [ez] at RA; contradiction
    · simp [ez] at RB; contradiction
  let N (z : ℂ) := (D z)⁻¹
  have HN : DifferentiableOn ℂ N Strip := HD.inv nd
  let H := dslope (dslope N a) b
  have HH : DifferentiableOn ℂ H Strip := (Complex.differentiableOn_dslope
    (strip_open.mem_nhds hb)).2 ((Complex.differentiableOn_dslope (strip_open.mem_nhds ha)).2 HN)
  refine ⟨H,HH,fun z hz za zb ↦ ?_⟩
  have e := slope_mul (dslope N a) b z
  have d := slope_mul N a z
  change (z-b)*H z=_ at e
  have NA : N a = (a-b)/deriv g a := by
    rw [RA]; dsimp [N]; field_simp [ba',nd a ha]
  have NB : N b = (b-a)/deriv g b := by
    rw [RB]; dsimp [N]; field_simp [ab',nd b hb]
  have sb : dslope N a b = (deriv g a)⁻¹+(deriv g b)⁻¹ := by
    rw [dslope_of_ne _ ab.symm, slope_def_field, NA, NB]
    field_simp
    ring
  rw [sb] at e
  rw [NA] at d
  have nm : N z = (z-a)*(z-b)*H z + (z-b)/deriv g a + (z-a)/deriv g b := by
    simp only [div_eq_mul_inv] at d ⊢
    linear_combination -d - (z-a)*e
  have za' := sub_ne_zero.mpr za
  have zb' := sub_ne_zero.mpr zb
  calc
    _ = N z / ((z-a)*(z-b)) := by
      dsimp [N]; rw [factor]; field_simp [nd z hz]
    _ = _ := by rw [nm]; field_simp

theorem zeros_in_strip {q : ℝ} (hq : 0<q) (crit : -1<Real.log q+(1-2*q))
    {z : ℂ} (gz : G q z=0) (iz : z.im∈Ioo 0 (Real.pi/2)) {w : ℂ}
    (hw : w∈Strip) (gw : G q w=0) : w=z ∨ w=conj z := by
  have zu : z.im∈Ioo 0 Real.pi := ⟨iz.1, by linarith [iz.2,Real.pi_pos]⟩
  have up (v : ℂ) (hv : v∈Strip) (vp : 0<v.im) (gv : G q v=0) : v=z := by
    have pos : 0<Real.sin v.im := by
      have eq := congrArg Complex.im gv
      rw [im_G,Complex.zero_im] at eq
      by_contra! n
      have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hq.le (Real.exp_pos v.re).le) n
      linarith
    apply upper_unique hq gv gz ⟨vp,?_⟩ zu
    by_contra! ge
    change |v.im|<2*Real.pi at hv
    have si := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ge)
      (show v.im-Real.pi ≤ Real.pi by linarith [le_abs_self v.im])
    rw [Real.sin_sub_pi] at si
    linarith
  rcases lt_trichotomy 0 w.im with h|h|h
  · exact Or.inl (up w hw h gw)
  · have we : w=(w.re:ℂ) := Complex.ext rfl h.symm
    have pos := real_axis hq crit w.re
    rw [←we,gw,Complex.zero_re] at pos
    exact False.elim (lt_irrefl _ pos)
  · have c := up (conj w) (by simpa [Strip] using hw) (by simpa using h)
      (by simp [G_conj,gw])
    exact Or.inr (by simpa using congrArg (fun t : ℂ ↦ conj t) c)

end
end OrderedPartitions.TwoPole
