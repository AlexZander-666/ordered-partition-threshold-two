import OrderedPartitions.TwoPoleHeightLimit
import OrderedPartitions.TwoPoleRightBounds

noncomputable section
namespace OrderedPartitions.TwoPole
open Real Set Filter
open scoped Topology

def theta (q : ℝ) := (upperPole q).arg
def beta (q : ℝ) := (upperPole q+2*(q:ℂ)-2).arg
def phase (n : ℕ) (q : ℝ) := ((n:ℝ)+1)*theta q+beta q

theorem arg_vertical_limit {α : Type*} {l : Filter α} {Z : α→ℂ}
    (pos : ∀ᶠ i in l,0<(Z i).im)
    (lim : Tendsto (fun i ↦ (Z i).re/(Z i).im) l (𝓝 0)) :
    Tendsto (fun i ↦ (Z i).arg) l (𝓝 (π/2)) := by
  have normalized : Tendsto (fun i ↦ (((Z i).re/(Z i).im:ℝ):ℂ)+Complex.I) l (𝓝 Complex.I) := by
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp lim).add_const Complex.I
  have arg := (Complex.continuousAt_arg (show Complex.I∈Complex.slitPlane from Or.inr (by simp))).tendsto.comp normalized
  rw [Complex.arg_I] at arg
  apply arg.congr'
  filter_upwards [pos] with i pi
  change (↑((Z i).re/(Z i).im)+Complex.I).arg = (Z i).arg
  rw [← Complex.arg_real_mul _ pi]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  field_simp

theorem pole_real {q : ℝ} (hq : 0<q) (crit : -1<level q) :
    (upperPole q).re = 1-2*q+cos (upperPole q).im / sinc (upperPole q).im := by
  obtain ⟨hz,iv⟩ := upperPole_spec hq crit
  have hv := iv.1
  have hs := sin_pos_of_pos_of_lt_pi hv (by linarith [iv.2,pi_pos])
  rw [((zero_iff hq hv hs).mp hz).1,Real.sinc_of_ne_zero hv.ne']
  field_simp

theorem beta_limit {α : Type*} {l : Filter α} {q : α→ℝ}
    (domain : ∀ᶠ i in l,0<q i ∧ -1<level (q i))
    (lim : Tendsto (fun i ↦ (upperPole (q i)).im) l (𝓝 0)) :
    Tendsto (fun i ↦ beta (q i)) l (𝓝 (π/2)) := by
  let Z := fun i ↦ upperPole (q i)+2*(q i:ℂ)-2
  have im (i) : (Z i).im=(upperPole (q i)).im := by simp [Z]
  apply arg_vertical_limit (Z:=Z) (domain.mono (fun i h ↦ by rw [im];exact (upperPole_spec h.1 h.2).2.1))
  have low : Tendsto (fun i ↦ -(upperPole (q i)).im/2) l (𝓝 0) := by simpa using lim.neg.div_const 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low tendsto_const_nhds
  · filter_upwards [domain] with i h
    have sp := upperPole_spec h.1 h.2
    have v := sp.2.1
    have hs := sin_pos_of_pos_of_lt_pi v (by linarith [sp.2.2,pi_pos])
    have eq := ((zero_iff h.1 v hs).mp sp.1).1
    have bound := (cot_deficit_bound sp.2).2
    rw [im,le_div_iff₀ v]
    simp [Z,Complex.mul_re]; nlinarith
  · filter_upwards [domain] with i h
    have sp := upperPole_spec h.1 h.2
    have v := sp.2.1
    have hs := sin_pos_of_pos_of_lt_pi v (by linarith [sp.2.2,pi_pos])
    have eq := ((zero_iff h.1 v hs).mp sp.1).1
    have bound := (cot_deficit_bound sp.2).1
    rw [im,div_le_iff₀ v]
    simp [Z,Complex.mul_re];linarith

#print axioms beta_limit
end OrderedPartitions.TwoPole
