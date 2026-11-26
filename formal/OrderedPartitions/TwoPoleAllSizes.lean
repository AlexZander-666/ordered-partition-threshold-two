import OrderedPartitions.TwoPoleResidues
import OrderedPartitions.TwoPoleCosineModel
import OrderedPartitions.TwoPoleModelReadout
import OrderedPartitions.TwoPoleFirstRows

noncomputable section
namespace OrderedPartitions
open RootTracking TwoPole Real

private theorem threshold_two_estimate {n g : ℕ} (size : (g=1 ∧ 20≤n) ∨ (g=2 ∧ 25≤n))
    {q : ℝ} (lo : 1/6<q) (hi : q<1) (osc : -1<level q) : PhaseEstimate n g q := by
  have hp : 0<q := by linarith
  have z := upperPole_spec hp osc
  have exactModel := cosine_model_of_residues lo hi osc n (taylor_residues hp hi osc z.1 z.2 n)
  refine ⟨rowScale n q,realError n q,rowScale_pos lo hi osc n,?_,exactModel⟩
  rcases size with ⟨rfl,hn⟩|⟨rfl,hn⟩
  · simpa using realError_one lo hi osc hn
  · have err := realError_two lo hi osc hn
    have positive := shift_pos lo hi osc (g:=2) (Or.inr rfl)
    norm_num only [Nat.cast_ofNat] at positive ⊢
    linarith

/-- Original ordered set partitions counted by nonsingleton blocks.
Every adjacent pair and every pair two ranks apart has complete and strictly
interlacing root arrays at every lower rank n ≥ 2. -/
theorem original_threshold_two_three_rows {n g : ℕ} (hn : 2≤n) (gap : g=1 ∨ g=2) :
    OrderedPair (n/2) (row n 2) (row (n+g) 2) := by
  apply original_all_of_estimates _ hn gap
  intro m k h q lo hi osc
  exact ⟨threshold_two_estimate h lo hi osc,threshold_two_estimate (by omega) lo hi osc⟩

theorem original_threshold_two_consecutive {n : ℕ} (hn : 2≤n) :
    OrderedPair (n/2) (row n 2) (row (n+1) 2) :=
  original_threshold_two_three_rows hn (Or.inl rfl)

/-- Empty root lists at ranks zero and one are covered as well. -/
theorem original_threshold_two_window (n : ℕ) {g : ℕ} (gap : g=1 ∨ g=2) :
    OrderedPair (n/2) (row n 2) (row (n+g) 2) := by
  by_cases start : 2≤n
  · exact original_threshold_two_three_rows start gap
  · rcases gap with rfl|rfl
    · exact TwoPoleFinite.first_gap_one (by omega)
    · exact TwoPoleFinite.first_gap_two (by omega)

/-- Four consecutive rows need not be pairwise interlacing. Ranks three
and six already have degrees one and three. -/
theorem threshold_two_window_sharp : ¬ OrderedPair (3/2) (row 3 2) (row 6 2) := by
  rintro ⟨xs,_,⟨ys,hy,_⟩|⟨ys,hy,_⟩⟩ <;> have h := hy.degree <;> rw [(original_shape 6).1] at h <;> omega

#print axioms original_threshold_two_window
#print axioms threshold_two_window_sharp
#print axioms original_threshold_two_three_rows
#print axioms original_threshold_two_consecutive
end OrderedPartitions
