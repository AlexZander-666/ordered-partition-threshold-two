import OrderedPartitions.LastBlock

noncomputable section
open Finset Polynomial
namespace OrderedPartitions

private def degreeFiberEquiv (n b j d : ℕ) :
    {f : Onto n b // d = (large f.val j).card} ≃ Layer n b j d where
  toFun f := ⟨f.val.val, f.val.property, f.property.symm⟩
  invFun f := ⟨⟨f.val,f.property.1⟩, f.property.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coeff_blockRow (n b j d : ℕ) :
    (blockRow n b j).coeff d = (Fintype.card (Layer n b j d) : ℝ) := by
  classical
  rw [← Fintype.card_congr (degreeFiberEquiv n b j d), Fintype.card_subtype]
  simp [blockRow, finsetSum_coeff, coeff_X_pow, sum_boole]

theorem row_eq_sum {n j : ℕ} (hj : 1 ≤ j) : row n j = ∑ b ∈ range (n+1), blockRow n b j := by
  ext d
  simp [coeff_row hj, finsetSum_coeff, coeff_blockRow, count]

private theorem blockRow_too_many {n b : ℕ} (hb : n < b) (j : ℕ) : blockRow n b j = 0 := by
  have : IsEmpty (Onto n b) := ⟨fun f ↦ by
    have := Fintype.card_le_of_surjective _ f.property
    simp only [Fintype.card_fin] at this
    omega⟩
  simp [blockRow]

private theorem blockRow_no_blocks (n j : ℕ) : blockRow (n+1) 0 j = 0 := by
  have : IsEmpty (Onto (n+1) 0) := ⟨fun f ↦ Fin.elim0 (f.val 0)⟩
  simp [blockRow]

theorem row_last_subset (n : ℕ) {j : ℕ} (hj : 1 ≤ j) : row (n+1) j =
    ∑ s : {s : Finset (Fin (n+1)) // s.Nonempty},
      row (n+1-s.val.card) j * X^(if j ≤ s.val.card then 1 else 0) := by
  classical
  rw [row_eq_sum hj, sum_range_succ', blockRow_no_blocks, add_zero]
  simp_rw [blockRow_last]
  rw [sum_comm]
  apply Fintype.sum_congr
  intro s
  rw [← sum_mul, row_eq_sum hj]
  congr 1
  apply Eq.symm
  apply sum_subset
  · apply range_mono
    have := card_pos.mpr s.property
    omega
  · intro b _ hb
    apply blockRow_too_many
    simpa [not_lt] using hb

private def sizeFiberEquiv {N r : ℕ} (hr : 0 < r) :
    {s : {s : Finset (Fin N) // s.Nonempty} // s.val.card = r} ≃
      ↥((univ : Finset (Fin N)).powersetCard r) where
  toFun s := ⟨s.val.val, mem_powersetCard.mpr ⟨subset_univ _,s.property⟩⟩
  invFun s := ⟨⟨s.val, card_pos.mp (by simpa only [(mem_powersetCard.mp s.property).2] using hr)⟩,
    (mem_powersetCard.mp s.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_nonempty_sizes {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∑ s : {s : Finset (Fin N) // s.Nonempty}, f s.val.card) =
    ∑ r ∈ Icc 1 N, N.choose r • f r := by
  classical
  let U := {s : Finset (Fin N) // s.Nonempty}
  have maps (s : U) (_ : s ∈ univ) : s.val.card ∈ Icc 1 N :=
    mem_Icc.mpr ⟨card_pos.mpr s.property, by simpa using card_le_univ s.val⟩
  rw [← sum_fiberwise_of_maps_to maps]
  apply sum_congr rfl
  intro r hr
  let fiber := (univ : Finset U).filter fun s ↦ s.val.card = r
  have hcard : fiber.card = N.choose r := by
    rw [show fiber.card = Fintype.card {s : U // s.val.card = r} from
      (Fintype.card_subtype _).symm, Fintype.card_congr (sizeFiberEquiv (mem_Icc.mp hr).1)]
    simp
  calc
    _ = ∑ _s ∈ fiber, f r := sum_congr rfl (fun _ h ↦ congrArg f (mem_filter.mp h).2)
    _ = _ := by rw [sum_const, hcard]

/-- Last-block recurrence for the original unnormalized labeled ordered-partition row. -/
theorem row_recurrence (n : ℕ) {j : ℕ} (hj : 1 ≤ j) : row (n+1) j =
    ∑ r ∈ Icc 1 (n+1), (n+1).choose r •
      (row (n+1-r) j * X^(if j ≤ r then 1 else 0)) := by
  rw [row_last_subset n hj]
  exact sum_nonempty_sizes (M := ℝ[X]) (n+1) (fun r ↦ row (n+1-r) j * X^(if j ≤ r then 1 else 0))

/-- Integer recurrence, with no spurious degree-zero contribution from a large last block. -/
theorem count_recurrence (n : ℕ) {j : ℕ} (hj : 1 ≤ j) (d : ℕ) :
    count (n+1) j d = ∑ r ∈ Icc 1 (n+1), (n+1).choose r *
      (if j ≤ r then (if d=0 then 0 else count (n+1-r) j (d-1)) else count (n+1-r) j d) := by
  have rowCoeff := congrArg (fun p : ℝ[X] ↦ p.coeff d) (row_recurrence n hj)
  simp only [coeff_row hj, finsetSum_coeff, nsmul_eq_mul, coeff_natCast_mul] at rowCoeff
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_sum]
  refine rowCoeff.trans (sum_congr rfl (fun r _ ↦ ?_))
  rw [Nat.cast_mul]
  by_cases h : j ≤ r
  · cases d <;> simp [h, coeff_row hj]
  · simp [h, coeff_row hj]

#print axioms count_recurrence
#print axioms coeff_blockRow
#print axioms row_eq_sum
#print axioms row_recurrence

end OrderedPartitions
