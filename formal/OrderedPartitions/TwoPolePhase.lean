import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The sign transfer for two approximations whose phases differ by a positive sine. -/

namespace OrderedPartitions.TwoPolePhase
open Real

/-- At a root of the first approximation the sine of the old phase determines
the strict sign of the second approximation. -/
theorem next_sign {ψ θ E F : ℝ} (shift : 0 < sin θ) (zero : cos ψ = E)
    (old_error : |E| ≤ sin θ / 4) (new_error : |F| ≤ sin θ / 4) :
    0 < sin ψ * (-cos (ψ+θ)+F) := by
  have small : |cos ψ| ≤ 1/4 := by
    rw [zero]
    linarith [sin_le_one θ]
  have c2 : cos ψ ^ 2 ≤ (1/4 : ℝ)^2 := by
    rw [←sq_abs]
    gcongr
  have large : 1/2 < |sin ψ| := by
    by_contra! h
    have s2 : sin ψ ^ 2 ≤ (1/2 : ℝ)^2 := by
      rw [←sq_abs]
      gcongr
    linarith [sin_sq_add_cos_sq ψ]
  have term : |cos ψ*cos θ| ≤ sin θ / 4 := by
    rw [abs_mul]
    calc
      _ ≤ |cos ψ| * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one θ) (abs_nonneg _)
      _ ≤ _ := by simpa only [mul_one, zero] using old_error
  have err : abs (-(cos ψ * cos θ) + F) ≤ sin θ / 2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith
  rw [cos_add]
  rcases le_or_gt (sin ψ) 0 with hn | hp
  · rw [abs_of_nonpos hn] at large
    apply mul_pos_of_neg_of_neg (by linarith)
    have goal := mul_lt_mul_of_pos_right (show sin ψ < -(1/2) by linarith) shift
    linarith [(abs_le.mp err).2]
  · rw [abs_of_pos hp] at large
    apply mul_pos hp
    have goal := mul_lt_mul_of_pos_right large shift
    linarith [(abs_le.mp err).1]

#print axioms next_sign

end OrderedPartitions.TwoPolePhase
