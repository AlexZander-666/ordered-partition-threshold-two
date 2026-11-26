import OrderedPartitions.HardRodWindow
import OrderedPartitions.InterlacingStep

noncomputable section
namespace OrderedPartitions.HardRod
open Polynomial InterlacingStep

/-- All active roots strictly interlace for any two lengths one unit apart,
including the right integral endpoint, when the new top coefficient is zero. -/
theorem unit_interlacing (d : ℕ) {N : ℕ} (dN : d+1≤N) {x : ℝ}
    (lo : (d:ℝ)+1<x) (hi : x≤(d:ℝ)+2) :
    ∃ a : Fin d→ℝ, ∃ b : Fin (d+1)→ℝ,
      RootArray (phi N (x-1)) a ∧ RootArray (phi N x) b ∧ Interlaces a b := by
  induction d generalizing x with
  | zero =>
    have x1 : 1<x := by simpa using lo
    have x2 : x≤2 := by simpa using hi
    let a : Fin 0→ℝ := Fin.elim0
    have s0 := phi_shape (N:=N) (d:=0) (x:=x-1) (Nat.zero_le _)
      (by norm_num;linarith) (by norm_num;linarith)
    have s1 := phi_shape (N:=N) (d:=1) (x:=x) dN (by simpa using x1) (by norm_num;exact x2)
    have ha : RootArray (phi N (x-1)) a := by
      refine ⟨fun i ↦ Fin.elim0 i,fun i ↦ Fin.elim0 i,?_,s0.1,fun i ↦ Fin.elim0 i⟩
      intro h
      have z := s0.2.2
      simp [h] at z
    obtain ⟨b,hb,inter⟩ := rise_of_alternating_sign ha.ordered ha.negative s1.2.1
      (by linarith [s1.2.2]) s1.1 (fun i ↦ Fin.elim0 i)
    exact ⟨a,b,ha,hb,inter⟩
  | succ d ih =>
    push_cast at lo hi
    obtain ⟨a,b,ha,hb,inter⟩ := ih (by omega) (x:=x-1) (by linarith) (by linarith)
    have sp := phi_shape (N:=N) (d:=d) (x:=x-1-1) (by omega) (by linarith) (by linarith)
    have sr := phi_shape (N:=N) (d:=d+2) (x:=x) (by omega) (by push_cast;linarith) (by push_cast;linarith)
    have bound : x≤(N:ℝ)+1 := by
      have le : (d:ℝ)+2≤N := by exact_mod_cast dN
      linarith
    obtain ⟨z,hz,ord⟩ := rise_of_opposite ha hb inter sp.2.1 sr.2.1 (by linarith [sr.2.2]) sr.1
      (fun i ↦ by simpa using phi_sturm (N:=N) (s:=x-1) (hb.negative i) (by simpa using bound) (hb.zeros i))
    exact ⟨b,z,hb,hz,ord⟩

#print axioms unit_interlacing
end OrderedPartitions.HardRod
