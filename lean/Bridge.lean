import Base
namespace Rails
open Rule110Complete Rule110Fin1320Bridge Rule110LocalWindow Rule110Ether
theorem def_agree (u : V) (j : Int) (lo : -5520 < j) (hi : j < 5520) :
    flipZero (line u) j = line (defect u) j := by
  by_cases hz : j=0
  · subst j; simp [flipZero,line,pos,defect]
  · have hn : pos j ≠ 2760 := by unfold pos; omega
    have hb : (1#5520 <<< 2760).getLsbD (pos j) = false := by
      rw [BitVec.getLsbD_shiftLeft]
      by_cases h : pos j < 2760
      · simp [h]
      · simp [show pos j - 2760 ≠ 0 by omega]
    simp only [flipZero, ite_eq_right hz, line, defect, BitVec.getLsbD_xor, hb, Bool.xor_false]
theorem local_obs (u : V) (t : Nat) (x : Int) (hl : -5520<x-t) (hr : x+t<5520) :
    evolve t (flipZero (line u)) x = line (run t (defect u)) x := by
  rw [line_run]; apply evolve_agree_window; intro j lo hi; apply def_agree <;> omega
theorem outer (u : Config) (t : Nat) (x : Int)
    (h : x < -(t:Int) ∨ (↑(t-t/3):Int)<x) :
    evolve t (flipZero u) x = evolve t u x := by
  rcases h with h|h
  · apply evolve_agree_window; intro j _ hj; simp [flipZero,show j≠0 by omega]
  · apply global_upper_bound t _ _ 0
    · intro j hj; simp [flipZero,show j≠0 by omega]
    · omega
theorem essential (u : Config) (t : Nat) (s : Int)
    (h : evolve t u s ≠ evolve t (flipZero u) s) :
    Rule110KernelCert.EssentialAt t (-s) := by
  refine ⟨shift (-s) u, shift (-s) (flipZero u), ?_, ?_⟩
  · intro i hi; simp [shift,flipZero,show i+s≠0 by omega]
  · simpa only [evolve_shift,shift,Int.zero_sub,Int.neg_neg] using h
end Rails
