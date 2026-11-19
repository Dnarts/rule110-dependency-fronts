import Rule110Fin1320Bridge
import Rule110KernelCertificate

namespace Rule110KernelCert

open Rule110Complete Rule110Fin1320Bridge

def toFinRing (u : RingBV) : Ring := fun i => u.getLsbD i.val

private theorem rotL1_bit (u : RingBV) (i : Fin 1320) :
    (rotL1 u).getLsbD i.val = u.getLsbD (ix ((i.val : Int) - 1)).val := by
  have hi := i.isLt
  by_cases h : i.val = 0
  · have hj : (ix ((i.val : Int) - 1)).val = 1319 := by simp [h]; rfl
    rw [hj]; simp [rotL1, h]
  · have hj : (ix ((i.val : Int) - 1)).val = i.val - 1 := by
      unfold ix
      dsimp
      omega
    simp [rotL1, hi, show ¬ i.val < 1 by omega, show i.val - 1 < 1320 by omega, hj,
      BitVec.getLsbD_of_ge u _ (show 1320 ≤ 1319 + i.val by omega)]

private theorem rotR1_bit (u : RingBV) (i : Fin 1320) :
    (rotR1 u).getLsbD i.val = u.getLsbD (ix ((i.val : Int) + 1)).val := by
  have hi := i.isLt
  by_cases h : i.val = 1319
  · have hj : (ix ((i.val : Int) + 1)).val = 0 := by simp [h]; rfl
    rw [hj]; simp [rotR1, h]
  · have hj : (ix ((i.val : Int) + 1)).val = i.val + 1 := by
      unfold ix
      dsimp
      omega
    simp [rotR1, hi, show i.val < 1319 by omega, hj, Nat.add_comm]

theorem toFinRing_step (u : RingBV) :
    toFinRing (ringStepBV u) = ringStep (toFinRing u) := by
  funext i
  simp only [toFinRing, ringStepBV, ringStep, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    rotL1_bit, rotR1_bit, f_eq_fANF, fANF]

theorem toFinRing_evolve (t : Nat) (u : RingBV) :
    toFinRing (ringEvolveBV t u) = ringEvolve t (toFinRing u) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [ringEvolveBV, ringEvolve, toFinRing_step, ih]

theorem toFinRing_flipCenter (u : RingBV) :
    toFinRing (flipCenterBV u) = flipCenter (toFinRing u) := by
  funext i
  have hi := i.isLt
  simp only [toFinRing, flipCenterBV, flipCenter, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft]
  by_cases he : i.val = 660
  · simp [he]
  · by_cases hl : i.val < 660
    · simp [hi, hl, he]
    · have hn : i.val - 660 ≠ 0 := by omega
      simp [hi, hl, he, hn]

theorem centeredLift_evolveBV (t : Nat) (u : RingBV) :
    centeredLift (toFinRing (ringEvolveBV t u)) =
      evolve t (centeredLift (toFinRing u)) := by
  rw [toFinRing_evolve, centeredLift_evolve]

theorem singleDefect_BV_bridge (u : RingBV) (t : Nat) (i : Int)
    (ht : t ≤ 380) (hlo : -(t : Int) ≤ i) (hhi : i ≤ (t : Int)) :
    evolve t (flipZero (centeredLift (toFinRing u))) i =
      centeredLift (toFinRing (ringEvolveBV t (flipCenterBV u))) i := by
  rw [toFinRing_evolve, toFinRing_flipCenter]
  exact singleDefect_ring_bridge (toFinRing u) t i ht hlo hhi

#print axioms singleDefect_BV_bridge

#print axioms toFinRing_step
#print axioms toFinRing_evolve

end Rule110KernelCert
