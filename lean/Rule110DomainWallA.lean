import Rule110LocalWindow

namespace Rule110LocalWindow
open Rule110Complete Rule110Ether Rule110Fin1320Bridge

def domainWallA (x : Int) : Bool :=
  if -1397 ≤ x then shift (-5) ether x
  else if -1399 ≤ x then false
  else shift (-8) ether x

/-- Repeat one little-endian 14-bit word. -/
private def repeat14 (word copies : Nat) : Nat :=
  word * ((2^(14*copies)-1)/(2^14-1))

/-- Bit 31 is x=-2729. Bits 1361 and 1362 are the two zero cells.
    Bit 1363 is x=-1397. The last included bit is 2846 (x=86). -/
def domainWallTileA : V := BitVec.ofNat 5520
  ((repeat14 4598 95 <<< 31) ||| (repeat14 9196 106 <<< 1363))

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 8192

theorem tileA_reads (x : Int) (hl : -2729 ≤ x) (hr : x ≤ 86) :
    line domainWallTileA x = domainWallA x := by
  have table : ∀ i : Fin 2816, line domainWallTileA (-2729+(i.val:Int)) =
      domainWallA (-2729+(i.val:Int)) := by decide
  let i : Fin 2816 := ⟨(x+2729).toNat, by omega⟩
  have h := table i
  rwa [show -2729+(i.val:Int)=x by dsimp [i]; omega] at h

private theorem phase7 (d : Int) : evolve 7 (shift d ether) = shift d ether := by
  rw [evolve_shift, show evolve 7 ether = ether from ether_period 1]

theorem domain_wall_A_period7 : evolve 7 domainWallA = domainWallA := by
  funext x
  by_cases front : -1390 ≤ x
  · have h : evolve 7 domainWallA x = evolve 7 (shift (-5) ether) x := by
      apply evolve_agree_window
      intro j hl _
      simp [domainWallA, show -1397 ≤ j by omega]
    simpa [phase7,domainWallA,show -1397 ≤ x by omega] using h
  by_cases deep : x ≤ -1407
  · have h : evolve 7 domainWallA x = evolve 7 (shift (-8) ether) x := by
      apply evolve_agree_window
      intro j _ hr
      simp [domainWallA,show ¬ -1397 ≤ j by omega,show ¬ -1399 ≤ j by omega]
    simpa [phase7,domainWallA,show ¬ -1397 ≤ x by omega,show ¬ -1399 ≤ x by omega] using h
  have table : ∀ i : Fin 16, evolve 7 domainWallA (-1406+(i.val:Int)) =
      domainWallA (-1406+(i.val:Int)) := by decide
  let i : Fin 16 := ⟨(x+1406).toNat, by omega⟩
  have h := table i
  rwa [show -1406+(i.val:Int)=x by dsimp [i]; omega] at h

theorem domain_wall_A_period (n : Nat) : evolve (7*n) domainWallA = domainWallA := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 7*(n+1)=7+7*n by omega,evolve_add,ih,domain_wall_A_period7]

theorem domain_wall_A_step (u : Config)
    (h : ∀ i, -2729 ≤ i → i ≤ 86 → u i = domainWallA i)
    (x : Int) (hl : -2029 ≤ x) (hr : x ≤ -908) :
    evolve 882 u x = domainWallA x := by
  rw [← congrFun (domain_wall_A_period 126) x]
  apply agree3m u domainWallA 294 x
  intro i lo hi
  apply h <;> omega

#print axioms tileA_reads
#print axioms domain_wall_A_period7
#print axioms domain_wall_A_step
end Rule110LocalWindow
