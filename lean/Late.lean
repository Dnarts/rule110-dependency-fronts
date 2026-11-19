import Crystal50WedgeAll
import EtherWedge
import LeftCrystal50
import Rule110LeftCheckpoints
import Rule110Right20
namespace Rails
open Rule110KernelCert Rule110Fin1320Bridge
theorem late_all (t : Nat) (j : Int) (ht : 2485 ≤ t)
    (hl : -((t-t/3:Nat):Int) ≤ j) (hr : j ≤ t) : EssentialAt t j := by
  by_cases h : j < -((t-t/3:Nat):Int)+106
  · let k := (j+((t-t/3:Nat):Int)).toNat
    have z := strip_all leftPos 106 30 (by decide) LeftCheckpoints.strip_base t k (by omega) (by dsimp [k]; omega)
    simpa only [show -leftPos t k=j by unfold leftPos e; dsimp [k]; omega] using z
  by_cases he : 60-((t/2:Nat):Int) ≤ -j
  · simpa only [Int.neg_neg] using EtherWedge.half_sector t (-j) (by omega) he (by omega)
  by_cases hc : -(t:Int)+1302 ≤ -j
  · simpa only [Int.neg_neg] using Crystal50Wedge.wedge_all t (-j) ht hc (by omega)
  by_cases hs : 20 ≤ (t:Int)-j
  · simpa only [show (t:Int)-(t-j)=j by omega] using LeftCrystal50.left_strip t (by omega) (t-j) hs (by omega)
  let k := ((t:Int)-j).toNat
  simpa only [show (t:Int)-(k:Int)=j by dsimp [k]; omega] using right_boundary_width20 t k (by omega) (by dsimp [k]; omega)
#print axioms late_all
end Rails
