import Crystal50Media
namespace Rails.Crystal50Wedge
open Rule110Complete Rule110LocalWindow Rule110Fin1320Bridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

theorem bg_base (p : Phase) (x : Int) : evolve 2 (line (seed p)) x = Bg p 2 x := by
  let tile := BitVec.ofNat 10 (bgRows p)[2]!
  have hr : run 2 (seed p) = tile.replicate 552 := by cases p <;> decide +kernel
  have hp : pos x < 10*552 := by unfold pos; omega
  have hmod : pos x % 10 = (x%10).toNat := by unfold pos; omega
  rw [← line_run,hr]
  simp only [line,BitVec.getLsbD_replicate,hp,decide_true,Bool.true_and,
    tile,BitVec.getLsbD_ofNat,hmod,Bg,cell]
  simp [show (x%10).toNat < 10 by omega]
theorem bg_evolve (p : Phase) (t : Nat) (ht : 2 ≤ t) : evolve t (line (seed p)) = Bg p t := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction n with
  | zero => exact funext (bg_base p)
  | succ n ih => exact (congrArg step ih).trans (funext (Bg_step p _))
private theorem snap_eq (p : Phase) : run 2450 (defect (seed p)) = snap p := by cases p <;> decide +kernel

theorem cm_base (p : Phase) (x : Int) (lo : -2430 ≤ x) (hi : x ≤ -1100) :
    evolve 2450 (flipZero (line (seed p))) x = Cm p 2450 x := by
  rw [local_obs _ _ _ (by omega) (by omega),snap_eq]
  apply finite_interval (fun z => line (snap p) z = Cm p 2450 z) (-2430) 1331 _ x <;> try omega
  cases p <;> decide +kernel

theorem essential_of_cm (t : Nat) (x : Int) (ht : 2 ≤ t)
    (h : ∀ p, evolve t (flipZero (line (seed p))) x = Cm p t x) :
    Rule110KernelCert.EssentialAt t (-x) := by
  obtain ⟨p,hp⟩ := coverage t x
  apply essential (line (seed p))
  rwa [bg_evolve p t ht,h]
theorem cm_evolve (p : Phase) (n s : Nat) : evolve n (Cm p s) = Cm p (n+s) := by
  induction n with
  | zero => simp [evolve]
  | succ n ih =>
    rw [evolve,Nat.succ_add,ih]
    exact funext (Cm_step p (n+s))

theorem wedge_initial (t : Nat) (x : Int) (ht : 2485 ≤ t) (ht' : t ≤ 2582)
    (hl : -(t:Int)+1302 ≤ x) (hr : x ≤ 59-((t/2:Nat):Int)) :
    Rule110KernelCert.EssentialAt t (-x) := by
  apply essential_of_cm t x (by omega)
  intro p
  let n := t-2450
  have hn : n+2450=t := by dsimp [n]; omega
  rw [← hn,evolve_add,← cm_evolve p n 2450]
  apply evolve_agree_window
  intro j hj hk
  apply cm_base <;> dsimp [n] at * <;> omega

#print axioms wedge_initial
#print axioms Cm_step
#print axioms cm_base
#print axioms essential_of_cm
end Rails.Crystal50Wedge
