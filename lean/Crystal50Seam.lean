import Crystal50Wedge
namespace Rails.Crystal50Wedge
open Rule110Complete Rule110LocalWindow Rule110Fin1320Bridge
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 8192
def Y (p : Phase) (t : Nat) := evolve t (flipZero (line (seed p)))
private theorem snapBase (p : Phase) : run 2450 (defect (seed p)) = snap p := by cases p <;> decide +kernel
theorem readSnap (p : Phase) (n : Nat) (x : Int)
    (hl : -5520 < x-(n+2450:Nat)) (hr : x+(n+2450:Nat) < 5520) :
    Y p (n+2450) x = line (run n (snap p)) x := by
  unfold Y
  rw [local_obs _ _ _ hl hr, ← snapBase, line_run, line_run, evolve_add]
  rw [line_run]
theorem initialMedium (p : Phase) (x : Int) (lo : -2430 ≤ x) (hi : x < -350) :
    Y p 2450 x = Cm p 2450 x := by
  rw [readSnap p 0 x (by omega) (by omega)]
  apply finite_interval (fun z => line (snap p) z = Cm p 2450 z) (-2430) 2080 _ x <;> try omega
  cases p <;> decide +kernel
private theorem ret (p : Phase) (x : Int) (hx : x ≤ -1139) :
    Y p 2500 (x-50) = Y p 2450 x := by
  by_cases h : x < -2450
  · unfold Y
    rw [outer _ 2500 _ (Or.inl (by omega)), outer _ 2450 _ (Or.inl (by omega)),
        bg_evolve p 2500 (by decide),bg_evolve p 2450 (by decide)]
    simp only [Bg,show (x-50)%10=x%10 by omega]
  · rw [readSnap p 50 (x-50) (by omega) (by omega),readSnap p 0 x (by omega) (by omega)]
    apply finite_interval (fun z => line (run 50 (snap p)) (z-50) = line (snap p) z) (-2450) 1312 _ x <;> try omega
    cases p <;> decide +kernel
private theorem retLater (p : Phase) (n : Nat) (x : Int) (hx : x ≤ -1139-(n:Int)) :
    Y p (n+2500) (x-50) = Y p (n+2450) x := by
  have h := evolve_agree_window n (shift 50 (Y p 2500)) (Y p 2450) x
    (fun j _ hj => ret p j (by omega))
  rw [evolve_shift] at h
  simpa only [Y,shift,evolve_add n 2500,evolve_add n 2450] using h
theorem seam (p : Phase) (n : Nat) (k : Int) (lo : 1280 ≤ k) (hi : k ≤ 1311) :
    Y p (n+2450) (-(n+2450:Int)+k) = Cm p (n+2450) (-(n+2450:Int)+k) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 50
    · rw [readSnap p n _ (by omega) (by omega)]
      have tab : ∀ r : Fin 50, ∀ j : Fin 32,
          line (run r.val (snap p)) (-(r.val+2450:Int)+(1280+j.val)) =
          Cm p (r.val+2450) (-(r.val+2450:Int)+(1280+j.val)) := by cases p <;> decide +kernel
      let j : Fin 32 := ⟨(k-1280).toNat, by omega⟩
      simpa only [show (1280+(j.val:Int))=k by dsimp [j]; omega] using tab ⟨n,hn⟩ j
    · let m := n-50
      have h := ih m (by dsimp [m]; omega)
      have z : n=m+50 := by dsimp [m]; omega
      rw [show n+2450=m+2500 by omega,show -(n+2450:Int)+k=(-(m+2450:Int)+k)-50 by omega,
        retLater p m _ (by omega),h]
      unfold Cm
      rw [show (m+2500)%50=(m+2450)%50 by omega,show ((-(m+2450:Int)+k)-50)%50=(-(m+2450:Int)+k)%50 by omega]
#print axioms seam
#print axioms initialMedium
end Rails.Crystal50Wedge
