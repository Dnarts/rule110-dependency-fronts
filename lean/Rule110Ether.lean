import Rule110Complete

namespace Rule110Ether
open Rule110Complete

/-- The printed word reads 10110010001111 in increasing depth, opposite to x. -/
def ether (x : Int) : Bool :=
  ([true,true,true,true,false,false,false,true,false,false,true,true,false,true] : List Bool).getD
    (x % 14).toNat false

private theorem residue (x d : Int) : ether (x % 14 + d) = ether (x + d) := by
  unfold ether
  rw [show (x % 14 + d) % 14 = (x + d) % 14 by omega]

theorem ether_step : step ether = shift (-4) ether := by
  have table : ∀ r : Fin 14,
      f (ether ((r.val : Int) + (-1))) (ether ((r.val : Int) + 0))
        (ether ((r.val : Int) + 1)) = ether ((r.val : Int) + 4) := by decide
  funext x
  let r : Fin 14 := ⟨(x % 14).toNat, by omega⟩
  have hr : (r.val : Int) = x % 14 := by dsimp [r]; omega
  have h := table r
  simp only [hr, residue, Int.add_zero] at h
  rw [show ether (x % 14) = ether x by simpa using residue x 0] at h
  exact h

theorem evolve_ether (t : Nat) : evolve t ether = shift (-4 * (t : Int)) ether := by
  induction t with
  | zero => funext i; simp [evolve, shift]
  | succ t ih =>
    rw [evolve, ih, step_shift, ether_step, shift_add]
    congr 1
    omega

theorem ether_period (t : Nat) : evolve (7*t) ether = ether := by
  rw [evolve_ether]
  funext x
  unfold shift ether
  rw [show (x - -4 * (↑(7*t) : Int)) % 14 = x % 14 by omega]

/-- Agreement on this closed interval suffices for 3m steps. -/
theorem agree3m (u v : Config) (m : Nat) (x : Int)
    (h : ∀ i, x - 2*(m : Int) ≤ i → i ≤ x + 3*(m : Int) → u i = v i) :
    evolve (3*m) u x = evolve (3*m) v x := by
  induction m generalizing x with
  | zero => exact h x (by omega) (by omega)
  | succ m ih =>
    rw [show 3*(m+1) = 3 + 3*m by omega, evolve_add, evolve_add]
    apply evolve3_eq_of_agree6 <;> apply ih <;> intro i hl hr <;> apply h <;> omega

/-- Any translated ether phase, with arbitrary exterior on both sides. -/
theorem ether_block_882 (u : Config) (s phase x : Int)
    (h : ∀ i, s ≤ i → i < s+1484 → u i = shift phase ether i)
    (hl : s+588 ≤ x) (hr : x < s+602) : evolve 882 u x = shift phase ether x := by
  have hv : evolve 882 (shift phase ether) = shift phase ether := by
    rw [evolve_shift, show evolve 882 ether = ether from ether_period 126]
  rw [← congrFun hv x]
  apply agree3m u (shift phase ether) 294 x
  intro i lo hi
  apply h <;> omega

/-- An equality on a whole half-line at times 0 and 3 propagates to the ray. -/
theorem ray_of_three_step (u : Config) (a : Int)
    (h : ∀ i, a ≤ i → evolve 3 u (i+2) = u i) (q : Nat) (x : Int) (hx : a ≤ x) :
    evolve (3*q) u (x + 2*(q : Int)) = u x := by
  induction q with
  | zero => simp [evolve]
  | succ q ih =>
    have ht : 3*(q+1) = 3*q+3 := by omega
    rw [ht, evolve_add]
    calc
      evolve (3*q) (evolve 3 u) (x + 2*↑(q+1)) =
          evolve (3*q) (shift 2 u) (x + 2*↑(q+1)) := by
        apply agree3m
        intro i lo _
        simpa [shift] using h (i-2) (by omega)
      _ = u x := by
        rw [evolve_shift]
        change evolve (3*q) u (x + 2*↑(q+1) - 2) = _
        rwa [show x + 2*↑(q+1) - 2 = x + 2*(q:Int) by omega]

#print axioms ray_of_three_step

#print axioms ether_period
#print axioms ether_block_882
end Rule110Ether
