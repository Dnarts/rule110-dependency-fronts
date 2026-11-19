import Rule110DomainWallA
namespace Rule110FrontGlue
open Rule110Complete

def splice (cut : Int) (u v : Config) : Config :=
  fun x => if x ≤ cut then u x else v x

/-- A moving cut may move one cell per tick; only the shared collar matters. -/
theorem step_splice (c d : Int) (u v : Config) (speed : c-1 ≤ d ∧ d ≤ c+1)
    (collar : ∀ x, c-2 ≤ x → x ≤ c+2 → u x = v x) :
    step (splice c u v) = splice d (step u) (step v) := by
  funext x
  by_cases hx : x ≤ d
  · have h (z : Int) (hz : x-1 ≤ z ∧ z ≤ x+1) : splice c u v z = u z := by
      by_cases hzc : z ≤ c
      · simp [splice,hzc]
      · simpa [splice,hzc] using (collar z (by omega) (by omega)).symm
    simp only [splice,ite_eq_left hx,step]
    change f (splice c u v (x-1)) (splice c u v x) (splice c u v (x+1)) = _
    rw [h _ (by omega),h _ (by omega),h _ (by omega)]
  · have h (z : Int) (hz : x-1 ≤ z ∧ z ≤ x+1) : splice c u v z = v z := by
      by_cases hzc : z ≤ c
      · simpa [splice,hzc] using collar z (by omega) (by omega)
      · simp [splice,hzc]
    simp only [splice,ite_eq_right hx,step]
    change f (splice c u v (x-1)) (splice c u v x) (splice c u v (x+1)) = _
    rw [h _ (by omega),h _ (by omega),h _ (by omega)]

theorem evolve_splice (c : Nat → Int) (u v : Config)
    (speed : ∀ t, c t-1 ≤ c (t+1) ∧ c (t+1) ≤ c t+1)
    (collar : ∀ t x, c t-2 ≤ x → x ≤ c t+2 → evolve t u x = evolve t v x)
    (t : Nat) :
    evolve t (splice (c 0) u v) = splice (c t) (evolve t u) (evolve t v) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [evolve,ih,step_splice _ _ _ _ (speed t) (collar t)]; rfl

theorem travelling_return (u : Config) (p : Nat) (d : Int)
    (base : evolve p u = shift d u) (k : Nat) :
    evolve (p*k) u = shift ((k:Int)*d) u := by
  induction k with
  | zero => funext x; simp [evolve,shift]
  | succ k ih =>
    rw [Nat.mul_succ,Nat.add_comm,evolve_add,ih,evolve_shift,base,shift_add]
    simp [Int.add_mul]

theorem A_outer_13 (u : Config) (base : evolve 273 u = shift (-28) u) :
    evolve 11466 u = shift (-1176) u := travelling_return u 273 (-28) base 42

#print axioms evolve_splice
#print axioms A_outer_13
end Rule110FrontGlue
