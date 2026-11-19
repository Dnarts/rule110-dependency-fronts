import Rule110CheckpointSoundness
import Rule110LocalWindow
namespace Rails
open Rule110Complete Rule110Fin1320Bridge Rule110LocalWindow
def cell (w : Nat) (i : Int) : Bool := w.testBit i.toNat
def profile (l r : Nat → Config) (tab : Nat → Nat) (P : Nat) (D lo hi : Int) (t : Nat) (x : Int) : Bool :=
  let z := x - ((t:Int)*D/P)
  if z < lo then l t x else if hi < z then r t x else cell (tab (t%P)) (z-lo)
theorem propagate (a : Nat → Config) (P : Nat) (D : Int) (hp : 0<P)
    (ret : ∀ t x, a (t+P) (x+D) = a t x)
    (base : ∀ t, t<P → ∀ x, step (a t) x = a (t+1) x) :
    ∀ t x, step (a t) x = a (t+1) x := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro x
    by_cases h : t<P
    · exact base t h x
    let k := t-P
    have hk : t=k+P := by dsimp [k]; omega
    have hr (i : Int) : a t i = a k (i-D) := by
      simpa only [← hk, Int.sub_add_cancel] using ret k (i-D)
    have hh := ih k (by dsimp [k]; omega) (x-D)
    unfold step at hh ⊢
    rw [hr, hr, hr, show x-1-D=x-D-1 by omega, show x+1-D=x-D+1 by omega, hh]
    symm
    simpa only [show k+1+P=t+1 by omega, Int.sub_add_cancel] using ret (k+1) (x-D)
theorem finite_interval (p : Int → Prop) (a : Int) (w : Nat)
    (h : ∀ i : Fin w, p (a+i.val)) (x : Int) (hl : a≤x) (hr : x<a+w) : p x := by
  let i : Fin w := ⟨(x-a).toNat, by omega⟩
  exact (show a+(i.val:Int)=x by dsimp [i]; omega) ▸ h i
end Rails
