import Crystal50Data
namespace Rails.Crystal50Wedge
open Rule110Complete Rule110LocalWindow Rule110Fin1320Bridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

def Cm (p : Phase) (t : Nat) (x : Int) := cell (cmRows p)[t%50]! (x%50)
def Bg (p : Phase) (t : Nat) (x : Int) := cell (bgRows p)[t%50]! (x%10)
def seed (p : Phase) := input 10 576 (phase p)

private theorem tableStep (tab : Array Nat) (w : Nat) (hw : 0 < w)
    (h : ∀ i : Fin 50, ∀ j : Fin w,
      let row := fun (t : Nat) (x : Int) => cell tab[t%50]! (x%w)
      step (row i.val) j.val = row (i.val+1) j.val)
    (t : Nat) (x : Int) :
    let row := fun (t : Nat) (x : Int) => cell tab[t%50]! (x%w)
    step (row t) x = row (t+1) x := by
  have hwI : (0:Int) < w := by omega
  have hlo := Int.emod_nonneg x (show (w:Int) ≠ 0 by omega)
  have hhi := Int.emod_lt_of_pos x hwI
  let j : Fin w := ⟨(x%w).toNat,by omega⟩
  have hj : (j.val:Int)=x%w := by dsimp [j]; omega
  have e := h ⟨t%50,by omega⟩ j
  simp only [step,hj,Int.emod_sub_emod,Int.emod_add_emod,Int.emod_emod,
    Nat.mod_mod,show (t%50+1)%50=(t+1)%50 by omega] at e
  exact e

theorem Cm_step (p : Phase) (t : Nat) (x : Int) : step (Cm p t) x = Cm p (t+1) x := by
  apply tableStep (cmRows p) 50 (by decide) _ t x
  cases p <;> decide +kernel
theorem Bg_step (p : Phase) (t : Nat) (x : Int) : step (Bg p t) x = Bg p (t+1) x := by
  apply tableStep (bgRows p) 10 (by decide) _ t x
  cases p <;> decide +kernel
theorem Cm_period (p : Phase) (t : Nat) (x : Int) :
    Cm p (t+50) x = Cm p t x ∧ Cm p t (x+50) = Cm p t x := by simp [Cm]
private def Hit (i : Fin 50) (j : Fin 50) (p : Phase) := Bg p i.val j.val ≠ Cm p i.val j.val
private instance (i j p) : Decidable (Hit i j p) := by unfold Hit; infer_instance
theorem coverage (t : Nat) (x : Int) : ∃ p, Bg p t x ≠ Cm p t x := by
  have tab : ∀ i j, Hit i j .p0 ∨ Hit i j .p1 ∨ Hit i j .p2 ∨ Hit i j .p3 ∨ Hit i j .p7 ∨ Hit i j .p9 := by decide +kernel
  let j : Fin 50 := ⟨(x%50).toNat,by omega⟩
  let i : Fin 50 := ⟨t%50,by omega⟩
  have lift (p : Phase) (h : Hit i j p) : ∃ p, Bg p t x ≠ Cm p t x := by
    refine ⟨p,?_⟩
    simpa only [Hit,Bg,Cm,i,j,show ((x%50).toNat:Int)=x%50 by omega,
      Nat.mod_mod,Int.emod_emod,show x%50%10=x%10 by omega] using h
  rcases tab i j with h|h|h|h|h|h <;> exact lift _ h

end Rails.Crystal50Wedge
