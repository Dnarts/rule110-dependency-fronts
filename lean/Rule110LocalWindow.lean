import Rule110Fin1320Bridge
import Rule110Ether

namespace Rule110LocalWindow
open Rule110Complete

abbrev V := BitVec 5520

def advance (u : V) : V :=
  let l := (u <<< 1) ||| (u >>> 5519)
  let r := (u >>> 1) ||| (u <<< 5519)
  (u ^^^ r) ^^^ ((u &&& r) ^^^ (l &&& u &&& r))

def run : Nat → V → V
  | 0,u => u
  | t+1,u => run t (advance u)

def pos (x : Int) : Nat := ((x+2760)%5520).toNat
def line (u : V) (x : Int) : Bool := u.getLsbD (pos x)
def defect (u : V) : V := u ^^^ (1#5520 <<< 2760)

theorem line_advance (u : V) : line (advance u) = step (line u) := by
  funext x
  have hi : pos x < 5520 := by unfold pos; omega
  have hL : ((u <<< 1) ||| (u >>> 5519)).getLsbD (pos x) = line u (x-1) := by
    by_cases hz : pos x = 0
    · have hh : pos (x-1) = 5519 := by unfold pos at *; omega
      simp [line, hz, hh]
    · have hh : pos (x-1) = pos x - 1 := by unfold pos at *; omega
      simp [line, hh, hi, show ¬ pos x < 1 by omega, show pos x - 1 < 5520 by omega,
        BitVec.getLsbD_of_ge u _ (show 5520 ≤ 5519 + pos x by omega)]
  have hR : ((u >>> 1) ||| (u <<< 5519)).getLsbD (pos x) = line u (x+1) := by
    by_cases hz : pos x = 5519
    · have hh : pos (x+1) = 0 := by unfold pos at *; omega
      simp [line, hz, hh]
    · have hh : pos (x+1) = pos x + 1 := by unfold pos at *; omega
      simp [line, hh, hi, show pos x < 5519 by omega, Nat.add_comm]
  simp only [line, advance, step, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    hL,hR,f_eq_fANF,fANF]

theorem line_run (t : Nat) (u : V) : line (run t u) = evolve t (line u) := by
  induction t generalizing u with
  | zero => rfl
  | succ t ih =>
    rw [run, ih, line_advance, show evolve (t+1) (line u) = evolve t (step (line u)) from evolve_add t 1 _]

theorem single_defect (u : V) (x : Int) (hx : -317 ≤ x) (hx' : x ≤ -291) :
    evolve 2196 (Rule110Fin1320Bridge.flipZero (line u)) x = line (run 2196 (defect u)) x := by
  rw [line_run]
  apply Rule110Fin1320Bridge.evolve_agree_window
  intro j hlo hhi
  have hj : -2760 ≤ j ∧ j < 2760 := by omega
  have hp : pos j = (j+2760).toNat := by unfold pos; omega
  by_cases hz : j=0
  · subst j; simp [Rule110Fin1320Bridge.flipZero, line, pos, defect]
  · have hn : (j+2760).toNat ≠ 2760 := by omega
    have hb : (1#5520 <<< 2760).getLsbD (pos j) = false := by
      rw [BitVec.getLsbD_shiftLeft, hp]
      by_cases hl : (j+2760).toNat < 2760
      · simp [hl]
      · simp [show (j+2760).toNat - 2760 ≠ 0 by omega]
    simp only [Rule110Fin1320Bridge.flipZero, ite_eq_right hz, line, defect, BitVec.getLsbD_xor, hb, Bool.xor_false]

/-- Little-endian period word, rotated so physical x reads the bit at x+ph. -/
def input (period packed ph : Nat) : V :=
  (BitVec.ofNat 5520 (((2^5520-1)/(2^period-1))*packed)).rotateRight ph

/-- The 27-cell mask uses physical x increasing (bit 0 at -317). -/
def snapshot (u : V) : Bool × BitVec 27 :=
  ((run 2196 u).getLsbD (pos (-304)), (run 2196 (defect u)).extractLsb' (pos (-317)) 27)

theorem snapshot_bg (u : V) :
    (snapshot u).1 = evolve 2196 (line u) (-304) := congrFun (line_run 2196 u) (-304)

theorem snapshot_y (u : V) (i : Fin 27) :
    (snapshot u).2.getLsbD i.val =
      evolve 2196 (Rule110Fin1320Bridge.flipZero (line u)) (-317 + (i.val:Int)) := by
  rw [single_defect _ _ (by omega) (by omega)]
  simp only [snapshot, BitVec.getLsbD_extractLsb', i.isLt, Bool.true_and, decide_true]
  unfold line
  rw [show pos (-317 + (i.val:Int)) = pos (-317) + i.val by unfold pos; omega]

abbrev Spec := Nat × Nat × Nat
def initial (s : Spec) := input s.1 s.2.1 s.2.2
def exceptional : List Spec := [(10,576,9),(8,244,4)]

def RowValid (r : Bool × BitVec 27) : Prop :=
  r.1 = r.2.getLsbD 13 ∨ ∀ a p : Fin 14, ∃ i : Fin 14,
    r.2.getLsbD (a.val+i.val) ≠ Rule110Ether.ether ((p.val:Int)+i.val)

instance (r : Bool × BitVec 27) : Decidable (RowValid r) := by unfold RowValid; infer_instance

end Rule110LocalWindow
