import Rule110Fin1320Bridge

/-!
# Analytic induction from finite base half-ray equalities

This file deliberately has NO `sorry`, `axiom`, or table constants.
Its hypotheses `hBase` are genuine proof obligations: they must be
established by relating dynamically computed ring states to packed bits.

If `LeftQ` holds for 30 consecutive base times, then it holds at every
later time. If `RightQ` holds for 16 consecutive base times, likewise.
These are the analytic closure arguments needed after the Fin 1320 ↔ ℤ bridge.
-/

namespace Rule110Fin1320Bridge

open Rule110Complete

/-- The physical right-moving defect frontier `e_t = t - floor(t/3)`. -/
def e (t : Nat) : Nat := t - t / 3

theorem e_add30 (t : Nat) : (e (t + 30) : Int) = (e t : Int) + 20 := by
  simp only [e]
  omega

/-- Shift recurrence on the ENTIRE exterior right half-ray (the left input edge). -/
def LeftQ (Y : Config) (W t : Nat) : Prop :=
  ∀ s : Int, (e t : Int) - (W : Int) < s →
    evolve (t + 30) Y (s + 20) = evolve t Y s

/-- Shift recurrence on the ENTIRE exterior left half-ray (the right input edge). -/
def RightQ (Y : Config) (W t : Nat) : Prop :=
  ∀ s : Int, s < -(t : Int) + (W : Int) →
    evolve (t + 16) Y (s - 16) = evolve t Y s

/-- One 30-step inductive propagation using the proven Rule 110 2/3 barrier. -/
theorem leftQ_step (Y : Config) (W t : Nat)
    (h : LeftQ Y W t) : LeftQ Y W (t + 30) := by
  let p : Int := (e t : Int) + 20 - (W : Int)
  have hA : AgreesRightOf (evolve (t + 30) Y)
      (shift 20 (evolve t Y)) p := by
    intro s hs
    change evolve (t + 30) Y s = evolve t Y (s - 20)
    have hx := h (s - 20) (by dsimp only [p] at hs; omega)
    rw [show s - 20 + 20 = s by omega] at hx
    exact hx
  have hB := global_upper_bound 30
    (evolve (t + 30) Y) (shift 20 (evolve t Y)) p hA
  dsimp only [AgreesRightOf] at hB
  intro s hs
  have he : (e (t + 30) : Int) = (e t : Int) + 20 := e_add30 t
  have hs' : p + (((30 - 30 / 3 : Nat) : Int)) < s + 20 := by
    dsimp [p]
    omega
  have hx := hB (s + 20) hs'
  rw [← evolve_add 30 (t + 30) Y, evolve_shift] at hx
  dsimp only [shift] at hx
  rw [show s + 20 - 20 = s by omega] at hx
  rw [← evolve_add 30 t Y] at hx
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx

/-- One 16-step propagation using the radius-one leftward light cone. -/
theorem rightQ_step (Y : Config) (W t : Nat)
    (h : RightQ Y W t) : RightQ Y W (t + 16) := by
  let q : Int := -(t : Int) - 16 + (W : Int)
  have hA : AgreesLeftOf (evolve (t + 16) Y)
      (shift (-16) (evolve t Y)) q := by
    intro s hs
    change evolve (t + 16) Y s = evolve t Y (s + 16)
    have hx := h (s + 16) (by dsimp only [q] at hs; omega)
    rw [show s + 16 - 16 = s by omega] at hx
    exact hx
  have hB := global_left_cone_bound 16
    (evolve (t + 16) Y) (shift (-16) (evolve t Y)) q hA
  dsimp only [AgreesLeftOf] at hB
  intro s hs
  have hs' : s - 16 < q - (16 : Int) := by
    dsimp [q]
    omega
  have hx := hB (s - 16) hs'
  rw [← evolve_add 16 (t + 16) Y, evolve_shift] at hx
  dsimp only [shift] at hx
  rw [show s - 16 - -16 = s by omega] at hx
  rw [← evolve_add 16 t Y] at hx
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx

/-- An induction covering ALL residue classes modulo 30. -/
theorem leftQ_all (Y : Config) (W : Nat)
    (hBase : ∀ r : Nat, r < 30 → LeftQ Y W (300 + r)) :
    ∀ t : Nat, 300 ≤ t → LeftQ Y W t := by
  intro t ht
  let r := (t - 300) % 30
  let n := (t - 300) / 30
  have hr : r < 30 := by dsimp [r]; omega
  have h0 : LeftQ Y W (300 + r) := hBase r hr
  have hStep : ∀ k : Nat, LeftQ Y W (300 + r + 30 * k) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have hn := leftQ_step Y W (300 + r + 30 * k) ih
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
  have htRep : t = 300 + r + 30 * n := by
    dsimp [r, n]
    omega
  rw [htRep]
  exact hStep n

/-- An induction covering ALL residue classes modulo 16. -/
theorem rightQ_all (Y : Config) (W : Nat)
    (hBase : ∀ r : Nat, r < 16 → RightQ Y W (300 + r)) :
    ∀ t : Nat, 300 ≤ t → RightQ Y W t := by
  intro t ht
  let r := (t - 300) % 16
  let n := (t - 300) / 16
  have hr : r < 16 := by dsimp [r]; omega
  have h0 : RightQ Y W (300 + r) := hBase r hr
  have hStep : ∀ k : Nat, RightQ Y W (300 + r + 16 * k) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have hn := rightQ_step Y W (300 + r + 16 * k) ih
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
  have htRep : t = 300 + r + 16 * n := by
    dsimp [r, n]
    omega
  rw [htRep]
  exact hStep n

/-- A finite tile and the matching background establish the full left base ray. -/
theorem leftQ_of_tile (B : Config) (W t : Nat)
    (bg : ∀ s : Int, evolve (t + 30) B (s + 20) = evolve t B s)
    (tile : ∀ k : Nat, k < W →
      evolve (t + 30) (flipZero B) ((e t : Int) - k + 20) =
        evolve t (flipZero B) ((e t : Int) - k)) :
    LeftQ (flipZero B) W t := by
  intro s hs
  by_cases h : (e t : Int) < s
  · have h0 : AgreesRightOf (flipZero B) B 0 := by
      intro j hj
      simp [flipZero, show j ≠ 0 by omega]
    have hOld := global_upper_bound t (flipZero B) B 0 h0
    have hNew := global_upper_bound (t + 30) (flipZero B) B 0 h0
    have he := e_add30 t
    rw [hNew (s + 20) (by change (0 : Int) + (e (t + 30) : Int) < s + 20; omega),
      hOld s (by change (0 : Int) + (e t : Int) < s; omega)]
    exact bg s
  · let k := ((e t : Int) - s).toNat
    have hk : (e t : Int) - (k : Int) = s := by dsimp [k]; omega
    have hw : k < W := by omega
    simpa only [hk] using tile k hw

/-- A finite tile and the matching background establish the full right base ray. -/
theorem rightQ_of_tile (B : Config) (W t : Nat)
    (bg : ∀ s : Int, evolve (t + 16) B (s - 16) = evolve t B s)
    (tile : ∀ k : Nat, k < W →
      evolve (t + 16) (flipZero B) (-(t : Int) + k - 16) =
        evolve t (flipZero B) (-(t : Int) + k)) :
    RightQ (flipZero B) W t := by
  intro s hs
  by_cases h : s < -(t : Int)
  · have h0 : AgreesLeftOf (flipZero B) B 0 := by
      intro j hj
      simp [flipZero, show j ≠ 0 by omega]
    have hOld := global_left_cone_bound t (flipZero B) B 0 h0
    have hNew := global_left_cone_bound (t + 16) (flipZero B) B 0 h0
    rw [hNew (s - 16) (by omega), hOld s (by omega)]
    exact bg s
  · let k := (s + (t : Int)).toNat
    have hk : -(t : Int) + (k : Int) = s := by dsimp [k]; omega
    have hw : k < W := by omega
    simpa only [hk] using tile k hw

#print axioms leftQ_of_tile
#print axioms rightQ_of_tile
#print axioms leftQ_all
#print axioms rightQ_all

end Rule110Fin1320Bridge
