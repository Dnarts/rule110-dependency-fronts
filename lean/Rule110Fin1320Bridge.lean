import Rule110Complete

/-!
# Fin 1320 ↔ ℤ: the LOCAL bridge, independent of the boundary tables

The ring is indexed with bit i = u_i (not with a reversed bit convention).
`centeredLift` sends ring position 660 to integer position 0.

This module establishes:
1. the precise conjugacy between ring and periodic integer-line evolution;
2. a finite-propagation agreement lemma on ℤ;
3. agreement between a ring defect at bit 660 and a SINGLE defect at 0
   for times t ≤ 380 and output positions |i| ≤ t.

The ring defect is 1320-periodic when lifted. The single-defect comparison
needs a finite horizon; the periodic ring conjugacy itself holds for ALL t.

This module does NOT claim that any externally generated packed table is the
output of this ring evolution. Separate soundness checks are necessary.
-/

namespace Rule110Fin1320Bridge

open Rule110Complete

abbrev Ring := Fin 1320 → Bool

/-- Integer coordinates modulo 1320. -/
def ix (i : Int) : Fin 1320 :=
  ⟨(i % 1320).toNat, by omega⟩

/-- `ix` maps canonical ring indices to themselves. -/
theorem ix_nat (k : Fin 1320) : ix (k.val : Int) = k := by
  apply Fin.ext
  change (((k.val : Int) % 1320).toNat) = k.val
  omega

/-- Modular indexing is compatible with integer translation. -/
theorem ix_translate (i d : Int) :
    ix ((ix i).val + d) = ix (i + d) := by
  apply Fin.ext
  change (((((i % 1320).toNat : Nat) : Int) + d) % 1320).toNat =
    ((i + d) % 1320).toNat
  omega

/-- The ring rule uses the exact left/center/right order of `Rule110Complete.step`. -/
def ringStep (u : Ring) : Ring :=
  fun k =>
    f (u (ix ((k.val : Int) - 1)))
      (u k)
      (u (ix ((k.val : Int) + 1)))

/-- Ring evolution, with the same time convention as `Rule110Complete.evolve`. -/
def ringEvolve : Nat → Ring → Ring
  | 0, u => u
  | t + 1, u => ringStep (ringEvolve t u)

/-- Periodic lifting of a ring state to the whole integer line. -/
def liftRing (u : Ring) : Config := fun i => u (ix i)

/-- All-time exact conjugacy of one ring step with the lifted line step. -/
theorem liftRing_step (u : Ring) :
    liftRing (ringStep u) = step (liftRing u) := by
  funext i
  change f (u (ix (((ix i).val : Int) - 1)))
      (u (ix i))
      (u (ix (((ix i).val : Int) + 1))) =
    f (u (ix (i - 1))) (u (ix i)) (u (ix (i + 1)))
  have hl : ix (((ix i).val : Int) - 1) = ix (i - 1) := by
    simpa only [Int.sub_eq_add_neg] using ix_translate i (-1)
  have hr : ix (((ix i).val : Int) + 1) = ix (i + 1) :=
    ix_translate i 1
  rw [hl, hr]

/-- Periodic ring evolution agrees with integer-line evolution for ALL times. -/
theorem liftRing_evolve (t : Nat) (u : Ring) :
    liftRing (ringEvolve t u) = evolve t (liftRing u) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change liftRing (ringStep (ringEvolve t u)) =
      step (evolve t (liftRing u))
    rw [liftRing_step, ih]

/-- Integer zero is represented by ring coordinate 660. -/
def centeredLift (u : Ring) : Config := fun i => u (ix (i + 660))

theorem centeredLift_evolve (t : Nat) (u : Ring) :
    centeredLift (ringEvolve t u) = evolve t (centeredLift u) := by
  calc
    centeredLift (ringEvolve t u)
        = shift (-660) (liftRing (ringEvolve t u)) := rfl
    _ = shift (-660) (evolve t (liftRing u)) := by
      rw [liftRing_evolve]
    _ = evolve t (shift (-660) (liftRing u)) :=
      (evolve_shift t (-660) (liftRing u)).symm
    _ = evolve t (centeredLift u) := rfl

/-- A single defect at the integer origin. -/
def flipZero (u : Config) : Config :=
  fun i => if i = 0 then !u i else u i

/-- A defect at ring bit 660 (periodically copied when lifted). -/
def flipCenter (u : Ring) : Ring :=
  fun k => if k.val = 660 then !u k else u k

/-- Within ±760 there is only one copy of the ring defect. -/
theorem ix_center_iff (j : Int) (hlo : -760 ≤ j) (hhi : j ≤ 760) :
    (ix (j + 660)).val = 660 ↔ j = 0 := by
  change (((j + 660) % 1320).toNat = 660) ↔ j = 0
  omega

/-- The two different defect initializations agree on every relevant input. -/
theorem flip_agree (u : Ring) (j : Int)
    (hlo : -760 ≤ j) (hhi : j ≤ 760) :
    flipZero (centeredLift u) j = centeredLift (flipCenter u) j := by
  by_cases hj : j = 0
  · subst j
    simp [flipZero, centeredLift, flipCenter, ix] <;> rfl
  · have hn : (ix (j + 660)).val ≠ 660 := by
      intro heq
      exact hj ((ix_center_iff j hlo hhi).mp heq)
    simp [flipZero, centeredLift, flipCenter, hj, hn]

/-- Ordinary radius-one dependence for arbitrary bi-infinite configurations. -/
theorem evolve_agree_window (t : Nat) (u v : Config) (i : Int)
    (h : ∀ j : Int, i - (t : Int) ≤ j → j ≤ i + (t : Int) → u j = v j) :
    evolve t u i = evolve t v i := by
  induction t generalizing i with
  | zero =>
    exact h i (by omega) (by omega)
  | succ t ih =>
    have hm : evolve t u (i - 1) = evolve t v (i - 1) := by
      apply ih (i - 1)
      intro j h1 h2
      apply h j <;> omega
    have hc : evolve t u i = evolve t v i := by
      apply ih i
      intro j h1 h2
      apply h j <;> omega
    have hp : evolve t u (i + 1) = evolve t v (i + 1) := by
      apply ih (i + 1)
      intro j h1 h2
      apply h j <;> omega
    change f (evolve t u (i - 1)) (evolve t u i) (evolve t u (i + 1)) =
      f (evolve t v (i - 1)) (evolve t v i) (evolve t v (i + 1))
    rw [hm, hc, hp]

/-- The EXACT finite-horizon bridge required by the 1320-bit certificate.
The input is an arbitrary ring configuration, not a hard-coded table.
For t ≤ 380, any output position |i| ≤ t sees no other periodic copy
of the original single-bit defect. -/
theorem singleDefect_ring_bridge (u : Ring) (t : Nat) (i : Int)
    (ht : t ≤ 380)
    (hlo : -(t : Int) ≤ i)
    (hhi : i ≤ (t : Int)) :
    evolve t (flipZero (centeredLift u)) i =
      centeredLift (ringEvolve t (flipCenter u)) i := by
  rw [centeredLift_evolve]
  apply evolve_agree_window
  intro j hj1 hj2
  apply flip_agree u j <;> omega

-- The new bridge itself has no computational certificate axioms.
#print axioms singleDefect_ring_bridge

end Rule110Fin1320Bridge
