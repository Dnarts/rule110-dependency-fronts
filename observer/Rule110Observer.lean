import Rule110Exact
import Rule110FrontGlue

/-!
# Finite-horizon observation in Rule 110

A fixed list of lattice sites is read at every time from zero through the
deadline. A predictor receives this history and must give the target bit on
every admissible initial configuration.
-/

namespace Rule110Observer
open Rule110Complete

/-- Exact set of essential initial sites for site `x` at time `t`. -/
def InCone (t : Nat) (x j : Int) : Prop :=
  x - ((t - t / 3 : Nat) : Int) ≤ j ∧ j ≤ x + (t : Int)

theorem evolve_eq_of_agree_on_cone {t : Nat} {x : Int} {u v : Config}
    (agree : ∀ j, InCone t x j → u j = v j) :
    evolve t u x = evolve t v x := by
  let lo := x - ((t - t / 3 : Nat) : Int)
  let w := Rule110FrontGlue.splice (lo - 1) v u
  have right : AgreesRightOf u w (lo - 1) := by
    intro j hj
    simp [w, Rule110FrontGlue.splice, show ¬j ≤ lo - 1 by omega]
  have left : AgreesLeftOf w v (x + (t : Int) + 1) := by
    intro j hj
    by_cases h : j ≤ lo - 1
    · simp [w, Rule110FrontGlue.splice, h]
    · have inside : InCone t x j := by
        unfold InCone
        dsimp [lo] at h
        omega
      simpa [w, Rule110FrontGlue.splice, h] using agree j inside
  exact (global_upper_bound t u w (lo - 1) right x (by dsimp [lo]; omega)).trans
    (global_left_cone_bound t w v (x + (t : Int) + 1) left x (by omega))

/-- Translate the exact dependency theorem from the origin to any site. -/
theorem essential_iff_inCone (t : Nat) (x j : Int) :
    (∃ u v : Config, (∀ i, i ≠ j → u i = v i) ∧ evolve t u x ≠ evolve t v x) ↔
      InCone t x j := by
  constructor
  · rintro ⟨u, v, agree, differs⟩
    apply Classical.byContradiction
    intro outside
    exact differs (evolve_eq_of_agree_on_cone fun i hi =>
      agree i fun eq => outside (eq ▸ hi))
  · intro inside
    obtain ⟨u, v, agree, differs⟩ := (Rails.essential_iff t (j - x)).mpr (by
      unfold InCone at inside
      omega)
    refine ⟨shift x u, shift x v, ?_, ?_⟩
    · intro i hi
      exact agree (i - x) (by omega)
    · simpa only [evolve_shift, shift, Int.sub_self] using differs

abbrev History (sites : List Int) (deadline : Nat) :=
  Fin (deadline + 1) → Fin sites.length → Bool

def history (sites : List Int) (deadline : Nat) (u : Config) : History sites deadline :=
  fun s p => evolve s.val u (sites.get p)

def CanPredict (sites : List Int) (deadline t : Nat) (x : Int)
    (admissible : Config → Prop := fun _ => True) : Prop :=
  ∃ decode : History sites deadline → Bool,
    ∀ u, admissible u → decode (history sites deadline u) = evolve t u x

/-- Exact prediction is possible precisely when each attainable history has one target bit. -/
theorem canPredict_iff {sites : List Int} {deadline t : Nat} {x : Int}
    {admissible : Config → Prop} :
    CanPredict sites deadline t x admissible ↔
      ∀ u v, admissible u → admissible v → history sites deadline u = history sites deadline v →
        evolve t u x = evolve t v x := by
  constructor
  · rintro ⟨decode, correct⟩ u v hu hv same
    rw [← correct u hu, same, correct v hv]
  · intro consistent
    classical
    refine ⟨fun h => if ∃ u, admissible u ∧ history sites deadline u = h ∧ evolve t u x = true
      then true else false, ?_⟩
    intro u hu
    dsimp only
    split
    · rename_i witness
      obtain ⟨v, hv, same, bit⟩ := witness
      exact bit.symm.trans (consistent v u hv hu same)
    · rename_i absent
      cases bit : evolve t u x with
      | false => rfl
      | true => exact False.elim (absent ⟨u, hu, rfl, bit⟩)

theorem not_canPredict_iff {sites : List Int} {deadline t : Nat} {x : Int}
    {admissible : Config → Prop} :
    ¬CanPredict sites deadline t x admissible ↔
      ∃ u v, admissible u ∧ admissible v ∧ history sites deadline u = history sites deadline v ∧
        evolve t u x ≠ evolve t v x := by
  constructor
  · intro impossible
    apply Classical.byContradiction
    intro noPair
    apply impossible
    apply canPredict_iff.mpr
    intro u v hu hv same
    apply Classical.byContradiction
    intro differs
    exact noPair ⟨u, v, hu, hv, same, differs⟩
  · rintro ⟨u, v, hu, hv, same, differs⟩ possible
    exact differs (canPredict_iff.mp possible u v hu hv same)

/-- The union of the exact cones of all reads through the deadline. -/
def InObservedPast (sites : List Int) (deadline : Nat) (j : Int) : Prop :=
  ∃ (s : Fin (deadline + 1)) (p : Fin sites.length), InCone s.val (sites.get p) j

def CoversTarget (sites : List Int) (deadline t : Nat) (x : Int) : Prop :=
  ∀ j, InCone t x j → InObservedPast sites deadline j

theorem inObservedPast_iff_last {sites : List Int} {deadline : Nat} {j : Int} :
    InObservedPast sites deadline j ↔ ∃ p : Fin sites.length, InCone deadline (sites.get p) j := by
  constructor
  · rintro ⟨s, p, inside⟩
    have hs := s.isLt
    refine ⟨p, ?_⟩
    unfold InCone at inside ⊢
    omega
  · rintro ⟨p, inside⟩
    exact ⟨⟨deadline, Nat.lt_succ_self deadline⟩, p, inside⟩

theorem history_eq_of_agree_on_observed_past {sites : List Int} {deadline : Nat} {u v : Config}
    (agree : ∀ j, InObservedPast sites deadline j → u j = v j) :
    history sites deadline u = history sites deadline v := by
  funext s p
  exact evolve_eq_of_agree_on_cone fun j hj => agree j ⟨s, p, hj⟩

/-- An uncovered essential site supplies a pair differing only at that site. -/
theorem indistinguishable_of_missing_site {sites : List Int} {deadline t : Nat} {x j : Int}
    (essential : InCone t x j) (missing : ¬InObservedPast sites deadline j) :
    ∃ u v : Config, (∀ i, i ≠ j → u i = v i) ∧
      history sites deadline u = history sites deadline v ∧ evolve t u x ≠ evolve t v x := by
  obtain ⟨u, v, agree, differs⟩ := (essential_iff_inCone t x j).mpr essential
  refine ⟨u, v, agree, history_eq_of_agree_on_observed_past ?_, differs⟩
  intro i hi
  exact agree i fun eq => missing (eq ▸ hi)

theorem coversTarget_of_canPredict {sites : List Int} {deadline t : Nat} {x : Int}
    (possible : CanPredict sites deadline t x) : CoversTarget sites deadline t x := by
  intro j hj
  apply Classical.byContradiction
  intro missing
  obtain ⟨u, v, _, same, differs⟩ := indistinguishable_of_missing_site hj missing
  exact differs (canPredict_iff.mp possible u v trivial trivial same)

/-! ## Sufficiency at a deadline and minimal horizons -/

/-- The deadline row suffices when it contains the exact cone for the remaining steps. -/
theorem canPredict_of_last_row_covers {sites : List Int} {deadline remaining : Nat} {x : Int}
    (covered : ∀ j, InCone remaining x j → j ∈ sites) :
    CanPredict sites deadline (remaining + deadline) x := by
  apply canPredict_iff.mpr
  intro u v _ _ same
  rw [evolve_add, evolve_add]
  apply evolve_eq_of_agree_on_cone
  intro j hj
  obtain ⟨p, hp⟩ := List.get_of_mem (covered j hj)
  have read := congrFun (congrFun same ⟨deadline, Nat.lt_succ_self deadline⟩) p
  change evolve deadline u (sites.get p) = evolve deadline v (sites.get p) at read
  rwa [hp] at read

/-- At deadline zero, coverage gives the initial bit itself at each essential site. -/
theorem canPredict_at_zero_of_covers {sites : List Int} {t : Nat} {x : Int}
    (covered : CoversTarget sites 0 t x) : CanPredict sites 0 t x := by
  apply canPredict_of_last_row_covers (remaining := t)
  intro j hj
  obtain ⟨p, inside⟩ := inObservedPast_iff_last.mp (covered j hj)
  unfold InCone at inside
  have hp : sites.get p = j := by omega
  exact hp ▸ List.get_mem sites p

private theorem covered_endpoints {sites : List Int} {deadline t : Nat} {x : Int}
    (covered : CoversTarget sites deadline t x) :
    ∃ l r : Fin sites.length,
      InCone deadline (sites.get l) (x - ((t - t / 3 : Nat) : Int)) ∧
      InCone deadline (sites.get r) (x + (t : Int)) := by
  obtain ⟨l, left⟩ := inObservedPast_iff_last.mp
    (covered (x - ((t - t / 3 : Nat) : Int)) (by unfold InCone; omega))
  obtain ⟨r, right⟩ := inObservedPast_iff_last.mp
    (covered (x + (t : Int)) (by unfold InCone; omega))
  exact ⟨l, r, left, right⟩

/-- Covering a strictly future target requires at least two distinct read sites. -/
theorem two_sites_of_covers_strict_future {sites : List Int} {deadline t : Nat} {x : Int}
    (future : deadline < t) (covered : CoversTarget sites deadline t x) :
    ∃ l r : Fin sites.length, sites.get l < sites.get r := by
  obtain ⟨l, r, left, right⟩ := covered_endpoints covered
  unfold InCone at left right
  exact ⟨l, r, by omega⟩

/-- For a contiguous read region and a time-2 target, coverage supplies every
    parent of the target in the last read row. -/
theorem canPredict_at_two_of_contiguous_cover {sites : List Int} {x : Int}
    (contiguous : ∀ {a b i : Int}, a ∈ sites → b ∈ sites → a ≤ i → i ≤ b → i ∈ sites)
    (covered : CoversTarget sites 1 2 x) : CanPredict sites 1 2 x := by
  obtain ⟨l, r, left, right⟩ := covered_endpoints covered
  unfold InCone at left right
  apply canPredict_of_last_row_covers (remaining := 1)
  intro i inside
  unfold InCone at inside
  exact contiguous (List.get_mem sites l) (List.get_mem sites r) (by omega) (by omega)

/-! ## Counterexamples with full causal coverage -/

/-- Read sites −1 and 1 at times 0 and 1. Both histories are `10, 10`. -/
theorem separated_cells_counterexample :
    CoversTarget [-1, 1] 1 2 0 ∧
      ∃ u v : Config, (∀ j, j ≠ 0 → u j = v j) ∧
        history [-1, 1] 1 u = history [-1, 1] 1 v ∧
        history [-1, 1] 1 u = (fun _ p => p.val == 0) ∧
        evolve 2 u 0 = false ∧ evolve 2 v 0 = true := by
  constructor
  · intro j inside
    unfold InCone at inside
    apply inObservedPast_iff_last.mpr
    by_cases h : j ≤ 0
    · refine ⟨⟨0, by decide⟩, ?_⟩
      change -2 ≤ j ∧ j ≤ 0
      omega
    · refine ⟨⟨1, by decide⟩, ?_⟩
      change 0 ≤ j ∧ j ≤ 2
      omega
  · refine ⟨fun j => j == -1, fun j => j == -1 || j == 0, ?_, ?_, ?_, by decide, by decide⟩
    · intro j hj
      simp [hj]
    · funext s p
      revert s p
      decide +kernel
    · funext s p
      revert s p
      decide +kernel

/-- Read adjacent sites 0 and 1 through time 2. Both histories are `00, 01, 11`. -/
theorem adjacent_cells_counterexample :
    CoversTarget [0, 1] 2 3 0 ∧
      ∃ u v : Config, (∀ j, j ≠ -1 → u j = v j) ∧
        history [0, 1] 2 u = history [0, 1] 2 v ∧
        history [0, 1] 2 u = (fun s p => decide (2 ≤ s.val + p.val)) ∧
        evolve 3 u 0 = true ∧ evolve 3 v 0 = false := by
  constructor
  · intro j inside
    unfold InCone at inside
    apply inObservedPast_iff_last.mpr
    by_cases h : j ≤ 2
    · refine ⟨⟨0, by decide⟩, ?_⟩
      change -2 ≤ j ∧ j ≤ 2
      omega
    · refine ⟨⟨1, by decide⟩, ?_⟩
      change -1 ≤ j ∧ j ≤ 3
      omega
  · refine ⟨fun j => j == 2, fun j => j == 2 || j == -1, ?_, ?_, ?_, by decide, by decide⟩
    · intro j hj
      simp [hj]
    · funext s p
      revert s p
      decide +kernel
    · funext s p
      revert s p
      decide +kernel

theorem coverage_does_not_suffice :
    CoversTarget [-1, 1] 1 2 0 ∧ ¬CanPredict [-1, 1] 1 2 0 := by
  obtain ⟨covered, u, v, _, same, _, zero, one⟩ := separated_cells_counterexample
  exact ⟨covered, not_canPredict_iff.mpr ⟨u, v, trivial, trivial, same, by simp [zero, one]⟩⟩

#print axioms canPredict_iff
#print axioms not_canPredict_iff
#print axioms indistinguishable_of_missing_site
#print axioms coversTarget_of_canPredict
#print axioms canPredict_of_last_row_covers
#print axioms canPredict_at_zero_of_covers
#print axioms two_sites_of_covers_strict_future
#print axioms canPredict_at_two_of_contiguous_cover
#print axioms separated_cells_counterexample
#print axioms adjacent_cells_counterexample
#print axioms coverage_does_not_suffice

end Rule110Observer
