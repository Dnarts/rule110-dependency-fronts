import MergeMinimality4
import ContinuousSubject110

/-!
# Exact merger threshold for a fixed raw sensor and local context

This bridge combines the supplied lower-bound and four-history modules. It
identifies their Boolean rules and opposite iteration conventions explicitly,
then translates the witness input at coordinate 5 to coordinate 0.

`Protocol T` matches the observation class in the continuation paper: two
environments, one varying initial bit, complete merger within each environment,
one common raw sensor before merger, and a context bit in one common cell at
merger. A decoder uses both bits, and neither bit alone decodes all four inputs.
No claim is made about adaptive sensors or autonomous reinitialization.
-/

namespace MergeThreshold

abbrev Grid := MergeMinimality4.Grid

/-- The two supplied modules implement the same Boolean Rule 110. -/
theorem rule_agrees (l c r : Bool) :
    MergeMinimality4.rule110 l c r = ContinuousSubject110.rule110 l c r := by
  cases l <;> cases c <;> cases r <;> rfl

theorem step_agrees (g : Grid) :
    MergeMinimality4.step g = ContinuousSubject110.step g := by
  funext x
  exact rule_agrees _ _ _

theorem evolve_step (n : Nat) (g : Grid) :
    MergeMinimality4.evolve n (MergeMinimality4.step g) =
      MergeMinimality4.step (MergeMinimality4.evolve n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change MergeMinimality4.step (MergeMinimality4.evolve n (MergeMinimality4.step g)) =
      MergeMinimality4.step (MergeMinimality4.step (MergeMinimality4.evolve n g))
    rw [ih]

/-- Align outer-step recursion with the witness module's inner-step recursion. -/
theorem evolve_agrees (n : Nat) (g : Grid) :
    MergeMinimality4.evolve n g = ContinuousSubject110.evolve n g := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    calc
      MergeMinimality4.evolve (n + 1) g =
          MergeMinimality4.evolve n (MergeMinimality4.step g) := (evolve_step n g).symm
      _ = ContinuousSubject110.evolve n (MergeMinimality4.step g) := ih _
      _ = ContinuousSubject110.evolve n (ContinuousSubject110.step g) := by
        rw [step_agrees]
      _ = ContinuousSubject110.evolve (n + 1) g := rfl

theorem evolve_add (a b : Nat) (g : Grid) :
    MergeMinimality4.evolve (a + b) g =
      MergeMinimality4.evolve a (MergeMinimality4.evolve b g) := by
  induction a with
  | zero => simp [MergeMinimality4.evolve]
  | succ a ih =>
    have h : (a + 1) + b = (a + b) + 1 := by omega
    rw [h]
    change MergeMinimality4.step (MergeMinimality4.evolve (a + b) g) =
      MergeMinimality4.step (MergeMinimality4.evolve a (MergeMinimality4.evolve b g))
    rw [ih]

theorem merger_persists (T U : Nat) (hTU : T ≤ U) (g : Grid)
    (hm : ∀ x, MergeMinimality4.evolve T (MergeMinimality4.setAt0 g false) x =
      MergeMinimality4.evolve T (MergeMinimality4.setAt0 g true) x) :
    ∀ x, MergeMinimality4.evolve U (MergeMinimality4.setAt0 g false) x =
      MergeMinimality4.evolve U (MergeMinimality4.setAt0 g true) x := by
  intro x
  have htime : U = (U - T) + T := by omega
  rw [htime, evolve_add, evolve_add, funext hm]

/-- The allowed observation class; the sensor coordinates do not depend on k or y. -/
structure Protocol (T : Nat) where
  environment : Bool → Grid
  sensorTime : Nat
  sensorPosition : Int
  contextPosition : Int
  decode : Bool → Bool → Bool
  before : sensorTime < T
  merged : ∀ k x,
    MergeMinimality4.evolve T (MergeMinimality4.setAt0 (environment k) false) x =
      MergeMinimality4.evolve T (MergeMinimality4.setAt0 (environment k) true) x
  context : ∀ k y,
    MergeMinimality4.evolve T (MergeMinimality4.setAt0 (environment k) y)
      contextPosition = k
  decodes : ∀ k y,
    decode k (MergeMinimality4.evolve sensorTime
      (MergeMinimality4.setAt0 (environment k) y) sensorPosition) = y
  no_sensor_only : ¬ ∃ d : Bool → Bool, ∀ k y,
    d (MergeMinimality4.evolve sensorTime
      (MergeMinimality4.setAt0 (environment k) y) sensorPosition) = y
  no_context_only : ¬ ∃ d : Bool → Bool, ∀ k y, d k = y

/-- The fixed sensor must distinguish the two target values in each environment. -/
theorem sensor_sensitive {T : Nat} (p : Protocol T) (k : Bool) :
    MergeMinimality4.evolve p.sensorTime
      (MergeMinimality4.setAt0 (p.environment k) false) p.sensorPosition ≠
    MergeMinimality4.evolve p.sensorTime
      (MergeMinimality4.setAt0 (p.environment k) true) p.sensorPosition := by
  intro heq
  have h := congrArg (p.decode k) heq
  rw [p.decodes k false, p.decodes k true] at h
  cases h

/-- Merger at T ≤ 3 would make the context unnecessary. -/
theorem protocol_time_ge_four {T : Nat} (p : Protocol T) : 4 ≤ T := by
  by_cases hT : 4 ≤ T
  · exact hT
  · have hm0 := merger_persists T 3 (by omega) (p.environment false) (p.merged false)
    have hm1 := merger_persists T 3 (by omega) (p.environment true) (p.merged true)
    obtain ⟨d, hd⟩ := MergeMinimality4.no_joint_necessity_at_merge3
      (p.environment false) (p.environment true) hm0 hm1 p.sensorTime
      (by have := p.before; omega) p.sensorPosition (sensor_sensitive p false)
    apply False.elim
    apply p.no_sensor_only
    refine ⟨d, ?_⟩
    intro k y
    cases k
    · exact (hd y).1
    · exact (hd y).2

/-- Translate the original coordinate 5 to the normalized coordinate 0. -/
def shifted (g : Grid) : Grid := fun x => g (x + 5)

theorem evolve_shifted (n : Nat) (g : Grid) (x : Int) :
    MergeMinimality4.evolve n (shifted g) x =
      MergeMinimality4.evolve n g (x + 5) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change MergeMinimality4.rule110
      (MergeMinimality4.evolve n (shifted g) (x - 1))
      (MergeMinimality4.evolve n (shifted g) x)
      (MergeMinimality4.evolve n (shifted g) (x + 1)) =
      MergeMinimality4.rule110
      (MergeMinimality4.evolve n g (x + 5 - 1))
      (MergeMinimality4.evolve n g (x + 5))
      (MergeMinimality4.evolve n g (x + 5 + 1))
    rw [ih (x - 1), ih x, ih (x + 1)]
    have hL : (x - 1) + 5 = x + 5 - 1 := by omega
    have hR : (x + 1) + 5 = x + 5 + 1 := by omega
    rw [hL, hR]

def witnessEnvironment (k : Bool) : Grid :=
  shifted (ContinuousSubject110.witnessFor k false).initial

theorem witness_words_agree_away (k : Bool) (i : Int) (hi : i ≠ 5) :
    (ContinuousSubject110.witnessFor k false).initial i =
      (ContinuousSubject110.witnessFor k true).initial i := by
  cases k
  · change ContinuousSubject110.w00 i = ContinuousSubject110.w01 i
    by_cases heq : ContinuousSubject110.w00 i = ContinuousSubject110.w01 i
    · exact heq
    · exact False.elim (hi ((ContinuousSubject110.initial_diff_only_at_five i).1.mp heq))
  · change ContinuousSubject110.w10 i = ContinuousSubject110.w11 i
    by_cases heq : ContinuousSubject110.w10 i = ContinuousSubject110.w11 i
    · exact heq
    · exact False.elim (hi ((ContinuousSubject110.initial_diff_only_at_five i).2.mp heq))

theorem witness_history_eq (k y : Bool) :
    MergeMinimality4.setAt0 (witnessEnvironment k) y =
      shifted (ContinuousSubject110.witnessFor k y).initial := by
  funext i
  by_cases hi : i = 0
  · subst i
    cases k <;> cases y <;> decide
  · simp only [MergeMinimality4.setAt0, hi, ite_false, witnessEnvironment, shifted]
    cases y
    · rfl
    · exact witness_words_agree_away k (i + 5) (by omega)

/-- Both the coordinate change and the evolution convention are accounted for. -/
theorem witness_evolution (n : Nat) (k y : Bool) (x : Int) :
    MergeMinimality4.evolve n (MergeMinimality4.setAt0 (witnessEnvironment k) y) x =
      ContinuousSubject110.evolve n (ContinuousSubject110.witnessFor k y).initial (x + 5) := by
  rw [witness_history_eq, evolve_shifted, evolve_agrees]

theorem witness_sensor (k y : Bool) :
    MergeMinimality4.evolve 2 (MergeMinimality4.setAt0 (witnessEnvironment k) y) (-2) =
      xor k y := by
  rw [witness_evolution]
  cases k <;> cases y <;> decide

/-- A concrete admissible protocol, constructed from the supplied four histories. -/
def witnessProtocol : Protocol 4 where
  environment := witnessEnvironment
  sensorTime := 2
  sensorPosition := -2
  contextPosition := -5
  decode := xor
  before := by decide
  merged := by
    intro k x
    rw [witness_evolution, witness_evolution]
    cases k
    · exact ContinuousSubject110.merge_K0 (x + 5)
    · exact ContinuousSubject110.merge_K1 (x + 5)
  context := by
    intro k y
    rw [witness_evolution]
    cases k <;> cases y <;> decide
  decodes := by
    intro k y
    rw [witness_sensor]
    cases k <;> cases y <;> rfl
  no_sensor_only := by
    rintro ⟨d, hd⟩
    have h0 := hd false false
    have h1 := hd true true
    rw [witness_sensor] at h0 h1
    change d false = false at h0
    change d false = true at h1
    cases h0.symm.trans h1
  no_context_only := by
    rintro ⟨d, hd⟩
    have h0 := hd false false
    have h1 := hd false true
    cases h0.symm.trans h1

theorem protocol_at_four : Nonempty (Protocol 4) := ⟨witnessProtocol⟩

/-- Exact threshold: four is attainable, and no admissible protocol merges earlier. -/
theorem four_is_least :
    Nonempty (Protocol 4) ∧ ∀ T : Nat, Nonempty (Protocol T) → 4 ≤ T := by
  refine ⟨protocol_at_four, ?_⟩
  intro T hp
  rcases hp with ⟨p⟩
  exact protocol_time_ge_four p

#print axioms protocol_at_four
#print axioms protocol_time_ge_four
#print axioms four_is_least

end MergeThreshold
