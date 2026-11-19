/-!
# Formalization of Rule 110 Dependency-Front Theorems (Lean 4)
The supplied Lean 4.35.0 compilation report attests that the four main theorems
compiled without errors and have no `sorryAx` dependencies. This release edits
only this documentation header; the executable declarations and proofs are
unchanged. Recompile this file to verify the updated source.

Contents:
1. Local Rule 110 transition, Zhegalkin (ANF) form, and directional derivatives.
2. Exact 3-step rightward front exclusion over all 128 7-bit neighborhoods (`decide`).
3. **Theorem 1 (`D_t ⊆ [-(t - ⌊t/3⌋), t]`):**
   - `left_dependency_bound`: no site `j < -(t - t / 3)` can affect site `0` at time `t`.
   - `right_dependency_bound`: no site `j > t` can affect site `0` at time `t`.
4. **Theorem 2 (Sharpness of Both Endpoints):**
   - Complete proof of `B6_eq_shift2_B3` and `Y6_eq_shift2_Y3` on all of `ℤ`.
   - Inductive recurrence `Y_{3 + 3k} = σ^{2k} Y_3` for all `k : Nat`.
   - `left_endpoint_essential`: explicit witness pair differing only at `-(t - t / 3)`
     that produces opposite outputs at site `0` at time `t` for every `t : Nat`.
   - `right_endpoint_essential`: explicit witness pair (`0^∞` vs `e_t`) proving `+t ∈ D_t`.
-/

namespace Rule110Complete

/-- Local transition function for Elementary Cellular Automaton Rule 110. -/
def f (l c r : Bool) : Bool :=
  match l, c, r with
  | true,  true,  true  => false
  | true,  true,  false => true
  | true,  false, true  => true
  | true,  false, false => false
  | false, true,  true  => true
  | false, true,  false => true
  | false, false, true  => true
  | false, false, false => false

/-- Algebraic Normal Form (Zhegalkin polynomial): c ⊕ r ⊕ (c ∧ r) ⊕ (l ∧ c ∧ r). -/
def fANF (l c r : Bool) : Bool :=
  xor (xor c r) (xor (c && r) (l && c && r))

theorem f_eq_fANF (l c r : Bool) : f l c r = fANF l c r := by
  cases l <;> cases c <;> cases r <;> rfl

theorem left_sensitivity (c r : Bool) :
    (f true c r != f false c r) = (c && r) := by
  cases c <;> cases r <;> rfl

/-- A bi-infinite binary configuration on `ℤ`. -/
abbrev Config := Int → Bool

/-- Global synchronous Rule 110 update operator on `ℤ`. -/
def step (u : Config) : Config :=
  fun i => f (u (i - 1)) (u i) (u (i + 1))

/-- `t`-fold evolution of Rule 110. -/
def evolve : Nat → Config → Config
  | 0, u => u
  | t + 1, u => step (evolve t u)

/-- Right spatial shift `(σ^d u)(i) = u(i - d)`. -/
def shift (d : Int) (u : Config) : Config :=
  fun i => u (i - d)

theorem evolve_add (s t : Nat) (u : Config) :
    evolve (s + t) u = evolve s (evolve t u) := by
  induction s with
  | zero => simp [evolve]
  | succ s ih =>
    have h : (s + 1) + t = (s + t) + 1 := by omega
    rw [h, evolve, ih, evolve]

theorem step_shift (d : Int) (u : Config) :
    step (shift d u) = shift d (step u) := by
  funext i
  simp only [step, shift]
  have h1 : i - 1 - d = i - d - 1 := by omega
  have h2 : i + 1 - d = i - d + 1 := by omega
  rw [h1, h2]

theorem evolve_shift (t : Nat) (d : Int) (u : Config) :
    evolve t (shift d u) = shift d (evolve t u) := by
  induction t generalizing u with
  | zero => rfl
  | succ t ih =>
    simp only [evolve]
    rw [ih, step_shift]

theorem shift_add (d1 d2 : Int) (u : Config) :
    shift d1 (shift d2 u) = shift (d1 + d2) u := by
  funext i
  simp only [shift]
  have h : i - d1 - d2 = i - (d1 + d2) := by omega
  rw [h]

/-! ## Part 1: Local 3-Step Rightward Exclusion & Theorem 1 (Upper Bound) -/

def stepList : List Bool → List Bool
  | l :: c :: r :: rest => f l c r :: stepList (c :: r :: rest)
  | _ => []

def step3Window (w : List Bool) : Option Bool :=
  (stepList (stepList (stepList w))).head?

def bitOf (n k : Nat) : Bool :=
  ((n >>> k) &&& 1) == 1

def window7 (mask : Nat) : List Bool :=
  List.range 7 |>.map (bitOf mask)

def window7Flip0 (mask : Nat) : List Bool :=
  window7 (mask ^^^ 1)

/-- Kernel-verified exclusion of 3 consecutive rightward advances over all 128 patterns. -/
theorem three_step_right_move_impossible :
    ∀ mask : Fin 128, step3Window (window7 mask.val) = step3Window (window7Flip0 mask.val) := by
  decide

def slice7 (u : Config) (i : Int) : List Bool :=
  [u (i - 3), u (i - 2), u (i - 1), u i, u (i + 1), u (i + 2), u (i + 3)]

theorem evolve3_eq_step3Window (u : Config) (i : Int) :
    step3Window (slice7 u i) = some (evolve 3 u i) := by
  simp only [evolve, step, slice7, step3Window, stepList]
  have h1 : i - 2 - 1 = i - 3 := by omega
  have h2 : i - 2 + 1 = i - 1 := by omega
  have h3 : i - 1 - 1 = i - 2 := by omega
  have h4 : i - 1 + 1 = i := by omega
  have h5 : i + 1 - 1 = i := by omega
  have h6 : i + 1 + 1 = i + 2 := by omega
  have h7 : i + 2 - 1 = i + 1 := by omega
  have h8 : i + 2 + 1 = i + 3 := by omega
  simp only [h1, h2, h3, h4, h5, h6, h7, h8]
  rfl

def encode7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : Fin 128 :=
  let v :=
    (if b0 then 1 else 0) +
    (if b1 then 2 else 0) +
    (if b2 then 4 else 0) +
    (if b3 then 8 else 0) +
    (if b4 then 16 else 0) +
    (if b5 then 32 else 0) +
    (if b6 then 64 else 0)
  ⟨v, by cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide⟩

theorem window7_encode7 (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    window7 (encode7 b0 b1 b2 b3 b4 b5 b6).val = [b0, b1, b2, b3, b4, b5, b6] := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide

theorem window7Flip0_encode7 (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    window7Flip0 (encode7 b0 b1 b2 b3 b4 b5 b6).val = [!b0, b1, b2, b3, b4, b5, b6] := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide

theorem evolve3_eq_of_agree6 (u v : Config) (i : Int)
    (hm2 : u (i - 2) = v (i - 2))
    (hm1 : u (i - 1) = v (i - 1))
    (h0  : u i       = v i)
    (hp1 : u (i + 1) = v (i + 1))
    (hp2 : u (i + 2) = v (i + 2))
    (hp3 : u (i + 3) = v (i + 3)) :
    evolve 3 u i = evolve 3 v i := by
  have hu := evolve3_eq_step3Window u i
  have hv := evolve3_eq_step3Window v i
  suffices hwin : step3Window (slice7 u i) = step3Window (slice7 v i) by
    rw [hu, hv] at hwin
    exact Option.some.inj hwin
  simp only [slice7, hm2, hm1, h0, hp1, hp2, hp3]
  by_cases hm3 : u (i - 3) = v (i - 3)
  · rw [hm3]
  · have hneg : u (i - 3) = !(v (i - 3)) := by
      cases h1 : u (i - 3) <;> cases h2 : v (i - 3) <;> simp_all
    rw [hneg]
    let m := encode7 (v (i - 3)) (v (i - 2)) (v (i - 1)) (v i) (v (i + 1)) (v (i + 2)) (v (i + 3))
    have h_eq1 : [!(v (i - 3)), v (i - 2), v (i - 1), v i, v (i + 1), v (i + 2), v (i + 3)] =
                 window7Flip0 m.val :=
      (window7Flip0_encode7 _ _ _ _ _ _ _).symm
    have h_eq2 : [v (i - 3), v (i - 2), v (i - 1), v i, v (i + 1), v (i + 2), v (i + 3)] =
                 window7 m.val :=
      (window7_encode7 _ _ _ _ _ _ _).symm
    rw [h_eq1, h_eq2]
    exact (three_step_right_move_impossible m).symm

/-- `AgreesRightOf u v p` means `u` and `v` agree strictly to the right of `p`. -/
def AgreesRightOf (u v : Config) (p : Int) : Prop :=
  ∀ i : Int, p < i → u i = v i

/-- `AgreesLeftOf u v q` means `u` and `v` agree strictly to the left of `q`. -/
def AgreesLeftOf (u v : Config) (q : Int) : Prop :=
  ∀ i : Int, i < q → u i = v i

theorem step_agrees_right {u v : Config} {p : Int} (h : AgreesRightOf u v p) :
    AgreesRightOf (step u) (step v) (p + 1) := by
  intro i hi
  simp only [step]
  rw [h (i - 1) (by omega), h i (by omega), h (i + 1) (by omega)]

theorem step_agrees_left {u v : Config} {q : Int} (h : AgreesLeftOf u v q) :
    AgreesLeftOf (step u) (step v) (q - 1) := by
  intro i hi
  simp only [step]
  rw [h (i - 1) (by omega), h i (by omega), h (i + 1) (by omega)]

theorem step3_agrees_right {u v : Config} {p : Int} (h : AgreesRightOf u v p) :
    AgreesRightOf (evolve 3 u) (evolve 3 v) (p + 2) := by
  intro i hi
  exact evolve3_eq_of_agree6 u v i
    (h (i - 2) (by omega))
    (h (i - 1) (by omega))
    (h i       (by omega))
    (h (i + 1) (by omega))
    (h (i + 2) (by omega))
    (h (i + 3) (by omega))

/-- Global upper bound on rightward propagation: `p_t - p_0 ≤ t - ⌊t/3⌋`. -/
theorem global_upper_bound (t : Nat) (u v : Config) (p0 : Int)
    (h0 : AgreesRightOf u v p0) :
    AgreesRightOf (evolve t u) (evolve t v) (p0 + ((t - t / 3 : Nat) : Int)) := by
  induction t using Nat.strongRecOn generalizing u v p0 with
  | ind t ih =>
    match t with
    | 0 => simpa [evolve] using h0
    | 1 =>
      have h1 : AgreesRightOf (evolve 1 u) (evolve 1 v) (p0 + 1) := by
        simpa [evolve] using step_agrees_right h0
      simpa using h1
    | 2 =>
      have h1 : AgreesRightOf (evolve 1 u) (evolve 1 v) (p0 + 1) := by
        simpa [evolve] using step_agrees_right h0
      have h2 : AgreesRightOf (evolve 2 u) (evolve 2 v) ((p0 + 1) + 1) := by
        simpa [evolve] using step_agrees_right h1
      have h_idx : (p0 + 1) + 1 = p0 + ((2 - 2 / 3 : Nat) : Int) := by omega
      rwa [h_idx] at h2
    | t' + 3 =>
      have h3 : AgreesRightOf (evolve 3 u) (evolve 3 v) (p0 + 2) :=
        step3_agrees_right h0
      have h_rec := ih t' (by omega) (evolve 3 u) (evolve 3 v) (p0 + 2) h3
      rw [evolve_add t' 3 u, evolve_add t' 3 v]
      have h_arith : (p0 + 2) + ((t' - t' / 3 : Nat) : Int) =
                     p0 + (((t' + 3) - (t' + 3) / 3 : Nat) : Int) := by omega
      rwa [h_arith] at h_rec

/-- Standard radius-1 light-cone bound on the right: `q_t - q_0 ≥ -t`. -/
theorem global_left_cone_bound (t : Nat) (u v : Config) (q0 : Int)
    (h0 : AgreesLeftOf u v q0) :
    AgreesLeftOf (evolve t u) (evolve t v) (q0 - (t : Int)) := by
  induction t generalizing u v q0 with
  | zero => simpa [evolve] using h0
  | succ t ih =>
    have h1 : AgreesLeftOf (evolve 1 u) (evolve 1 v) (q0 - 1) := by
      simpa [evolve] using step_agrees_left h0
    have h_rec := ih (evolve 1 u) (evolve 1 v) (q0 - 1) h1
    have h_ev : evolve (t + 1) u = evolve t (evolve 1 u) := evolve_add t 1 u
    have h_ev' : evolve (t + 1) v = evolve t (evolve 1 v) := evolve_add t 1 v
    rw [h_ev, h_ev']
    have h_arith : (q0 - 1) - (t : Int) = q0 - ((t + 1 : Nat) : Int) := by omega
    rwa [h_arith] at h_rec

/--
**Theorem 1A (`D_t ⊆ [-(t - ⌊t/3⌋), +∞)`):**
No single-site toggle at `j < -(t - ⌊t/3⌋)` can influence site `0` at time `t`.
-/
theorem left_dependency_bound (t : Nat) (u v : Config) (j : Int)
    (h_agree : AgreesRightOf u v j)
    (hj : j < -((t - t / 3 : Nat) : Int)) :
    evolve t u 0 = evolve t v 0 := by
  exact global_upper_bound t u v j h_agree 0 (by omega)

/--
**Theorem 1B (`D_t ⊆ (-∞, t]`):**
No single-site toggle at `j > t` can influence site `0` at time `t`.
-/
theorem right_dependency_bound (t : Nat) (u v : Config) (j : Int)
    (h_agree : AgreesLeftOf u v j)
    (hj : (t : Int) < j) :
    evolve t u 0 = evolve t v 0 := by
  exact global_left_cone_bound t u v j h_agree 0 (by omega)

/-! ## Part 2: Complete Unconditional Proof of Theorem 2 (Sharpness of Endpoints) -/

/--
Clean 4-periodic background `B_0 = (1011)^∞` defined via Euclidean remainder `i.emod 4`.
Values for `i.emod 4 ∈ {0, 1, 2, 3}` are `true, false, true, true`.
-/
def B0 (i : Int) : Bool :=
  let r := i.emod 4
  r == 0 || r == 2 || r == 3

theorem B0_periodic (i : Int) : B0 (i + 4) = B0 i := by
  have h : (i + 4).emod 4 = i.emod 4 := Int.add_emod_right i 4
  simp only [B0, h]

/-- Period-4 invariance is preserved under `step` and `evolve t`. -/
theorem step_periodic4 {u : Config} (hu : ∀ i, u (i + 4) = u i) (i : Int) :
    step u (i + 4) = step u i := by
  simp only [step]
  have h1 : i + 4 - 1 = (i - 1) + 4 := by omega
  have h2 : i + 4 + 1 = (i + 1) + 4 := by omega
  rw [h1, h2, hu (i - 1), hu i, hu (i + 1)]

theorem evolve_B0_periodic (t : Nat) (i : Int) :
    evolve t B0 (i + 4) = evolve t B0 i := by
  induction t generalizing i with
  | zero => exact B0_periodic i
  | succ t ih => exact step_periodic4 ih i

/-- Any two 4-periodic configurations that agree on `0, 1, 2, 3` agree on all of `ℤ`. -/
theorem periodic4_ext {u v : Config}
    (hu : ∀ i, u (i + 4) = u i)
    (hv : ∀ i, v (i + 4) = v i)
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) :
    ∀ i : Int, u i = v i := by
  have h_nat : ∀ n : Nat, u (n : Int) = v (n : Int) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      match n with
      | 0 => exact h0
      | 1 => exact h1
      | 2 => exact h2
      | 3 => exact h3
      | m + 4 =>
        have hstep : ((m + 4 : Nat) : Int) = (m : Int) + 4 := by omega
        rw [hstep, hu, hv]
        exact ih m (by omega)
  intro i
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact h_nat n
  · -- Shift `i < 0` into `ℕ` by adding `4 * Int.natAbs i`
    let k : Nat := Int.natAbs i
    have hshift : ∀ m : Nat, ∀ x : Int,
        (u (x + 4 * (m : Int)) = v (x + 4 * (m : Int))) ↔ (u x = v x) := by
      intro m x
      induction m generalizing x with
      | zero => simp
      | succ m ihm =>
        have h_eq : x + 4 * ((m + 1 : Nat) : Int) = (x + 4 * (m : Int)) + 4 := by omega
        rw [h_eq, hu, hv]
        exact ihm x
    have hpos : 0 ≤ i + 4 * (k : Int) := by omega
    rw [← hshift k i]
    have h_eq_nat : i + 4 * (k : Int) = ((i + 4 * (k : Int)).toNat : Int) := by omega
    rw [h_eq_nat]
    exact h_nat _

/--
**Complete Unconditional Lemma `B_6 = σ² B_3`:**
Verified on residues `0, 1, 2, 3` by kernel reduction (`decide`) and extended to all `ℤ`.
-/
theorem B6_eq_shift2_B3 : evolve 6 B0 = shift 2 (evolve 3 B0) := by
  funext i
  refine periodic4_ext (evolve_B0_periodic 6) ?_ ?_ ?_ ?_ ?_ i
  · intro x
    simp only [shift]
    have h : x + 4 - 2 = (x - 2) + 4 := by omega
    rw [h, evolve_B0_periodic 3]
  · decide
  · decide
  · decide
  · decide

/-- Perturbed configuration `Y_0 = B_0 ⊕ e_2` differing from `B_0` only at site `2`. -/
def Y0 (i : Int) : Bool :=
  if i == 2 then !(B0 i) else B0 i

/-- Outside `[2 - t, 2 + t]`, `Y_t` coincides with the unperturbed background `B_t`. -/
theorem Y_eq_B_outside (t : Nat) (i : Int)
    (hi : i < 2 - (t : Int) ∨ (2 + (t : Int)) < i) :
    evolve t Y0 i = evolve t B0 i := by
  induction t generalizing i with
  | zero =>
    simp only [evolve, Y0]
    have hne : (i == 2) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp [hne]
  | succ t ih =>
    simp only [evolve, step]
    have h1 : i - 1 < 2 - (t : Int) ∨ (2 + (t : Int)) < i - 1 := by omega
    have h2 : i < 2 - (t : Int)     ∨ (2 + (t : Int)) < i     := by omega
    have h3 : i + 1 < 2 - (t : Int) ∨ (2 + (t : Int)) < i + 1 := by omega
    rw [ih (i - 1) h1, ih i h2, ih (i + 1) h3]

/-- Kernel check of `Y_6 = σ² Y_3` inside the active window `[-4, 10]`. -/
def checkWindowY6EqShift2Y3 : Bool :=
  (List.range 15).all fun idx =>
    let i : Int := (idx : Int) - 4
    evolve 6 Y0 i == shift 2 (evolve 3 Y0) i

theorem Y6_eq_shift2_Y3_window : checkWindowY6EqShift2Y3 = true := by
  decide

/--
**Unconditional Traveling Defect Identity (`Y_6 = σ² Y_3` on all of `ℤ`):**
Combines `decide` on `[-4, 10]` with `Y_eq_B_outside` and `B6_eq_shift2_B3` outside `[-4, 10]`.
-/
theorem Y6_eq_shift2_Y3 : evolve 6 Y0 = shift 2 (evolve 3 Y0) := by
  funext i
  by_cases hwin : -4 ≤ i ∧ i ≤ 10
  · have hmem : (i + 4).toNat ∈ List.range 15 := by
      rw [List.mem_range]
      omega
    have h_all := List.all_eq_true.mp Y6_eq_shift2_Y3_window (i + 4).toNat hmem
    have h_idx : ((i + 4).toNat : Int) - 4 = i := by omega
    rw [h_idx] at h_all
    exact beq_iff_eq.mp h_all
  · -- Outside `[-4, 10]`: both `Y_6(i)` and `(σ² Y_3)(i)` reduce to `B_6(i) = (σ² B_3)(i)`
    have h6 : evolve 6 Y0 i = evolve 6 B0 i :=
      Y_eq_B_outside 6 i (by omega)
    have h3 : shift 2 (evolve 3 Y0) i = shift 2 (evolve 3 B0) i := by
      simp only [shift]
      exact Y_eq_B_outside 3 (i - 2) (by omega)
    rw [h6, h3, B6_eq_shift2_B3]

/--
**Inductive Defect Recurrence (`Y_{3 + 3k} = σ^{2k} Y_3` for all `k : Nat`):**
Unconditional theorem on `ℤ`.
-/
theorem defect_recurrence (k : Nat) :
    evolve (3 + 3 * k) Y0 = shift (2 * (k : Int)) (evolve 3 Y0) := by
  induction k with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, Int.ofNat_zero, Int.mul_zero]
    funext i
    simp [shift]
  | succ k ih =>
    have h_step : 3 + 3 * (k + 1) = 3 + (3 + 3 * k) := by omega
    rw [h_step, evolve_add 3 (3 + 3 * k) Y0, ih, evolve_shift]
    have h_back : evolve 3 (evolve 3 Y0) = evolve 6 Y0 := (evolve_add 3 3 Y0).symm
    rw [h_back, Y6_eq_shift2_Y3, shift_add]
    congr 1

/-- Exact discrepancy at the rightmost front `2 + (t - t / 3)` for every `t : Nat`. -/
theorem traveling_defect_front_diff (t : Nat) :
    evolve t Y0 (2 + ((t - t / 3 : Nat) : Int)) ≠
    evolve t B0 (2 + ((t - t / 3 : Nat) : Int)) := by
  -- Decompose `t` either as `< 3` or as `3 + 3 * k + r` with `r ∈ {0, 1, 2}`
  match t with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | t' + 3 =>
    let k := t' / 3
    let r := t' % 3
    have ht : t' + 3 = r + (3 + 3 * k) := by omega
    have hfront : 2 + (((t' + 3) - (t' + 3) / 3 : Nat) : Int) =
                  (2 + ((3 + r - (3 + r) / 3 : Nat) : Int)) + 2 * (k : Int) := by omega
    rw [hfront, ht, evolve_add r (3 + 3 * k) Y0, evolve_add r (3 + 3 * k) B0, defect_recurrence k]
    -- Also shift background `B_{3 + 3k}` by `2k` via `B6_eq_shift2_B3`
    have hB_rec : evolve (3 + 3 * k) B0 = shift (2 * (k : Int)) (evolve 3 B0) := by
      induction k with
      | zero =>
        simp only [Nat.mul_zero, Nat.add_zero, Int.ofNat_zero, Int.mul_zero]
        funext i; simp [shift]
      | succ k ihk =>
        have hs : 3 + 3 * (k + 1) = 3 + (3 + 3 * k) := by omega
        rw [hs, evolve_add 3 (3 + 3 * k) B0, ihk, evolve_shift]
        have hb : evolve 3 (evolve 3 B0) = evolve 6 B0 := (evolve_add 3 3 B0).symm
        rw [hb, B6_eq_shift2_B3, shift_add]
        congr 1
    rw [hB_rec, evolve_shift, evolve_shift]
    simp only [shift]
    have h_cancel : (2 + ((3 + r - (3 + r) / 3 : Nat) : Int)) + 2 * (k : Int) - 2 * (k : Int) =
                    2 + ((3 + r - (3 + r) / 3 : Nat) : Int) := by omega
    rw [h_cancel, ← evolve_add r 3 Y0, ← evolve_add r 3 B0]
    -- `r ∈ {0, 1, 2}`, verified directly by `decide`
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr with h | h | h <;> rw [h] <;> decide

/--
**Theorem 2A (Left Endpoint Sharpness: `-(t - ⌊t/3⌋) ∈ D_t` for all `t : Nat`):**
Shifting `(B_0, Y_0)` spatially puts the single initial bit flip at `j = -(t - ⌊t/3⌋)`
and produces opposite outputs at site `0` after `t` steps.
-/
theorem left_endpoint_essential (t : Nat) :
    let d : Int := -(2 + ((t - t / 3 : Nat) : Int))
    let u : Config := shift d B0
    let v : Config := shift d Y0
    (∀ i : Int, i ≠ -((t - t / 3 : Nat) : Int) → u i = v i) ∧
    (evolve t u 0 ≠ evolve t v 0) := by
  intro d u v
  constructor
  · intro i hi
    simp only [u, v, shift, Y0]
    have hne : (i - d == 2) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp [hne]
  · simp only [u, v, evolve_shift, shift]
    have h0 : 0 - d = 2 + ((t - t / 3 : Nat) : Int) := by omega
    rw [h0]
    exact Ne.symm (traveling_defect_front_diff t)

/--
**Theorem 2B (Right Endpoint Sharpness: `+t ∈ D_t` for all `t : Nat`):**
Comparing the all-zero configuration `0^∞` against a lone `1` at site `+(t : Int)`
yields opposite values at site `0` after `t` steps.
-/
def zeroCfg : Config := fun _ => false

def loneOneAt (a : Int) : Config := fun i => i == a

theorem evolve_zero (t : Nat) : evolve t zeroCfg = zeroCfg := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [evolve, ih]
    funext i
    rfl

theorem loneOne_leftmost_one (a : Int) (t : Nat) :
    (∀ i : Int, i < a - (t : Int) → evolve t (loneOneAt a) i = false) ∧
    (evolve t (loneOneAt a) (a - (t : Int)) = true) := by
  induction t with
  | zero =>
    constructor
    · intro i hi
      simp only [evolve, loneOneAt]
      exact beq_eq_false_iff_ne.mpr (by omega)
    · simp [evolve, loneOneAt]
  | succ t ih =>
    obtain ⟨h_left, h_front⟩ := ih
    constructor
    · intro i hi
      simp only [evolve, step]
      rw [h_left (i - 1) (by omega), h_left i (by omega), h_left (i + 1) (by omega)]
      rfl
    · simp only [evolve, step]
      have h1 : a - ((t + 1 : Nat) : Int) - 1 < a - (t : Int) := by omega
      have h2 : a - ((t + 1 : Nat) : Int) < a - (t : Int) := by omega
      have h3 : a - ((t + 1 : Nat) : Int) + 1 = a - (t : Int) := by omega
      rw [h_left _ h1, h_left _ h2, h3, h_front]
      rfl

theorem right_endpoint_essential (t : Nat) :
    let u : Config := zeroCfg
    let v : Config := loneOneAt (t : Int)
    (∀ i : Int, i ≠ (t : Int) → u i = v i) ∧
    (evolve t u 0 ≠ evolve t v 0) := by
  intro u v
  constructor
  · intro i hi
    simp only [u, v, zeroCfg, loneOneAt]
    exact (beq_eq_false_iff_ne.mpr hi).symm
  · rw [evolve_zero]
    have h_front := (loneOne_leftmost_one (t : Int) t).2
    have h0 : (t : Int) - (t : Int) = 0 := by omega
    rw [h0] at h_front
    simp [v, zeroCfg, h_front]

end Rule110Complete


-- Proof-kernel audit; review output after a successful lean build.
#print axioms Rule110Complete.left_dependency_bound
#print axioms Rule110Complete.right_dependency_bound
#print axioms Rule110Complete.left_endpoint_essential
#print axioms Rule110Complete.right_endpoint_essential
