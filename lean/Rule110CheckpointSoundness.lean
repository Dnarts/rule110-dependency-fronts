import Rule110BitVecBridge
import Rule110HalfRayClosure

namespace Rule110KernelCert

open Rule110Complete Rule110Fin1320Bridge

private theorem packed_bit (positions : List Nat) (read : Nat → Bool) (acc k : Nat) :
    (positions.foldl (fun a j => if read j then a ||| (1 <<< j) else a) acc).testBit k =
      (acc.testBit k || (positions.contains k && read k)) := by
  induction positions generalizing acc with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons, ih]
    have hmask : ((1 : Nat) <<< j).testBit k = decide (j = k) := by
      simp [Nat.shiftLeft_eq, Nat.testBit_two_pow]
    by_cases he : j = k
    · subst j
      cases read k <;> simp [hmask]
    · cases read j <;> simp [hmask, he, Ne.symm he]

theorem extractDown_bit (u : RingBV) (hi w k : Nat) (hk : k < w) :
    (extractDown u hi w).testBit k = u.getLsbD (hi - k) := by
  unfold extractDown
  rw [packed_bit]
  simp [List.mem_range, hk]

theorem extractUp_bit (u : RingBV) (lo w k : Nat) (hk : k < w) :
    (extractUp u lo w).testBit k = u.getLsbD (lo + k) := by
  unfold extractUp
  rw [packed_bit]
  simp [List.mem_range, hk]

def background (u : RingBV) : Config := centeredLift (toFinRing u)

theorem background_rotL20 (u : RingBV) (s : Int) :
    background (rotL 20 u) (s + 20) = background u s := by
  let i := ix (s + 20 + 660)
  have hi := i.isLt
  have hh : ix ((i.val : Int) - 20) = ix (s + 660) := by
    dsimp only [i]
    rw [Int.sub_eq_add_neg, ix_translate]
    congr 1
    omega
  change (rotL 20 u).getLsbD i.val = u.getLsbD (ix (s + 660)).val
  rw [← hh]
  have hr : rotL 20 u = u.rotateLeft 20 := rfl
  rw [hr, BitVec.getLsbD_rotateLeft_of_le (by decide : 20 < 1320)]
  by_cases h : i.val < 20
  · have hj : (ix ((i.val : Int) - 20)).val = 1300 + i.val := by
      change (((i.val : Int) - 20) % 1320).toNat = _
      omega
    simp only [ite_eq_left h, hj]
  · have hj : (ix ((i.val : Int) - 20)).val = i.val - 20 := by
      change (((i.val : Int) - 20) % 1320).toNat = _
      omega
    simp only [ite_eq_right h, hj, hi, decide_true, Bool.true_and]

theorem background_rotR16 (u : RingBV) (s : Int) :
    background (rotR 16 u) (s - 16) = background u s := by
  let i := ix (s - 16 + 660)
  have hi := i.isLt
  have hh : ix ((i.val : Int) + 16) = ix (s + 660) := by
    dsimp only [i]
    rw [ix_translate]
    congr 1
    omega
  change (rotR 16 u).getLsbD i.val = u.getLsbD (ix (s + 660)).val
  rw [← hh]
  have hr : rotR 16 u = u.rotateRight 16 := rfl
  rw [hr, BitVec.getLsbD_rotateRight_of_lt (by decide : 16 < 1320)]
  by_cases h : i.val < 1304
  · have hj : (ix ((i.val : Int) + 16)).val = 16 + i.val := by
      change (((i.val : Int) + 16) % 1320).toNat = _
      omega
    simp only [ite_eq_left h, hj]
  · have hj : (ix ((i.val : Int) + 16)).val = i.val - 1304 := by
      change (((i.val : Int) + 16) % 1320).toNat = _
      omega
    simp only [ite_eq_right h, hj, hi, decide_true, Bool.true_and]

theorem background_at_bit (u : RingBV) (s : Int)
    (hlo : -660 ≤ s) (hhi : s < 660) :
    background u s = u.getLsbD (s + 660).toNat := by
  change u.getLsbD (((s + 660) % 1320).toNat) = _
  congr 2
  omega

theorem evolve_bg (u : RingBV) (t : Nat) : evolve t (background u) = background (ringEvolveBV t u) :=
  (centeredLift_evolveBV t u).symm

theorem evolve_defect (u : RingBV) (t : Nat) (s : Int)
    (ht : t ≤ 380) (hlo : -(t : Int) ≤ s) (hhi : s ≤ (t : Int)) :
    evolve t (flipZero (background u)) s = background (ringEvolveBV t (flipCenterBV u)) s :=
  singleDefect_BV_bridge u t s ht hlo hhi

def leftPos (t k : Nat) : Int := (e t : Int) - k
def rightPos (t k : Nat) : Int := -(t : Int) + k

theorem left_bit_index (t k : Nat) (hk : k ≤ 660 + edgeNat t) :
    (leftPos t k + 660).toNat = 660 + edgeNat t - k := by
  unfold leftPos
  change ((edgeNat t : Int) - (k : Int) + 660).toNat = _
  omega

theorem right_bit_index (t k : Nat) (ht : t ≤ 660) :
    (rightPos t k + 660).toNat = 660 - t + k := by
  unfold rightPos
  omega

theorem xor_true_ne (a b : Bool) (h : (a ^^ b) = true) : a ≠ b := by
  cases a <;> cases b <;> simp_all

def BgShift (B : Config) (t dt : Nat) (d : Int) : Prop :=
  ∀ s : Int, evolve (t + dt) B (s + d) = evolve t B s

theorem bgShift_after (B : Config) (t dt : Nat) (d : Int)
    (h : BgShift B t dt d) (n : Nat) : BgShift B (n + t) dt d := by
  have eq₀ : evolve (t + dt) B = shift d (evolve t B) := by
    funext s
    have hs := h (s - d)
    rw [show s - d + d = s by omega] at hs
    exact hs
  intro s
  rw [show n + t + dt = n + (t + dt) by omega,
    evolve_add, eq₀, evolve_shift, evolve_add]
  change evolve n (evolve t B) (s + d - d) = _
  rw [show s + d - d = s by omega]

theorem leftBg_from_row (u b b' : RingBV) (t : Nat)
    (hb : ringEvolveBV t u = b) (hb' : ringEvolveBV (t + 30) u = b')
    (hs : b' = rotL 20 b) : BgShift (background u) t 30 20 := by
  intro s
  rw [evolve_bg, evolve_bg, hb, hb', hs]
  exact background_rotL20 b s

theorem rightBg_from_row (u b b' : RingBV) (t : Nat)
    (hb : ringEvolveBV t u = b) (hb' : ringEvolveBV (t + 16) u = b')
    (hs : b' = rotR 16 b) : BgShift (background u) t 16 (-16) := by
  intro s
  change evolve (t + 16) (background u) (s - 16) = _
  rw [evolve_bg, evolve_bg, hb, hb', hs]
  exact background_rotR16 b s

theorem leftQ_from_row (u y y' : RingBV) (t : Nat)
    (ht : 300 ≤ t) (ht' : t < 330)
    (bg : BgShift (background u) t 30 20)
    (hy : ringEvolveBV t (flipCenterBV u) = y)
    (hy' : ringEvolveBV (t + 30) (flipCenterBV u) = y')
    (tile : extractDown y (660 + edgeNat t) 167 =
      extractDown y' (660 + edgeNat (t + 30)) 167) :
    LeftQ (flipZero (background u)) 167 t := by
  apply leftQ_of_tile _ _ _ bg
  intro k hk
  have hp : (e t : Int) - k + 20 = leftPos (t + 30) k := by
    unfold leftPos
    rw [e_add30]
    omega
  change evolve (t + 30) (flipZero (background u)) ((e t : Int) - k + 20) =
    evolve t (flipZero (background u)) (leftPos t k)
  rw [hp]
  have small₀ : -(t : Int) ≤ leftPos t k ∧ leftPos t k ≤ t := by
    unfold leftPos e
    omega
  have small₁ : -((t + 30 : Nat) : Int) ≤ leftPos (t + 30) k ∧
      leftPos (t + 30) k ≤ (t + 30 : Nat) := by
    unfold leftPos e
    omega
  rw [evolve_defect _ _ _ (by omega) small₀.1 small₀.2, hy,
    evolve_defect _ _ _ (by omega) small₁.1 small₁.2, hy',
    background_at_bit _ _ (by omega) (by omega), background_at_bit _ _ (by omega) (by omega),
    left_bit_index _ _ (by omega), left_bit_index _ _ (by omega)]
  have h := congrArg (fun x : Nat => x.testBit k) tile
  rw [extractDown_bit _ _ _ _ hk, extractDown_bit _ _ _ _ hk] at h
  exact h.symm

theorem rightQ_from_row (u y y' : RingBV) (t : Nat)
    (ht : 300 ≤ t) (ht' : t < 316)
    (bg : BgShift (background u) t 16 (-16))
    (hy : ringEvolveBV t (flipCenterBV u) = y)
    (hy' : ringEvolveBV (t + 16) (flipCenterBV u) = y')
    (tile : extractUp y (660 - t) 20 = extractUp y' (660 - (t + 16)) 20) :
    RightQ (flipZero (background u)) 20 t := by
  apply rightQ_of_tile _ _ _ bg
  intro k hk
  have hp : -(t : Int) + k - 16 = rightPos (t + 16) k := by
    unfold rightPos
    omega
  change evolve (t + 16) (flipZero (background u)) (-(t : Int) + k - 16) =
    evolve t (flipZero (background u)) (rightPos t k)
  rw [hp]
  have small₀ : -(t : Int) ≤ rightPos t k ∧ rightPos t k ≤ t := by
    unfold rightPos
    omega
  have small₁ : -((t + 16 : Nat) : Int) ≤ rightPos (t + 16) k ∧
      rightPos (t + 16) k ≤ (t + 16 : Nat) := by
    unfold rightPos
    omega
  rw [evolve_defect _ _ _ (by omega) small₀.1 small₀.2, hy,
    evolve_defect _ _ _ (by omega) small₁.1 small₁.2, hy',
    background_at_bit _ _ (by omega) (by omega), background_at_bit _ _ (by omega) (by omega),
    right_bit_index _ _ (by omega), right_bit_index _ _ (by omega)]
  have h := congrArg (fun x : Nat => x.testBit k) tile
  rw [extractUp_bit _ _ _ _ hk, extractUp_bit _ _ _ _ hk] at h
  exact h.symm

def Differs (u : RingBV) (t : Nat) (s : Int) : Prop :=
  evolve t (background u) s ≠ evolve t (flipZero (background u)) s

theorem leftDiff_from_row (u b y : RingBV) (t k : Nat)
    (ht : 300 ≤ t) (ht' : t < 330) (hk : k < 106)
    (hb : ringEvolveBV t u = b)
    (hy : ringEvolveBV t (flipCenterBV u) = y)
    (bit : (extractDown (b ^^^ y) (660 + edgeNat t) 106).testBit k = true) :
    Differs u t (leftPos t k) := by
  have small : -(t : Int) ≤ leftPos t k ∧ leftPos t k ≤ t := by
    unfold leftPos e
    omega
  unfold Differs
  rw [evolve_bg, hb, evolve_defect _ _ _ (by omega) small.1 small.2, hy,
    background_at_bit _ _ (by omega) (by omega), background_at_bit _ _ (by omega) (by omega),
    left_bit_index _ _ (by omega)]
  rw [extractDown_bit _ _ _ _ hk, BitVec.getLsbD_xor] at bit
  exact xor_true_ne _ _ bit

theorem rightDiff_from_row (u b y : RingBV) (t k : Nat)
    (ht : 300 ≤ t) (ht' : t < 316) (hk : k < 20)
    (hb : ringEvolveBV t u = b)
    (hy : ringEvolveBV t (flipCenterBV u) = y)
    (bit : (extractUp (b ^^^ y) (660 - t) 20).testBit k = true) :
    Differs u t (rightPos t k) := by
  have small : -(t : Int) ≤ rightPos t k ∧ rightPos t k ≤ t := by
    unfold rightPos
    omega
  unfold Differs
  rw [evolve_bg, hb, evolve_defect _ _ _ (by omega) small.1 small.2, hy,
    background_at_bit _ _ (by omega) (by omega), background_at_bit _ _ (by omega) (by omega),
    right_bit_index _ _ (by omega)]
  rw [extractUp_bit _ _ _ _ hk, BitVec.getLsbD_xor] at bit
  exact xor_true_ne _ _ bit

theorem leftDiff_step (u : RingBV) (t k : Nat) (hk : k < 106)
    (bg : BgShift (background u) t 30 20)
    (ray : LeftQ (flipZero (background u)) 167 t)
    (h : Differs u t (leftPos t k)) : Differs u (t + 30) (leftPos (t + 30) k) := by
  have hp : leftPos (t + 30) k = leftPos t k + 20 := by
    unfold leftPos
    rw [e_add30]
    omega
  unfold Differs
  rw [hp, bg, ray _ (by unfold leftPos; omega)]
  exact h

theorem rightDiff_step (u : RingBV) (t k : Nat) (hk : k < 20)
    (bg : BgShift (background u) t 16 (-16))
    (ray : RightQ (flipZero (background u)) 20 t)
    (h : Differs u t (rightPos t k)) : Differs u (t + 16) (rightPos (t + 16) k) := by
  have hp : rightPos (t + 16) k = rightPos t k - 16 := by
    unfold rightPos
    omega
  unfold Differs
  rw [hp, show rightPos t k - 16 = rightPos t k + -16 by omega, bg]
  rw [show rightPos t k + -16 = rightPos t k - 16 by omega, ray _ (by unfold rightPos; omega)]
  exact h

/-- A site is essential if changing only that input bit can change the output at zero. -/
def EssentialAt (t : Nat) (j : Int) : Prop :=
  ∃ u v : Config, (∀ i : Int, i ≠ j → u i = v i) ∧ evolve t u 0 ≠ evolve t v 0

theorem essential_of_differs (u : RingBV) (t : Nat) (s : Int) (h : Differs u t s) :
    EssentialAt t (-s) := by
  refine ⟨shift (-s) (background u), shift (-s) (flipZero (background u)), ?_, ?_⟩
  · intro i hi
    simp [shift, flipZero, show i + s ≠ 0 by omega]
  · rw [evolve_shift, evolve_shift]
    simp only [shift, Int.zero_sub, Int.neg_neg]
    exact h

/-- A witness carries the difference forward by one period at each strip depth. -/
def Repeats (pos : Nat → Nat → Int) (width period : Nat) (u : RingBV) : Prop :=
  ∀ t k : Nat, 300 ≤ t → k < width →
    Differs u t (pos t k) → Differs u (t + period) (pos (t + period) k)

theorem leftRepeats_of_base (u : RingBV)
    (bg : BgShift (background u) 300 30 20)
    (ray : ∀ r : Nat, r < 30 → LeftQ (flipZero (background u)) 167 (300 + r)) :
    Repeats leftPos 106 30 u := by
  intro t k ht hk hd
  apply leftDiff_step u t k hk _ (leftQ_all _ _ ray t ht) hd
  have h := bgShift_after _ _ _ _ bg (t - 300)
  rwa [show t - 300 + 300 = t by omega] at h

theorem rightRepeats_of_base (u : RingBV)
    (bg : BgShift (background u) 300 16 (-16))
    (ray : ∀ r : Nat, r < 16 → RightQ (flipZero (background u)) 20 (300 + r)) :
    Repeats rightPos 20 16 u := by
  intro t k ht hk hd
  apply rightDiff_step u t k hk _ (rightQ_all _ _ ray t ht) hd
  have h := bgShift_after _ _ _ _ bg (t - 300)
  rwa [show t - 300 + 300 = t by omega] at h

theorem strip_all (pos : Nat → Nat → Int) (width period : Nat) (hp : 0 < period)
    (base : ∀ r k : Nat, r < period → k < width →
      ∃ u : RingBV, Repeats pos width period u ∧ Differs u (300 + r) (pos (300 + r) k))
    (t k : Nat) (ht : 300 ≤ t) (hk : k < width) :
    EssentialAt t (-pos t k) := by
  let r := (t - 300) % period
  obtain ⟨u, hu, h0⟩ := base r k (Nat.mod_lt _ hp) hk
  have hStep (n : Nat) :
      Differs u (300 + r + period * n) (pos (300 + r + period * n) k) := by
    induction n with
    | zero => simpa only [Nat.mul_zero, Nat.add_zero] using h0
    | succ n ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact hu _ _ (by omega) hk ih
  have hd := Nat.mod_add_div (t - 300) period
  have hrep : 300 + r + period * ((t - 300) / period) = t := by
    dsimp only [r]
    omega
  have h := hStep ((t - 300) / period)
  rw [hrep] at h
  exact essential_of_differs u t (pos t k) h

end Rule110KernelCert
