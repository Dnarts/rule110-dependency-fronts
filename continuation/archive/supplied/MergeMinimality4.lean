/-!
# MergeMinimality4.lean

Машинно-проверяемое доказательство (чистое ядро Lean 4, без Mathlib, без `sorry`,
без `native_decide` и без `Classical.choice`) **минимальности такта 4 для полного
слияния** с совместной необходимостью $(K, Z)$ в клеточном автомате Rule 110
(закрывает оставшуюся часть строки §7 препринта `110 OBSERVER` / `causal_crosscheck.py`):

1. **Точная классификация всех $2^{12} = 4096$ окружений (`merges3Strip_iff`, `merges3_count_eq_8`):**
   полное слияние к такту 3 при изолированном перевороте клетки `0` происходит ровно на 8
   окружениях из 4096 — в точности на шаблоне `*10111[Y]1000**` на интервале `[-6, 6]`.
2. **Глобальный критерий слияния на всей бесконечной прямой (`global_merge3_iff_pattern`):**
   для любой конфигурации `g : Int → Bool` слияние `evolve 3 (setAt0 g false)` и
   `evolve 3 (setAt0 g true)` на всей прямой `ℤ` эквивалентно этому 9-битному шаблону.
3. **Невозможность противоположных ориентаций датчика до слияния (`no_opposite_orientations_at_merge3`):**
   для любых двух сливающихся к такту 3 миров `g0, g1 : Grid`, любого момента `τ < 3` и
   любой позиции `s : Int` чувствительный в обоих мирах датчик имеет **одинаковую**
   ориентацию реакции на переворот `Y`.
4. **Отсутствие совместной необходимости $(K, Z)$ на такте 3 (`no_joint_necessity_at_merge3`):**
   для любых двух сливающихся к такту 3 миров и любого чувствительного датчика `(τ, s)` (`τ < 3`)
   существует декодер `decZ : Bool → Bool`, восстанавливающий `Y` по одному только `Z`
   (без участия контекста `K`), что опровергает совместную необходимость $(K, Z)$ и доказывает
   минимальность такта 4.
-/

set_option synthInstance.maxSize 8192
set_option maxRecDepth 262144
set_option maxHeartbeats 2000000
namespace MergeMinimality4

/-- Локальное правило Rule 110: `f(l, c, r) = (c ∨ r) ⊕ (l ∧ c ∧ r)`. -/
def rule110 (l c r : Bool) : Bool :=
  (c || r) != (l && c && r)

/-- Конфигурация бесконечной решётки `ℤ`. -/
abbrev Grid := Int → Bool

/-- Один синхронный шаг эволюции Rule 110 на `ℤ`. -/
def step (g : Grid) : Grid :=
  fun i => rule110 (g (i - 1)) (g i) (g (i + 1))

/-- `t` шагов эволюции Rule 110 на `ℤ`. -/
def evolve : Nat → Grid → Grid
  | 0,     g => g
  | t + 1, g => step (evolve t g)

/-- Подстановка бита `y` в позицию `0` при сохранении всего окружения `g`. -/
def setAt0 (g : Grid) (y : Bool) : Grid :=
  fun i => if i = 0 then y else g i

-- ============================================================================
-- 1. ЛОКАЛЬНОСТЬ СВЕТОВОГО КОНУСА НА `ℤ`
-- ============================================================================

/-- Локальность эволюции: значение `evolve t g x` зависит только от `[x - t, x + t]`. -/
theorem evolve_cone (t : Nat) (g1 g2 : Grid) (x : Int)
    (h : ∀ i : Int, x - (t : Int) ≤ i ∧ i ≤ x + (t : Int) → g1 i = g2 i) :
    evolve t g1 x = evolve t g2 x := by
  induction t generalizing x with
  | zero =>
    exact h x (by constructor <;> omega)
  | succ t ih =>
    unfold evolve step
    have hL : evolve t g1 (x - 1) = evolve t g2 (x - 1) :=
      ih (x - 1) (fun i hi => h i (by constructor <;> omega))
    have hC : evolve t g1 x = evolve t g2 x :=
      ih x (fun i hi => h i (by constructor <;> omega))
    have hR : evolve t g1 (x + 1) = evolve t g2 (x + 1) :=
      ih (x + 1) (fun i hi => h i (by constructor <;> omega))
    rw [hL, hC, hR]

/-- Вне светового конуса `[-t, t]` переворот клетки `0` не влияет на `evolve t`. -/
theorem setAt0_outside_cone (t : Nat) (g : Grid) (x : Int)
    (hout : x < -(t : Int) ∨ (t : Int) < x) :
    evolve t (setAt0 g false) x = evolve t (setAt0 g true) x := by
  apply evolve_cone
  intro i hi
  unfold setAt0
  have hne : i ≠ 0 := by omega
  rw [ite_eq_right hne, ite_eq_right hne]

-- ============================================================================
-- 2. ЧИСТО БУЛЕВА 3-ТАКТНАЯ ЭВОЛЮЦИЯ 13-БИТНОГО ОКНА `[-6..6]`
-- ============================================================================

/-- 3-тактный выход на 7 позициях `[-3..3]` по 13-битному входу `[-6..6]`. -/
def evolve3Bits (l0 l1 l2 l3 l4 l5 y r0 r1 r2 r3 r4 r5 : Bool) :
    Bool × Bool × Bool × Bool × Bool × Bool × Bool :=
  -- такт 1: позиции [-5..5] (11 бит)
  let a0  := rule110 l0 l1 l2
  let a1  := rule110 l1 l2 l3
  let a2  := rule110 l2 l3 l4
  let a3  := rule110 l3 l4 l5
  let a4  := rule110 l4 l5 y
  let a5  := rule110 l5 y  r0
  let a6  := rule110 y  r0 r1
  let a7  := rule110 r0 r1 r2
  let a8  := rule110 r1 r2 r3
  let a9  := rule110 r2 r3 r4
  let a10 := rule110 r3 r4 r5
  -- такт 2: позиции [-4..4] (9 бит)
  let b0 := rule110 a0 a1 a2
  let b1 := rule110 a1 a2 a3
  let b2 := rule110 a2 a3 a4
  let b3 := rule110 a3 a4 a5
  let b4 := rule110 a4 a5 a6
  let b5 := rule110 a5 a6 a7
  let b6 := rule110 a6 a7 a8
  let b7 := rule110 a7 a8 a9
  let b8 := rule110 a8 a9 a10
  -- такт 3: позиции [-3..3] (7 бит)
  ( rule110 b0 b1 b2,
    rule110 b1 b2 b3,
    rule110 b2 b3 b4,
    rule110 b3 b4 b5,
    rule110 b4 b5 b6,
    rule110 b5 b6 b7,
    rule110 b6 b7 b8 )

/-- Предикат слияния двух траекторий (`y = false` и `y = true`) на всех 7 клетках `[-3..3]` к такту 3. -/
def merges3Strip (l0 l1 l2 l3 l4 l5 r0 r1 r2 r3 r4 r5 : Bool) : Bool :=
  evolve3Bits l0 l1 l2 l3 l4 l5 false r0 r1 r2 r3 r4 r5 ==
  evolve3Bits l0 l1 l2 l3 l4 l5 true  r0 r1 r2 r3 r4 r5

/-- Теорема 1 (исчерпывающая классификация всех $2^{12} = 4096$ окружений):
    слияние к такту 3 происходит в точности на 9-битном шаблоне `*10111[Y]1000**`. -/
theorem merges3Strip_iff :
    ∀ l0 l1 l2 l3 l4 l5 r0 r1 r2 r3 r4 r5 : Bool,
      merges3Strip l0 l1 l2 l3 l4 l5 r0 r1 r2 r3 r4 r5 = true ↔
      (l1 = true ∧ l2 = false ∧ l3 = true ∧ l4 = true ∧ l5 = true ∧
       r0 = true ∧ r1 = false ∧ r2 = false ∧ r3 = false) := by
  decide

/-- Явный подсчёт числа сливающихся окружений среди всех 4096: ровно 8. -/
def countMerging3 : Nat :=
  let bs : List Bool := [false, true]
  bs.foldl (fun acc0 l0 =>
  bs.foldl (fun acc1 l1 =>
  bs.foldl (fun acc2 l2 =>
  bs.foldl (fun acc3 l3 =>
  bs.foldl (fun acc4 l4 =>
  bs.foldl (fun acc5 l5 =>
  bs.foldl (fun acc6 r0 =>
  bs.foldl (fun acc7 r1 =>
  bs.foldl (fun acc8 r2 =>
  bs.foldl (fun acc9 r3 =>
  bs.foldl (fun acc10 r4 =>
  bs.foldl (fun acc11 r5 =>
    if merges3Strip l0 l1 l2 l3 l4 l5 r0 r1 r2 r3 r4 r5 then acc11 + 1 else acc11
  ) acc10) acc9) acc8) acc7) acc6) acc5) acc4) acc3) acc2) acc1) acc0) 0

theorem merges3_count_eq_8 : countMerging3 = 8 := by
  decide

/-- Мост: 7 центральных клеток глобальной эволюции `evolve 3 (setAt0 g y)` тождественно
    равны кортежу `evolve3Bits` на `g (-6) .. g 6`. -/
theorem evolve3_eq_evolve3Bits (g : Grid) (y : Bool) :
    ( evolve 3 (setAt0 g y) (-3),
      evolve 3 (setAt0 g y) (-2),
      evolve 3 (setAt0 g y) (-1),
      evolve 3 (setAt0 g y) 0,
      evolve 3 (setAt0 g y) 1,
      evolve 3 (setAt0 g y) 2,
      evolve 3 (setAt0 g y) 3 ) =
    evolve3Bits (g (-6)) (g (-5)) (g (-4)) (g (-3)) (g (-2)) (g (-1)) y
                (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) := by
  rfl

/-- Условие 9-битного шаблона `*10111[Y]1000**` на бесконечной решётке `g : Grid`. -/
def Merge3Pattern (g : Grid) : Prop :=
  g (-5) = true ∧ g (-4) = false ∧ g (-3) = true ∧ g (-2) = true ∧ g (-1) = true ∧
  g 1 = true ∧ g 2 = false ∧ g 3 = false ∧ g 4 = false

private theorem outside_of_not_inside {lo hi i : Int} (h : ¬(lo ≤ i ∧ i ≤ hi)) :
    i < lo ∨ hi < i := by
  rcases Int.lt_or_le i lo with lt | le
  · exact .inl lt
  · exact .inr (Int.lt_of_not_ge (fun upper => h ⟨le, upper⟩))

/-- Теорема 2 (глобальный критерий полного слияния к такту 3 на всей прямой `ℤ`). -/
theorem global_merge3_iff_pattern (g : Grid) :
    (∀ x : Int, evolve 3 (setAt0 g false) x = evolve 3 (setAt0 g true) x) ↔
    Merge3Pattern g := by
  constructor
  · intro hall
    have htup :
        evolve3Bits (g (-6)) (g (-5)) (g (-4)) (g (-3)) (g (-2)) (g (-1)) false
                    (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) =
        evolve3Bits (g (-6)) (g (-5)) (g (-4)) (g (-3)) (g (-2)) (g (-1)) true
                    (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) := by
      rw [← evolve3_eq_evolve3Bits g false, ← evolve3_eq_evolve3Bits g true]
      rw [hall (-3), hall (-2), hall (-1), hall 0, hall 1, hall 2, hall 3]
    have hm : merges3Strip (g (-6)) (g (-5)) (g (-4)) (g (-3)) (g (-2)) (g (-1))
                           (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) = true := by
      unfold merges3Strip
      exact beq_iff_eq.mpr htup
    exact (merges3Strip_iff _ _ _ _ _ _ _ _ _ _ _ _).mp hm
  · intro hpat x
    rcases Decidable.em (-3 ≤ x ∧ x ≤ 3) with hin | hin
    · have hm : merges3Strip (g (-6)) (g (-5)) (g (-4)) (g (-3)) (g (-2)) (g (-1))
                             (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) = true :=
        (merges3Strip_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr hpat
      have htup :
          ( evolve 3 (setAt0 g false) (-3), evolve 3 (setAt0 g false) (-2),
            evolve 3 (setAt0 g false) (-1), evolve 3 (setAt0 g false) 0,
            evolve 3 (setAt0 g false) 1,    evolve 3 (setAt0 g false) 2,
            evolve 3 (setAt0 g false) 3 ) =
          ( evolve 3 (setAt0 g true) (-3),  evolve 3 (setAt0 g true) (-2),
            evolve 3 (setAt0 g true) (-1),  evolve 3 (setAt0 g true) 0,
            evolve 3 (setAt0 g true) 1,     evolve 3 (setAt0 g true) 2,
            evolve 3 (setAt0 g true) 3 ) := by
        rw [evolve3_eq_evolve3Bits, evolve3_eq_evolve3Bits]
        exact beq_iff_eq.mp hm
      have hcases : x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact congrArg Prod.fst htup
      · exact congrArg (fun p => p.2.1) htup
      · exact congrArg (fun p => p.2.2.1) htup
      · exact congrArg (fun p => p.2.2.2.1) htup
      · exact congrArg (fun p => p.2.2.2.2.1) htup
      · exact congrArg (fun p => p.2.2.2.2.2.1) htup
      · exact congrArg (fun p => p.2.2.2.2.2.2) htup
    · have hout := outside_of_not_inside hin
      exact setAt0_outside_cone 3 g x hout

-- ============================================================================
-- 3. ОДИНАКОВАЯ ОРИЕНТАЦИЯ ДАТЧИКА И НЕВОЗМОЖНОСТЬ СОВМЕСТНОЙ НЕОБХОДИМОСТИ
-- ============================================================================

/-- Для любых двух сливающихся к такту 3 миров `g0, g1` их начальные конфигурации
    совпадают на всём интервале `[-4, 4]` (после подстановки одного и того же `y` в `0`). -/
theorem merging_worlds_agree_on_m4_4 (g0 g1 : Grid)
    (hm0 : ∀ x : Int, evolve 3 (setAt0 g0 false) x = evolve 3 (setAt0 g0 true) x)
    (hm1 : ∀ x : Int, evolve 3 (setAt0 g1 false) x = evolve 3 (setAt0 g1 true) x)
    (y : Bool) (i : Int) (hi : -4 ≤ i ∧ i ≤ 4) :
    setAt0 g0 y i = setAt0 g1 y i := by
  have hp0 := (global_merge3_iff_pattern g0).mp hm0
  have hp1 := (global_merge3_iff_pattern g1).mp hm1
  rcases hp0 with ⟨_, h0m4, h0m3, h0m2, h0m1, h01, h02, h03, h04⟩
  rcases hp1 with ⟨_, h1m4, h1m3, h1m2, h1m1, h11, h12, h13, h14⟩
  have hcases : i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [setAt0, h0m4, h0m3, h0m2, h0m1, h01, h02, h03, h04,
                  h1m4, h1m3, h1m2, h1m1, h11, h12, h13, h14]

/-- Теорема 3 (инвариантность показания датчика до слияния):
    для любых двух сливающихся к такту 3 миров `g0, g1`, любого времени `τ < 3` и
    любой позиции `s` внутри конуса `[-τ, τ]` показание датчика полностью совпадает
    в обоих мирах при каждом `y ∈ {false, true}`. -/
theorem same_sensor_on_merging_worlds (g0 g1 : Grid)
    (hm0 : ∀ x : Int, evolve 3 (setAt0 g0 false) x = evolve 3 (setAt0 g0 true) x)
    (hm1 : ∀ x : Int, evolve 3 (setAt0 g1 false) x = evolve 3 (setAt0 g1 true) x)
    (τ : Nat) (hτ : τ < 3) (s : Int) (hs : -(τ : Int) ≤ s ∧ s ≤ (τ : Int)) (y : Bool) :
    evolve τ (setAt0 g0 y) s = evolve τ (setAt0 g1 y) s := by
  apply evolve_cone
  intro i hi
  apply merging_worlds_agree_on_m4_4 g0 g1 hm0 hm1 y i
  constructor <;> omega

/-- Теорема 4 (одинаковая ориентация любого чувствительного датчика при `τ < 3`):
    если датчик `(τ, s)` чувствителен в обоих сливающихся к такту 3 мирах `g0, g1`,
    то его реакция на `y = false` и `y = true` в `g0` и `g1` тождественно совпадает. -/
theorem no_opposite_orientations_at_merge3 (g0 g1 : Grid)
    (hm0 : ∀ x : Int, evolve 3 (setAt0 g0 false) x = evolve 3 (setAt0 g0 true) x)
    (hm1 : ∀ x : Int, evolve 3 (setAt0 g1 false) x = evolve 3 (setAt0 g1 true) x)
    (τ : Nat) (hτ : τ < 3) (s : Int)
    (hsens0 : evolve τ (setAt0 g0 false) s ≠ evolve τ (setAt0 g0 true) s) :
    evolve τ (setAt0 g0 false) s = evolve τ (setAt0 g1 false) s ∧
    evolve τ (setAt0 g0 true) s  = evolve τ (setAt0 g1 true) s := by
  have hs : -(τ : Int) ≤ s ∧ s ≤ (τ : Int) := by
    rcases Decidable.em (-(τ : Int) ≤ s ∧ s ≤ (τ : Int)) with h | h
    · exact h
    · exact False.elim (hsens0 (setAt0_outside_cone τ g0 s (outside_of_not_inside h)))
  exact ⟨same_sensor_on_merging_worlds g0 g1 hm0 hm1 τ hτ s hs false,
         same_sensor_on_merging_worlds g0 g1 hm0 hm1 τ hτ s hs true⟩

/-- Теорема 5 (главная теорема — минимальность такта 4):
    для любых двух сливающихся к такту 3 миров `g0, g1` и любого фиксированного датчика
    `(τ, s)` (`τ < 3`), чувствительного в `g0`, существует одноаргументный декодер
    `decZ : Bool → Bool`, восстанавливающий `Y` по одному только `Z` в обоих мирах сразу
    (контекст `K` избыточен; совместная необходимость `(K, Z)` невозможна при слиянии к такту 3). -/
theorem no_joint_necessity_at_merge3 (g0 g1 : Grid)
    (hm0 : ∀ x : Int, evolve 3 (setAt0 g0 false) x = evolve 3 (setAt0 g0 true) x)
    (hm1 : ∀ x : Int, evolve 3 (setAt0 g1 false) x = evolve 3 (setAt0 g1 true) x)
    (τ : Nat) (hτ : τ < 3) (s : Int)
    (hsens0 : evolve τ (setAt0 g0 false) s ≠ evolve τ (setAt0 g0 true) s) :
    ∃ decZ : Bool → Bool,
      ∀ y : Bool,
        decZ (evolve τ (setAt0 g0 y) s) = y ∧
        decZ (evolve τ (setAt0 g1 y) s) = y := by
  have hsame := no_opposite_orientations_at_merge3 g0 g1 hm0 hm1 τ hτ s hsens0
  let z0 := evolve τ (setAt0 g0 false) s
  let z1 := evolve τ (setAt0 g0 true) s
  refine ⟨fun z => if z = z0 then false else true, ?_⟩
  intro y
  cases y
  · constructor
    · simp [z0]
    · rw [← hsame.1]; simp [z0]
  · have hne : z1 ≠ z0 := hsens0.symm
    constructor
    · change (if z1 = z0 then false else true) = true
      rw [ite_eq_right hne]
    · rw [← hsame.2]
      change (if z1 = z0 then false else true) = true
      rw [ite_eq_right hne]

#print axioms outside_of_not_inside
#print axioms evolve3_eq_evolve3Bits
#print axioms merging_worlds_agree_on_m4_4
#print axioms evolve_cone
#print axioms setAt0_outside_cone
#print axioms merges3Strip_iff
#print axioms merges3_count_eq_8
#print axioms global_merge3_iff_pattern
#print axioms same_sensor_on_merging_worlds
#print axioms no_opposite_orientations_at_merge3
#print axioms no_joint_necessity_at_merge3

end MergeMinimality4
