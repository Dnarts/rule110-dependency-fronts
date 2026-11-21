/-!
# Rule110ChiralSeam.lean

Машинно-проверяемое доказательство (чистое ядро Lean 4, без Mathlib, без `sorry`
и без `native_decide`), закрывающее как конечные сертификаты, так и глобальную
математическую индукцию на бесконечной решётке `Config := Int → Bool`.
-/

namespace Rule110ChiralSeam

/-- Локальное правило Rule 110: `f(l, c, r) = (c ∨ r) ⊕ (l ∧ c ∧ r)`. -/
def rule110 (l c r : Bool) : Bool :=
  (c || r) != (l && c && r)

/-- Зеркальный двойник Rule 124: инверсия хиральности `(l, c, r) ↦ (r, c, l)`. -/
def rule124 (l c r : Bool) : Bool :=
  rule110 r c l

/-- Линейное правило Rule 90: `l ⊕ r`. -/
def rule90 (l _c r : Bool) : Bool :=
  l != r

-- ============================================================================
-- 1. ТРЁХТАКТНАЯ ХИРАЛЬНОСТЬ (ГОРИЗОНТ 3 ТАКТОВ, 2^7 = 128 СЛОВ)
-- ============================================================================

/-- 3-тактный выход центрального узла на 7-битном слове. -/
def step3 (rule : Bool → Bool → Bool → Bool)
    (x0 x1 x2 x3 x4 x5 x6 : Bool) : Bool :=
  let a1 := rule x0 x1 x2
  let a2 := rule x1 x2 x3
  let a3 := rule x2 x3 x4
  let a4 := rule x3 x4 x5
  let a5 := rule x4 x5 x6
  let b1 := rule a1 a2 a3
  let b2 := rule a2 a3 a4
  let b3 := rule a3 a4 a5
  rule b1 b2 b3

/-- Rule 110: выход `step3` не зависит от левой крайней координаты `x0` (3-тактная граница v_R ≤ 2/3). -/
theorem rule110_right_exclusion :
    ∀ x0 x1 x2 x3 x4 x5 x6 : Bool,
      step3 rule110 x0 x1 x2 x3 x4 x5 x6 = step3 rule110 (!x0) x1 x2 x3 x4 x5 x6 := by
  decide

/-- Rule 110: правая крайняя координата `x6` влияет на выход `step3`. -/
theorem rule110_no_left_exclusion :
    ∃ x0 x1 x2 x3 x4 x5 x6 : Bool,
      step3 rule110 x0 x1 x2 x3 x4 x5 x6 ≠ step3 rule110 x0 x1 x2 x3 x4 x5 (!x6) := by
  decide

/-- Зеркальный Rule 124 меняет стороны исключения местами (3-тактная граница v_L ≥ -2/3). -/
theorem rule124_inverts_chirality :
    (∃ x0 x1 x2 x3 x4 x5 x6 : Bool,
      step3 rule124 x0 x1 x2 x3 x4 x5 x6 ≠ step3 rule124 (!x0) x1 x2 x3 x4 x5 x6) ∧
    (∀ x0 x1 x2 x3 x4 x5 x6 : Bool,
      step3 rule124 x0 x1 x2 x3 x4 x5 x6 = step3 rule124 x0 x1 x2 x3 x4 x5 (!x6)) := by
  decide

/-- Линейный Rule 90 не имеет трёхтактного исключения ни с одной стороны. -/
theorem rule90_symmetric_cone :
    (∃ x0 x1 x2 x3 x4 x5 x6 : Bool,
      step3 rule90 x0 x1 x2 x3 x4 x5 x6 ≠ step3 rule90 (!x0) x1 x2 x3 x4 x5 x6) ∧
    (∃ x0 x1 x2 x3 x4 x5 x6 : Bool,
      step3 rule90 x0 x1 x2 x3 x4 x5 x6 ≠ step3 rule90 x0 x1 x2 x3 x4 x5 (!x6)) := by
  decide

-- ============================================================================
-- 2. КРИСТАЛЛ `ether14` И ГЛОБАЛЬНАЯ ДИНАМИКА НА `Config := Int → Bool`
-- ============================================================================

/-- Извлечение бита `k` из натурального числа. -/
def testBit (n k : Nat) : Bool :=
  ((n >>> k) &&& 1) == 1

/-- 7 временных строк фонового кристалла `ether14` (период 14 по пространству, 7 по времени). -/
def etherRow (t : Nat) : Nat :=
  match t % 7 with
  | 0 => 16072
  | 1 => 9196
  | 2 => 12862
  | 3 => 15139
  | 4 => 4018
  | 5 => 2299
  | _ => 11407

/-- Значение кристалла `ether14` в точке `(t, x)` (по модулю 7 и 14). -/
def etherCm (t x : Nat) : Bool :=
  testBit (etherRow t) (x % 14)

theorem etherCm_time_periodic (t x : Nat) :
    etherCm (t + 7) x = etherCm t x := by
  simp [etherCm, etherRow]

theorem etherCm_space_periodic (t x : Nat) :
    etherCm t (x + 14) = etherCm t x := by
  simp [etherCm]

/-- Проверка всех 7 × 14 = 98 локальных равенств орбиты Rule 110 на кольце длины 14. -/
theorem etherCm_is_exact_crystal :
    ∀ (t : Fin 7) (x : Fin 14),
      rule110 (etherCm t.val ((x.val + 13) % 14))
              (etherCm t.val x.val)
              (etherCm t.val ((x.val + 1) % 14)) =
      etherCm ((t.val + 1) % 7) x.val := by
  decide

theorem etherCm_step (t x : Nat) :
    rule110 (etherCm t ((x + 13) % 14))
            (etherCm t x)
            (etherCm t ((x + 1) % 14)) =
    etherCm (t + 1) x := by
  have h := etherCm_is_exact_crystal
    ⟨t % 7, Nat.mod_lt t (by decide)⟩
    ⟨x % 14, Nat.mod_lt x (by decide)⟩
  simpa [etherCm, etherRow, Nat.add_mod, Nat.mod_mod] using h

/-- Пространственные фазы `p = 0` и `p = 7` кристалла различны в каждый момент периода 7. -/
theorem donor_phases_0_7_distinguishable :
    ∀ (t : Fin 7), ∃ (x : Fin 14),
      etherCm t.val x.val ≠ etherCm t.val ((x.val + 7) % 14) := by
  decide

/-- Глобальная конфигурация на бесконечной решётке `ℤ`. -/
abbrev Config := Int → Bool

/-- Один синхронный шаг глобального клеточного автомата на `ℤ`. -/
def globalStep (rule : Bool → Bool → Bool → Bool) (c : Config) : Config :=
  fun x => rule (c (x - 1)) (c x) (c (x + 1))

/-- `t`-кратная глобальная эволюция конфигурации `c`. -/
def globalEvol (rule : Bool → Bool → Bool → Bool) (c : Config) : Nat → Config
  | 0     => c
  | t + 1 => globalStep rule (globalEvol rule c t)

/-- Остаток целого числа по модулю 14 в `0..13`. -/
def mod14 (x : Int) : Nat := (x % 14).toNat

/-- Глобальная орбита кристалла `ether14` с пространственным сдвигом `p`. -/
def crystalAt (p t : Nat) (x : Int) : Bool :=
  etherCm t (mod14 (x + p))

/-- `crystalAt p` является точным глобальным решением Rule 110 на всей прямой `ℤ`. -/
theorem crystalAt_step (p t : Nat) (x : Int) :
    globalStep rule110 (crystalAt p t) x = crystalAt p (t + 1) x := by
  unfold globalStep crystalAt
  have h1 : mod14 (x - 1 + p) = (mod14 (x + p) + 13) % 14 := by unfold mod14; omega
  have h2 : mod14 (x + 1 + p) = (mod14 (x + p) + 1) % 14 := by unfold mod14; omega
  rw [h1, h2]
  exact etherCm_step t (mod14 (x + p))

/-- Двукратное побитовое сжатие 9-битного входа `[l0..l3, w0..w3, r]` в `(cm_bit, next_win)`. -/
def step2Window (rule : Bool → Bool → Bool → Bool)
    (l0 l1 l2 l3 w0 w1 w2 w3 r : Bool) : Bool × Nat :=
  let a0 := rule l0 l1 l2
  let a1 := rule l1 l2 l3
  let a2 := rule l2 l3 w0
  let a3 := rule l3 w0 w1
  let a4 := rule w0 w1 w2
  let a5 := rule w1 w2 w3
  let a6 := rule w2 w3 r
  let b0 := rule a0 a1 a2
  let b1 := rule a1 a2 a3
  let b2 := rule a2 a3 a4
  let b3 := rule a3 a4 a5
  let b4 := rule a4 a5 a6
  let nwin := (if b1 then 1 else 0) + (if b2 then 2 else 0) +
              (if b3 then 4 else 0) + (if b4 then 8 else 0)
  (b0, nwin)

private theorem pack4_bits (b1 b2 b3 b4 : Bool) :
    let nwin := (if b1 then 1 else 0) + (if b2 then 2 else 0) +
                (if b3 then 4 else 0) + (if b4 then 8 else 0)
    b1 = testBit nwin 0 ∧ b2 = testBit nwin 1 ∧
    b3 = testBit nwin 2 ∧ b4 = testBit nwin 3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private theorem globalStep2_at (rule : Bool → Bool → Bool → Bool) (c : Config) (x : Int) :
    globalStep rule (globalStep rule c) x =
      rule (rule (c (x - 2)) (c (x - 1)) (c x))
           (rule (c (x - 1)) (c x) (c (x + 1)))
           (rule (c x) (c (x + 1)) (c (x + 2))) := by
  unfold globalStep
  have h1 : x - 1 - 1 = x - 2 := by omega
  have h2 : x - 1 + 1 = x := by omega
  have h3 : x + 1 - 1 = x := by omega
  have h4 : x + 1 + 1 = x + 2 := by omega
  rw [h1, h2, h3, h4]

/-- Мост между `step2Window` и 2-тактной глобальной эволюцией в точках `[a-2 .. a+2]`. -/
theorem globalStep2_bridge (rule : Bool → Bool → Bool → Bool) (c : Config) (a : Int) :
    let res := step2Window rule
      (c (a - 4)) (c (a - 3)) (c (a - 2)) (c (a - 1))
      (c a) (c (a + 1)) (c (a + 2)) (c (a + 3)) (c (a + 4))
    globalStep rule (globalStep rule c) (a - 2) = res.1 ∧
    globalStep rule (globalStep rule c) (a - 1) = testBit res.2 0 ∧
    globalStep rule (globalStep rule c) a       = testBit res.2 1 ∧
    globalStep rule (globalStep rule c) (a + 1) = testBit res.2 2 ∧
    globalStep rule (globalStep rule c) (a + 2) = testBit res.2 3 := by
  dsimp only [step2Window]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [globalStep2_at]
    have h1 : a - 2 - 2 = a - 4 := by omega
    have h2 : a - 2 - 1 = a - 3 := by omega
    have h3 : a - 2 + 1 = a - 1 := by omega
    have h4 : a - 2 + 2 = a := by omega
    rw [h1, h2, h3, h4]
  · rw [globalStep2_at]
    have h1 : a - 1 - 2 = a - 3 := by omega
    have h2 : a - 1 - 1 = a - 2 := by omega
    have h3 : a - 1 + 1 = a := by omega
    have h4 : a - 1 + 2 = a + 1 := by omega
    rw [h1, h2, h3, h4]
    exact (pack4_bits _ _ _ _).1
  · rw [globalStep2_at]
    exact (pack4_bits _ _ _ _).2.1
  · rw [globalStep2_at]
    have h1 : a + 1 - 2 = a - 1 := by omega
    have h2 : a + 1 - 1 = a := by omega
    have h3 : a + 1 + 1 = a + 2 := by omega
    have h4 : a + 1 + 2 = a + 3 := by omega
    rw [h1, h2, h3, h4]
    exact (pack4_bits _ _ _ _).2.2.1
  · rw [globalStep2_at]
    have h1 : a + 2 - 2 = a := by omega
    have h2 : a + 2 - 1 = a + 1 := by omega
    have h3 : a + 2 + 1 = a + 3 := by omega
    have h4 : a + 2 + 2 = a + 4 := by omega
    rw [h1, h2, h3, h4]
    exact (pack4_bits _ _ _ _).2.2.2

-- ============================================================================
-- 3. 63-СОСТОЯННЫЙ ГРАНИЧНЫЙ ТРАНСДЬЮСЕР И ЕГО ДОСТИЖИМОСТЬ
-- ============================================================================

/-- Узел 63-состоянного детерминированного граничного трансдьюсера. -/
structure Node where
  tm    : Nat      -- фаза времени (mod 7)
  am    : Nat      -- фаза границы `a(j) + p` (mod 14)
  win   : Nat      -- 4-битное граничное окно `[a(j) .. a(j)+3]`
  next0 : Fin 63   -- переход при внешнем бите `r = false`
  next1 : Fin 63   -- переход при внешнем бите `r = true`
  deriving Repr, DecidableEq

/-- Упакованная таблица 63 достижимых состояний трансдьюсера (скорость границы `-1/2`). -/
def transducerTable (i : Fin 63) : Node :=
  match i.val with
  |  0 => { tm := 0, am :=  0, win :=  8, next0 := ⟨ 1, by decide⟩, next1 := ⟨ 1, by decide⟩ }
  |  1 => { tm := 2, am := 13, win := 13, next0 := ⟨ 2, by decide⟩, next1 := ⟨ 3, by decide⟩ }
  |  2 => { tm := 4, am := 12, win :=  0, next0 := ⟨ 4, by decide⟩, next1 := ⟨ 5, by decide⟩ }
  |  3 => { tm := 4, am := 12, win :=  8, next0 := ⟨ 6, by decide⟩, next1 := ⟨ 6, by decide⟩ }
  |  4 => { tm := 6, am := 11, win :=  1, next0 := ⟨ 7, by decide⟩, next1 := ⟨ 8, by decide⟩ }
  |  5 => { tm := 6, am := 11, win :=  9, next0 := ⟨ 9, by decide⟩, next1 := ⟨ 9, by decide⟩ }
  |  6 => { tm := 6, am := 11, win := 13, next0 := ⟨10, by decide⟩, next1 := ⟨11, by decide⟩ }
  |  7 => { tm := 1, am := 10, win :=  2, next0 := ⟨12, by decide⟩, next1 := ⟨13, by decide⟩ }
  |  8 => { tm := 1, am := 10, win := 10, next0 := ⟨14, by decide⟩, next1 := ⟨14, by decide⟩ }
  |  9 => { tm := 1, am := 10, win := 14, next0 := ⟨13, by decide⟩, next1 := ⟨12, by decide⟩ }
  | 10 => { tm := 1, am := 10, win :=  0, next0 := ⟨14, by decide⟩, next1 := ⟨15, by decide⟩ }
  | 11 => { tm := 1, am := 10, win :=  8, next0 := ⟨13, by decide⟩, next1 := ⟨13, by decide⟩ }
  | 12 => { tm := 3, am :=  9, win :=  5, next0 := ⟨16, by decide⟩, next1 := ⟨17, by decide⟩ }
  | 13 => { tm := 3, am :=  9, win := 13, next0 := ⟨17, by decide⟩, next1 := ⟨16, by decide⟩ }
  | 14 => { tm := 3, am :=  9, win :=  1, next0 := ⟨18, by decide⟩, next1 := ⟨19, by decide⟩ }
  | 15 => { tm := 3, am :=  9, win :=  9, next0 := ⟨20, by decide⟩, next1 := ⟨20, by decide⟩ }
  | 16 => { tm := 5, am :=  8, win :=  8, next0 := ⟨21, by decide⟩, next1 := ⟨21, by decide⟩ }
  | 17 => { tm := 5, am :=  8, win :=  0, next0 := ⟨22, by decide⟩, next1 := ⟨23, by decide⟩ }
  | 18 => { tm := 5, am :=  8, win :=  2, next0 := ⟨24, by decide⟩, next1 := ⟨21, by decide⟩ }
  | 19 => { tm := 5, am :=  8, win := 10, next0 := ⟨22, by decide⟩, next1 := ⟨22, by decide⟩ }
  | 20 => { tm := 5, am :=  8, win := 14, next0 := ⟨21, by decide⟩, next1 := ⟨24, by decide⟩ }
  | 21 => { tm := 0, am :=  7, win := 13, next0 := ⟨25, by decide⟩, next1 := ⟨26, by decide⟩ }
  | 22 => { tm := 0, am :=  7, win :=  1, next0 := ⟨27, by decide⟩, next1 := ⟨28, by decide⟩ }
  | 23 => { tm := 0, am :=  7, win :=  9, next0 := ⟨29, by decide⟩, next1 := ⟨29, by decide⟩ }
  | 24 => { tm := 0, am :=  7, win :=  5, next0 := ⟨26, by decide⟩, next1 := ⟨25, by decide⟩ }
  | 25 => { tm := 2, am :=  6, win :=  0, next0 := ⟨30, by decide⟩, next1 := ⟨31, by decide⟩ }
  | 26 => { tm := 2, am :=  6, win :=  8, next0 := ⟨32, by decide⟩, next1 := ⟨32, by decide⟩ }
  | 27 => { tm := 2, am :=  6, win :=  2, next0 := ⟨33, by decide⟩, next1 := ⟨32, by decide⟩ }
  | 28 => { tm := 2, am :=  6, win := 10, next0 := ⟨30, by decide⟩, next1 := ⟨30, by decide⟩ }
  | 29 => { tm := 2, am :=  6, win := 14, next0 := ⟨32, by decide⟩, next1 := ⟨33, by decide⟩ }
  | 30 => { tm := 4, am :=  5, win :=  1, next0 := ⟨34, by decide⟩, next1 := ⟨35, by decide⟩ }
  | 31 => { tm := 4, am :=  5, win :=  9, next0 := ⟨36, by decide⟩, next1 := ⟨36, by decide⟩ }
  | 32 => { tm := 4, am :=  5, win := 13, next0 := ⟨37, by decide⟩, next1 := ⟨38, by decide⟩ }
  | 33 => { tm := 4, am :=  5, win :=  5, next0 := ⟨38, by decide⟩, next1 := ⟨37, by decide⟩ }
  | 34 => { tm := 6, am :=  4, win :=  2, next0 := ⟨39, by decide⟩, next1 := ⟨40, by decide⟩ }
  | 35 => { tm := 6, am :=  4, win := 10, next0 := ⟨41, by decide⟩, next1 := ⟨41, by decide⟩ }
  | 36 => { tm := 6, am :=  4, win := 14, next0 := ⟨40, by decide⟩, next1 := ⟨39, by decide⟩ }
  | 37 => { tm := 6, am :=  4, win :=  0, next0 := ⟨41, by decide⟩, next1 := ⟨42, by decide⟩ }
  | 38 => { tm := 6, am :=  4, win :=  8, next0 := ⟨40, by decide⟩, next1 := ⟨40, by decide⟩ }
  | 39 => { tm := 1, am :=  3, win :=  5, next0 := ⟨43, by decide⟩, next1 := ⟨44, by decide⟩ }
  | 40 => { tm := 1, am :=  3, win := 13, next0 := ⟨44, by decide⟩, next1 := ⟨43, by decide⟩ }
  | 41 => { tm := 1, am :=  3, win :=  1, next0 := ⟨45, by decide⟩, next1 := ⟨46, by decide⟩ }
  | 42 => { tm := 1, am :=  3, win :=  9, next0 := ⟨47, by decide⟩, next1 := ⟨47, by decide⟩ }
  | 43 => { tm := 3, am :=  2, win :=  8, next0 := ⟨48, by decide⟩, next1 := ⟨48, by decide⟩ }
  | 44 => { tm := 3, am :=  2, win :=  0, next0 := ⟨49, by decide⟩, next1 := ⟨50, by decide⟩ }
  | 45 => { tm := 3, am :=  2, win :=  2, next0 := ⟨51, by decide⟩, next1 := ⟨48, by decide⟩ }
  | 46 => { tm := 3, am :=  2, win := 10, next0 := ⟨49, by decide⟩, next1 := ⟨49, by decide⟩ }
  | 47 => { tm := 3, am :=  2, win := 14, next0 := ⟨48, by decide⟩, next1 := ⟨51, by decide⟩ }
  | 48 => { tm := 5, am :=  1, win := 13, next0 := ⟨52, by decide⟩, next1 := ⟨ 0, by decide⟩ }
  | 49 => { tm := 5, am :=  1, win :=  1, next0 := ⟨53, by decide⟩, next1 := ⟨54, by decide⟩ }
  | 50 => { tm := 5, am :=  1, win :=  9, next0 := ⟨55, by decide⟩, next1 := ⟨55, by decide⟩ }
  | 51 => { tm := 5, am :=  1, win :=  5, next0 := ⟨ 0, by decide⟩, next1 := ⟨52, by decide⟩ }
  | 52 => { tm := 0, am :=  0, win :=  0, next0 := ⟨56, by decide⟩, next1 := ⟨57, by decide⟩ }
  | 53 => { tm := 0, am :=  0, win :=  2, next0 := ⟨58, by decide⟩, next1 := ⟨ 1, by decide⟩ }
  | 54 => { tm := 0, am :=  0, win := 10, next0 := ⟨56, by decide⟩, next1 := ⟨56, by decide⟩ }
  | 55 => { tm := 0, am :=  0, win := 14, next0 := ⟨ 1, by decide⟩, next1 := ⟨58, by decide⟩ }
  | 56 => { tm := 2, am := 13, win :=  1, next0 := ⟨59, by decide⟩, next1 := ⟨60, by decide⟩ }
  | 57 => { tm := 2, am := 13, win :=  9, next0 := ⟨61, by decide⟩, next1 := ⟨61, by decide⟩ }
  | 58 => { tm := 2, am := 13, win :=  5, next0 := ⟨ 3, by decide⟩, next1 := ⟨ 2, by decide⟩ }
  | 59 => { tm := 4, am := 12, win :=  2, next0 := ⟨62, by decide⟩, next1 := ⟨ 6, by decide⟩ }
  | 60 => { tm := 4, am := 12, win := 10, next0 := ⟨ 4, by decide⟩, next1 := ⟨ 4, by decide⟩ }
  | 61 => { tm := 4, am := 12, win := 14, next0 := ⟨ 6, by decide⟩, next1 := ⟨62, by decide⟩ }
  | _  => { tm := 6, am := 11, win :=  5, next0 := ⟨11, by decide⟩, next1 := ⟨10, by decide⟩ }

/-- Шаг графа переходов по внешнему биту `r`. -/
def nextNode (i : Fin 63) (r : Bool) : Fin 63 :=
  if r then (transducerTable i).next1 else (transducerTable i).next0

/-- Прогон конечного входного слова по графу переходов. -/
def runList (st : Fin 63) : List Bool → Fin 63
  | []      => st
  | r :: rs => runList (nextNode st r) rs

/-- Кратчайшие слова-свидетели достижимости каждого из 63 узлов из узла 0. -/
def witnessWord (i : Fin 63) : List Bool :=
  match i.val with
  |  0 => []
  |  1 => [false]
  |  2 => [false, false]
  |  3 => [false, true]
  |  4 => [false, false, false]
  |  5 => [false, false, true]
  |  6 => [false, true, false]
  |  7 => [false, false, false, false]
  |  8 => [false, false, false, true]
  |  9 => [false, false, true, false]
  | 10 => [false, true, false, false]
  | 11 => [false, true, false, true]
  | 12 => [false, false, false, false, false]
  | 13 => [false, false, false, false, true]
  | 14 => [false, false, false, true, false]
  | 15 => [false, true, false, false, true]
  | 16 => [false, false, false, false, false, false]
  | 17 => [false, false, false, false, false, true]
  | 18 => [false, false, false, true, false, false]
  | 19 => [false, false, false, true, false, true]
  | 20 => [false, true, false, false, true, false]
  | 21 => [false, false, false, false, false, false, false]
  | 22 => [false, false, false, false, false, true, false]
  | 23 => [false, false, false, false, false, true, true]
  | 24 => [false, false, false, true, false, false, false]
  | 25 => [false, false, false, false, false, false, false, false]
  | 26 => [false, false, false, false, false, false, false, true]
  | 27 => [false, false, false, false, false, true, false, false]
  | 28 => [false, false, false, false, false, true, false, true]
  | 29 => [false, false, false, false, false, true, true, false]
  | 30 => [false, false, false, false, false, false, false, false, false]
  | 31 => [false, false, false, false, false, false, false, false, true]
  | 32 => [false, false, false, false, false, false, false, true, false]
  | 33 => [false, false, false, false, false, true, false, false, false]
  | 34 => [false, false, false, false, false, false, false, false, false, false]
  | 35 => [false, false, false, false, false, false, false, false, false, true]
  | 36 => [false, false, false, false, false, false, false, false, true, false]
  | 37 => [false, false, false, false, false, false, false, true, false, false]
  | 38 => [false, false, false, false, false, false, false, true, false, true]
  | 39 => [false, false, false, false, false, false, false, false, false, false, false]
  | 40 => [false, false, false, false, false, false, false, false, false, false, true]
  | 41 => [false, false, false, false, false, false, false, false, false, true, false]
  | 42 => [false, false, false, false, false, false, false, true, false, false, true]
  | 43 => [false, false, false, false, false, false, false, false, false, false, false, false]
  | 44 => [false, false, false, false, false, false, false, false, false, false, false, true]
  | 45 => [false, false, false, false, false, false, false, false, false, true, false, false]
  | 46 => [false, false, false, false, false, false, false, false, false, true, false, true]
  | 47 => [false, false, false, false, false, false, false, true, false, false, true, false]
  | 48 => [false, false, false, false, false, false, false, false, false, false, false, false, false]
  | 49 => [false, false, false, false, false, false, false, false, false, false, false, true, false]
  | 50 => [false, false, false, false, false, false, false, false, false, false, false, true, true]
  | 51 => [false, false, false, false, false, false, false, false, false, true, false, false, false]
  | 52 => [false, false, false, false, false, false, false, false, false, false, false, false, false, false]
  | 53 => [false, false, false, false, false, false, false, false, false, false, false, true, false, false]
  | 54 => [false, false, false, false, false, false, false, false, false, false, false, true, false, true]
  | 55 => [false, false, false, false, false, false, false, false, false, false, false, true, true, false]
  | 56 => [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
  | 57 => [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]
  | 58 => [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false]
  | 59 => [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
  | 60 => [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]
  | 61 => [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]
  | _  => [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

/-- Начальный узел 0 точно соответствует чистому окну фазы `p = 0`: `etherCm 0 [0..3]`. -/
theorem initial_node_p0_sound :
    let nd := transducerTable ⟨0, by decide⟩
    nd.tm = 0 ∧ nd.am = 0 ∧
    ∀ k : Fin 4, testBit nd.win k.val = etherCm 0 k.val := by
  decide

/-- Узел 21 точно соответствует чистому окну донорской фазы `p = 7`: `etherCm 0 [7..10]`. -/
theorem initial_node_p7_sound :
    let nd := transducerTable ⟨21, by decide⟩
    nd.tm = 0 ∧ nd.am = 7 ∧
    ∀ k : Fin 4, testBit nd.win k.val = etherCm 0 ((k.val + 7) % 14) := by
  decide

/-- Все 63 состояния таблицы действительно достижимы из узла 0. -/
theorem every_node_reachable :
    ∀ i : Fin 63, runList ⟨0, by decide⟩ (witnessWord i) = i := by
  decide

/-- Локальный двутактный отклик узла `i` под Rule 110. -/
def evalNode (i : Fin 63) (r : Bool) : Bool × Nat :=
  let nd := transducerTable i
  step2Window rule110
    (etherCm nd.tm ((nd.am + 10) % 14))
    (etherCm nd.tm ((nd.am + 11) % 14))
    (etherCm nd.tm ((nd.am + 12) % 14))
    (etherCm nd.tm ((nd.am + 13) % 14))
    (testBit nd.win 0) (testBit nd.win 1) (testBit nd.win 2) (testBit nd.win 3) r

/-- Центральный конечный сертификат (63 × 2 = 126 переходов). -/
theorem transducer_step_sound :
    ∀ (i : Fin 63) (r : Bool),
      let nd  := transducerTable i
      let nd' := transducerTable (nextNode i r)
      let res := evalNode i r
      res.1 = etherCm ((nd.tm + 2) % 7) ((nd.am + 12) % 14) ∧
      res.2 = nd'.win ∧
      nd'.tm = (nd.tm + 2) % 7 ∧
      nd'.am = (nd.am + 13) % 14 := by
  decide

-- ============================================================================
-- 4. ГЛОБАЛЬНАЯ ИНДУКЦИЯ НА БЕСКОНЕЧНОЙ РЕШЁТКЕ (ВСЕ `j : Nat` И ВСЕ `x < -j`)
-- ============================================================================

/-- Сопряжённый глобальный инвариант на шаге `j` для фазы `p`:
    вся бесконечная левая полупрямая `x < -(j : Int)` совпадает с `crystalAt p (2 * j)`,
    а 4-битное окно на границе `[-(j : Int) .. -(j : Int) + 3]` совпадает с узлом `st`. -/
def GlobalInv (cfg : Config) (p j : Nat) : Prop :=
  ∃ st : Fin 63,
    let c := globalEvol rule110 cfg (2 * j)
    let nd := transducerTable st
    nd.tm = (2 * j) % 7 ∧
    nd.am = mod14 (-(j : Int) + p) ∧
    (∀ x : Int, x < -(j : Int) → c x = crystalAt p (2 * j) x) ∧
    (∀ k : Fin 4, c (-(j : Int) + k.val) = testBit nd.win k.val)

/-- Стартовая конфигурация фазы `p` с произвольным внешним правым хвостом `tail`. -/
def cfgWithTail (p : Nat) (tail : Int → Bool) : Config :=
  fun x => if x < 4 then crystalAt p 0 x else tail x

/-- Индукционный шаг `j → j + 1`: глобальная эволюция Rule 110 сохраняет `GlobalInv`. -/
theorem globalInv_step (cfg : Config) (p j : Nat) (h : GlobalInv cfg p j) :
    GlobalInv cfg p (j + 1) := by
  rcases h with ⟨st, htm, ham, hleft, hwin⟩
  let c : Config := globalEvol rule110 cfg (2 * j)
  let a : Int := -(j : Int)
  change (transducerTable st).am = mod14 (a + p) at ham
  change ∀ x : Int, x < a → c x = crystalAt p (2 * j) x at hleft
  change ∀ k : Fin 4, c (a + k.val) = testBit (transducerTable st).win k.val at hwin
  let r : Bool := c (a + 4)
  have hl0 : c (a - 4) = etherCm (transducerTable st).tm (((transducerTable st).am + 10) % 14) := by
    rw [hleft (a - 4) (by omega)]; unfold crystalAt; rw [htm, ham]
    have hm : mod14 (a - 4 + p) = (mod14 (a + p) + 10) % 14 := by unfold mod14; omega
    rw [hm]; simp [etherCm, etherRow]
  have hl1 : c (a - 3) = etherCm (transducerTable st).tm (((transducerTable st).am + 11) % 14) := by
    rw [hleft (a - 3) (by omega)]; unfold crystalAt; rw [htm, ham]
    have hm : mod14 (a - 3 + p) = (mod14 (a + p) + 11) % 14 := by unfold mod14; omega
    rw [hm]; simp [etherCm, etherRow]
  have hl2 : c (a - 2) = etherCm (transducerTable st).tm (((transducerTable st).am + 12) % 14) := by
    rw [hleft (a - 2) (by omega)]; unfold crystalAt; rw [htm, ham]
    have hm : mod14 (a - 2 + p) = (mod14 (a + p) + 12) % 14 := by unfold mod14; omega
    rw [hm]; simp [etherCm, etherRow]
  have hl3 : c (a - 1) = etherCm (transducerTable st).tm (((transducerTable st).am + 13) % 14) := by
    rw [hleft (a - 1) (by omega)]; unfold crystalAt; rw [htm, ham]
    have hm : mod14 (a - 1 + p) = (mod14 (a + p) + 13) % 14 := by unfold mod14; omega
    rw [hm]; simp [etherCm, etherRow]
  have hw0 : c a       = testBit (transducerTable st).win 0 := by simpa using hwin ⟨0, by decide⟩
  have hw1 : c (a + 1) = testBit (transducerTable st).win 1 := by simpa using hwin ⟨1, by decide⟩
  have hw2 : c (a + 2) = testBit (transducerTable st).win 2 := by simpa using hwin ⟨2, by decide⟩
  have hw3 : c (a + 3) = testBit (transducerTable st).win 3 := by simpa using hwin ⟨3, by decide⟩
  refine ⟨nextNode st r, ?_, ?_, ?_, ?_⟩
  · have hs := (transducer_step_sound st r).2.2.1
    rw [hs, htm]; omega
  · have hs := (transducer_step_sound st r).2.2.2
    rw [hs, ham]; unfold mod14; omega
  · intro x hx
    have h2 : globalEvol rule110 cfg (2 * (j + 1)) x =
              globalStep rule110 (globalStep rule110 c) x := by
      have heq : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [heq]; rfl
    rw [h2]
    by_cases hfar : x ≤ a - 3
    · have hc1 : ∀ y : Int, y < a - 1 → globalStep rule110 c y = crystalAt p (2 * j + 1) y := by
        intro y hy
        change rule110 (c (y - 1)) (c y) (c (y + 1)) = crystalAt p (2 * j + 1) y
        rw [hleft (y - 1) (by omega), hleft y (by omega), hleft (y + 1) (by omega)]
        exact crystalAt_step p (2 * j) y
      change rule110 (globalStep rule110 c (x - 1)) (globalStep rule110 c x) (globalStep rule110 c (x + 1)) =
             crystalAt p (2 * (j + 1)) x
      rw [hc1 (x - 1) (by omega), hc1 x (by omega), hc1 (x + 1) (by omega)]
      have heq : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [heq]
      exact crystalAt_step p (2 * j + 1) x
    · have hx_eq : x = a - 2 := by omega
      rw [hx_eq, (globalStep2_bridge rule110 c a).1]
      rw [hl0, hl1, hl2, hl3, hw0, hw1, hw2, hw3]
      have hs := (transducer_step_sound st r).1
      change (evalNode st r).1 = crystalAt p (2 * (j + 1)) (a - 2)
      rw [hs, htm, ham]
      unfold crystalAt etherCm etherRow
      have ht : ((2 * j % 7 + 2) % 7) % 7 = (2 * (j + 1)) % 7 := by omega
      have ha : ((mod14 (a + p) + 12) % 14) % 14 = mod14 (a - 2 + p) % 14 := by unfold mod14; omega
      rw [ht, ha]
  · intro k
    have h2 : globalEvol rule110 cfg (2 * (j + 1)) (-(↑(j + 1) : Int) + k.val) =
              globalStep rule110 (globalStep rule110 c) (-(↑(j + 1) : Int) + k.val) := by
      have heq : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [heq]; rfl
    rw [h2]
    have hbr := globalStep2_bridge rule110 c a
    have hwin_eq : (evalNode st r).2 = (transducerTable (nextNode st r)).win :=
      (transducer_step_sound st r).2.1
    rcases k with ⟨kv, hkv⟩
    match kv, hkv with
    | 0, _ =>
      have hx : -(↑(j + 1) : Int) + (0 : Nat) = a - 1 := by omega
      rw [hx, hbr.2.1, hl0, hl1, hl2, hl3, hw0, hw1, hw2, hw3]
      exact congrArg (fun w => testBit w 0) hwin_eq
    | 1, _ =>
      have hx : -(↑(j + 1) : Int) + (1 : Nat) = a := by omega
      rw [hx, hbr.2.2.1, hl0, hl1, hl2, hl3, hw0, hw1, hw2, hw3]
      exact congrArg (fun w => testBit w 1) hwin_eq
    | 2, _ =>
      have hx : -(↑(j + 1) : Int) + (2 : Nat) = a + 1 := by omega
      rw [hx, hbr.2.2.2.1, hl0, hl1, hl2, hl3, hw0, hw1, hw2, hw3]
      exact congrArg (fun w => testBit w 2) hwin_eq
    | 3, _ =>
      have hx : -(↑(j + 1) : Int) + (3 : Nat) = a + 2 := by omega
      rw [hx, hbr.2.2.2.2, hl0, hl1, hl2, hl3, hw0, hw1, hw2, hw3]
      exact congrArg (fun w => testBit w 3) hwin_eq

theorem globalInv_p0_zero (tail : Int → Bool) :
    GlobalInv (cfgWithTail 0 tail) 0 0 := by
  refine ⟨⟨0, by decide⟩, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro x hx
    unfold globalEvol cfgWithTail
    have h4 : x < 4 := by omega
    rw [if_pos h4]
  · intro k
    unfold globalEvol cfgWithTail
    have h4 : (-(↑(0 : Nat) : Int) + (k.val : Int)) < 4 := by omega
    rw [if_pos h4]
    unfold crystalAt
    have hm : mod14 (-(↑(0 : Nat) : Int) + (k.val : Int) + (0 : Nat)) = k.val := by
      unfold mod14; omega
    rw [hm]
    exact (initial_node_p0_sound.2.2 k).symm

theorem globalInv_p7_zero (tail : Int → Bool) :
    GlobalInv (cfgWithTail 7 tail) 7 0 := by
  refine ⟨⟨21, by decide⟩, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro x hx
    unfold globalEvol cfgWithTail
    have h4 : x < 4 := by omega
    rw [if_pos h4]
  · intro k
    unfold globalEvol cfgWithTail
    have h4 : (-(↑(0 : Nat) : Int) + (k.val : Int)) < 4 := by omega
    rw [if_pos h4]
    unfold crystalAt
    have hm : mod14 (-(↑(0 : Nat) : Int) + (k.val : Int) + (7 : Nat)) = (k.val + 7) % 14 := by
      unfold mod14; omega
    rw [hm]
    exact (initial_node_p7_sound.2.2 k).symm

/-- Теорема 4a (ГЛОБАЛЬНОЕ ЗАМЫКАНИЕ ДЛЯ ФАЗЫ `p = 0`):
    индукцией по `j : Nat` вся бесконечная левая полупрямая `x < -(j : Int)` сохраняет
    кристалл `ether14` при любом произвольном внешнем хвосте `tail : Int → Bool`. -/
theorem global_crystal_preserved_p0 (tail : Int → Bool) :
    ∀ (j : Nat) (x : Int), x < -(j : Int) →
      globalEvol rule110 (cfgWithTail 0 tail) (2 * j) x = crystalAt 0 (2 * j) x := by
  have hall : ∀ j : Nat, GlobalInv (cfgWithTail 0 tail) 0 j := by
    intro j
    induction j with
    | zero => exact globalInv_p0_zero tail
    | succ j ih => exact globalInv_step _ 0 j ih
  intro j x hx
  rcases hall j with ⟨_, _, _, hleft, _⟩
  exact hleft x hx

/-- Теорема 4b (ГЛОБАЛЬНОЕ ЗАМЫКАНИЕ ДЛЯ ДОНОРСКОЙ ФАЗЫ `p = 7`):
    та же глобальная теорема для донорской фазы `p = 7` (узел 21) при том же `tail`. -/
theorem global_crystal_preserved_p7 (tail : Int → Bool) :
    ∀ (j : Nat) (x : Int), x < -(j : Int) →
      globalEvol rule110 (cfgWithTail 7 tail) (2 * j) x = crystalAt 7 (2 * j) x := by
  have hall : ∀ j : Nat, GlobalInv (cfgWithTail 7 tail) 7 j := by
    intro j
    induction j with
    | zero => exact globalInv_p7_zero tail
    | succ j ih => exact globalInv_step _ 7 j ih
  intro j x hx
  rcases hall j with ⟨_, _, _, hleft, _⟩
  exact hleft x hx

-- ============================================================================
-- 5. ГЛОБАЛЬНАЯ КОНТРФАКТИЧЕСКАЯ ПОДМЕНА ДОНОРСКИХ ФАЗ (G5-1)
-- ============================================================================

/-- Теорема 5 (G5-1 на бесконечной решётке): для ЛЮБОГО общего внешнего правого хвоста
    `tail : Int → Bool` и ЛЮБОГО шага `j : Nat` подмена донорской фазы `p = 0 ↔ p = 7`
    причинно переключает глобальное состояние позади движущейся границы `a(j) = -(j : Int)`. -/
theorem counterfactual_donor_swap_G5_1 (tail : Int → Bool) (j : Nat) :
    ∃ x : Int, x < -(j : Int) ∧
      globalEvol rule110 (cfgWithTail 0 tail) (2 * j) x ≠
      globalEvol rule110 (cfgWithTail 7 tail) (2 * j) x := by
  rcases donor_phases_0_7_distinguishable ⟨(2 * j) % 7, Nat.mod_lt (2 * j) (by decide)⟩ with ⟨x0, hdiff⟩
  let base : Int := -(j : Int) - 14
  let shift : Nat := (x0.val + 14 - mod14 base) % 14
  let x : Int := base + shift
  have hx : x < -(j : Int) := by
    have hs : shift < 14 := Nat.mod_lt _ (by decide)
    omega
  refine ⟨x, hx, ?_⟩
  rw [global_crystal_preserved_p0 tail j x hx, global_crystal_preserved_p7 tail j x hx]
  unfold crystalAt
  have hm0 : mod14 (x + (0 : Nat)) = x0.val := by
    have hlt : x0.val < 14 := x0.isLt
    have hb  : mod14 base < 14 := by unfold mod14; omega
    have hsh : shift = (x0.val + 14 - mod14 base) % 14 := rfl
    unfold mod14 at *
    omega
  have hm7 : mod14 (x + (7 : Nat)) = (x0.val + 7) % 14 := by
    have h0 := hm0
    unfold mod14 at *
    omega
  rw [hm0, hm7]
  simpa [etherCm, etherRow] using hdiff

-- ============================================================================
-- 6. СЛОМ ДОСТИЖИМОГО ШВА ПРИ ЗЕРКАЛЬНОЙ ИНВЕРСИИ НА RULE 124 (G5-2)
-- ============================================================================

/-- Локальный двутактный отклик узла `i` таблицы `transducerTable` под зеркальным Rule 124. -/
def evalNode124 (i : Fin 63) (r : Bool) : Bool × Nat :=
  let nd := transducerTable i
  step2Window rule124
    (etherCm nd.tm ((nd.am + 10) % 14))
    (etherCm nd.tm ((nd.am + 11) % 14))
    (etherCm nd.tm ((nd.am + 12) % 14))
    (etherCm nd.tm ((nd.am + 13) % 14))
    (testBit nd.win 0) (testBit nd.win 1) (testBit nd.win 2) (testBit nd.win 3) r

/-- Теорема 6 (G5-2): на достижимом узле `i = 0` таблицы `transducerTable` и входе `r = false`
    зеркальный Rule 124 нарушает кристаллический бит Rule 110. -/
theorem mirror_rule124_breaks_reachable_seam :
    ∃ (i : Fin 63) (r : Bool),
      runList ⟨0, by decide⟩ (witnessWord i) = i ∧
      (evalNode124 i r).1 ≠
        etherCm (((transducerTable i).tm + 2) % 7) (((transducerTable i).am + 12) % 14) := by
  refine ⟨⟨0, by decide⟩, false, by decide, by decide⟩

end Rule110ChiralSeam