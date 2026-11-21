/-!
# Rule110RingDecoupling.lean

Машинно-проверяемое доказательство (чистое ядро Lean 4, без Mathlib, без `sorry`
и без `native_decide`) **персистентного расцепления ёмкости и причинного носителя**
в клеточном автомате Rule 110 на конечном периодическом кольце `ℤ_7`:

- Максимальный предпериод `μ_7 = 7`, НОК длин циклов `P_7 = 14`.
- Для **всех** `t ≥ 7` (без верхней границы по времени) множество достижимых состояний
  сжимается ровно до **15 состояний** (`|B_t^(7)| = 15 < 2^4`, битовая ёмкость `C_t^(7) = 4` бита).
- При этом для **всех** `t ≥ 7` **все 7 входных координат** `j ∈ ℤ_7` остаются причинно
  существенными для наблюдаемой `obs0` (`D_t^(7) = ℤ_7`, `C_t^(7) = 4 < 7 = |D_t^(7)|`).
- Для контраста доказан полный коллапс линейного правила Rule 90 на кольце `ℤ_8` за 4 такта.
-/

namespace Rule110RingDecoupling

set_option maxRecDepth 4096

/-- Один синхронный шаг Rule 110 на периодическом кольце `ℤ_7` (7-битная маска). -/
def stepRing7 (u : Fin 128) : Fin 128 :=
  let c := u.val
  let l := ((c <<< 1) ||| (c >>> 6)) &&& 127
  let r := ((c >>> 1) ||| ((c &&& 1) <<< 6)) &&& 127
  let nxt := ((c ||| r) ^^^ (l &&& c &&& r)) &&& 127
  ⟨nxt, Nat.lt_of_le_of_lt Nat.and_le_right (by decide : 127 < 128)⟩

/-- `t`-кратная эволюция Rule 110 на кольце `ℤ_7`. -/
def evolRing7 : Nat → Fin 128 → Fin 128
  | 0,     u => u
  | t + 1, u => stepRing7 (evolRing7 t u)

/-- Наблюдаемая в ячейке `0`. -/
def obs0 (u : Fin 128) : Bool :=
  (u.val &&& 1) == 1

/-- Переворот одного входного бита `j ∈ Fin 7`. -/
def flipBit7 (j : Fin 7) (u : Fin 128) : Fin 128 :=
  ⟨(u.val ^^^ (1 <<< j.val)) &&& 127, Nat.lt_of_le_of_lt Nat.and_le_right (by decide : 127 < 128)⟩

theorem evolRing7_add (a b : Nat) (u : Fin 128) :
    evolRing7 (a + b) u = evolRing7 a (evolRing7 b u) := by
  induction a with
  | zero => simp [evolRing7]
  | succ a ih =>
    have h : (a + 1) + b = (a + b) + 1 := by omega
    rw [h]
    unfold evolRing7
    rw [ih]

-- ============================================================================
-- 1. ТОЧНЫЙ ПРЕДПЕРИОД `μ_7 = 7` И ПЕРИОД `P_7 = 14` ДЛЯ ВСЕХ `t ≥ 7`
-- ============================================================================

/-- Конечный сертификат (128 состояний): при `t = 7` система уже на цикле делителя 14. -/
theorem ring7_cycle_base :
    ∀ u : Fin 128, evolRing7 21 u = evolRing7 7 u := by
  decide

theorem evolRing7_period14 (t : Nat) (ht : t ≥ 7) (u : Fin 128) :
    evolRing7 (t + 14) u = evolRing7 t u := by
  have h1 : t + 14 = (t - 7) + 21 := by omega
  have h2 : t = (t - 7) + 7 := by omega
  rw [h1, evolRing7_add, ring7_cycle_base, ← evolRing7_add, ← h2]

theorem evolRing7_add_mul14 (k d : Nat) (u : Fin 128) :
    evolRing7 (7 + d + 14 * k) u = evolRing7 (7 + d) u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : 7 + d + 14 * (k + 1) = (7 + d + 14 * k) + 14 := by omega
    rw [h, evolRing7_period14 _ (by omega), ih]

/-- Редукция любого времени `t ≥ 7` к базовому окну `7 + (t - 7) % 14`. -/
theorem evolRing7_reduce (t : Nat) (ht : t ≥ 7) (u : Fin 128) :
    evolRing7 t u = evolRing7 (7 + (t - 7) % 14) u := by
  have hdiv : t = 7 + (t - 7) % 14 + 14 * ((t - 7) / 14) := by omega
  conv => lhs; rw [hdiv]
  exact evolRing7_add_mul14 ((t - 7) / 14) ((t - 7) % 14) u

-- ============================================================================
-- 2. СЖАТИЕ ЁМКОСТИ: РОВНО 15 АТТРАКТОРНЫХ СОСТОЯНИЙ (`C_t^(7) = 4 < 7`)
-- ============================================================================

/-- Точный список 15 достижимых аттракторных состояний кольца `ℤ_7`. -/
def attractors7 (k : Fin 15) : Fin 128 :=
  match k.val with
  |  0 => ⟨  0, by decide⟩
  |  1 => ⟨ 13, by decide⟩
  |  2 => ⟨ 26, by decide⟩
  |  3 => ⟨ 31, by decide⟩
  |  4 => ⟨ 35, by decide⟩
  |  5 => ⟨ 52, by decide⟩
  |  6 => ⟨ 62, by decide⟩
  |  7 => ⟨ 70, by decide⟩
  |  8 => ⟨ 79, by decide⟩
  |  9 => ⟨ 81, by decide⟩
  | 10 => ⟨103, by decide⟩
  | 11 => ⟨104, by decide⟩
  | 12 => ⟨115, by decide⟩
  | 13 => ⟨121, by decide⟩
  | _  => ⟨124, by decide⟩

/-- Перестановка на 15 аттракторах под действием одного шага `stepRing7`. -/
def nextAttr7 (k : Fin 15) : Fin 15 :=
  match k.val with
  |  0 => ⟨ 0, by decide⟩
  |  1 => ⟨ 8, by decide⟩
  |  2 => ⟨ 3, by decide⟩
  |  3 => ⟨ 9, by decide⟩
  |  4 => ⟨12, by decide⟩
  |  5 => ⟨ 6, by decide⟩
  |  6 => ⟨ 4, by decide⟩
  |  7 => ⟨10, by decide⟩
  |  8 => ⟨11, by decide⟩
  |  9 => ⟨13, by decide⟩
  | 10 => ⟨ 5, by decide⟩
  | 11 => ⟨14, by decide⟩
  | 12 => ⟨ 2, by decide⟩
  | 13 => ⟨ 1, by decide⟩
  | _  => ⟨ 7, by decide⟩

/-- Итерация перестановки аттракторов. -/
def iterNextAttr7 : Nat → Fin 15 → Fin 15
  | 0,     k => k
  | d + 1, k => nextAttr7 (iterNextAttr7 d k)

/-- Кодировщик `u ↦ индекс evolRing7 7 u` в `Fin 15`. -/
def idx7 (u : Fin 128) : Fin 15 :=
  match u.val with
  |   0 => ⟨ 0, by decide⟩
  |   1 => ⟨11, by decide⟩
  |   2 => ⟨ 9, by decide⟩
  |   3 => ⟨13, by decide⟩
  |   4 => ⟨ 4, by decide⟩
  |   5 => ⟨14, by decide⟩
  |   6 => ⟨12, by decide⟩
  |   7 => ⟨ 2, by decide⟩
  |   8 => ⟨ 7, by decide⟩
  |   9 => ⟨12, by decide⟩
  |  10 => ⟨13, by decide⟩
  |  11 => ⟨ 6, by decide⟩
  |  12 => ⟨10, by decide⟩
  |  13 => ⟨ 6, by decide⟩
  |  14 => ⟨ 5, by decide⟩
  |  15 => ⟨ 1, by decide⟩
  |  16 => ⟨ 1, by decide⟩
  |  17 => ⟨ 6, by decide⟩
  |  18 => ⟨10, by decide⟩
  |  19 => ⟨ 3, by decide⟩
  |  20 => ⟨12, by decide⟩
  |  21 => ⟨ 5, by decide⟩
  |  22 => ⟨14, by decide⟩
  |  23 => ⟨13, by decide⟩
  |  24 => ⟨ 8, by decide⟩
  |  25 => ⟨13, by decide⟩
  |  26 => ⟨14, by decide⟩
  |  27 => ⟨ 5, by decide⟩
  |  28 => ⟨11, by decide⟩
  |  29 => ⟨ 4, by decide⟩
  |  30 => ⟨ 2, by decide⟩
  |  31 => ⟨ 7, by decide⟩
  |  32 => ⟨ 2, by decide⟩
  |  33 => ⟨ 3, by decide⟩
  |  34 => ⟨14, by decide⟩
  |  35 => ⟨ 8, by decide⟩
  |  36 => ⟨ 8, by decide⟩
  |  37 => ⟨ 1, by decide⟩
  |  38 => ⟨ 6, by decide⟩
  |  39 => ⟨11, by decide⟩
  |  40 => ⟨10, by decide⟩
  |  41 => ⟨ 4, by decide⟩
  |  42 => ⟨11, by decide⟩
  |  43 => ⟨ 0, by decide⟩
  |  44 => ⟨13, by decide⟩
  |  45 => ⟨ 0, by decide⟩
  |  46 => ⟨12, by decide⟩
  |  47 => ⟨10, by decide⟩
  |  48 => ⟨ 3, by decide⟩
  |  49 => ⟨10, by decide⟩
  |  50 => ⟨12, by decide⟩
  |  51 => ⟨ 7, by decide⟩
  |  52 => ⟨13, by decide⟩
  |  53 => ⟨ 0, by decide⟩
  |  54 => ⟨11, by decide⟩
  |  55 => ⟨ 4, by decide⟩
  |  56 => ⟨ 9, by decide⟩
  |  57 => ⟨ 8, by decide⟩
  |  58 => ⟨ 7, by decide⟩
  |  59 => ⟨ 2, by decide⟩
  |  60 => ⟨ 5, by decide⟩
  |  61 => ⟨ 3, by decide⟩
  |  62 => ⟨ 1, by decide⟩
  |  63 => ⟨14, by decide⟩
  |  64 => ⟨ 5, by decide⟩
  |  65 => ⟨14, by decide⟩
  |  66 => ⟨ 6, by decide⟩
  |  67 => ⟨ 1, by decide⟩
  |  68 => ⟨13, by decide⟩
  |  69 => ⟨ 3, by decide⟩
  |  70 => ⟨ 3, by decide⟩
  |  71 => ⟨ 7, by decide⟩
  |  72 => ⟨ 3, by decide⟩
  |  73 => ⟨ 8, by decide⟩
  |  74 => ⟨ 2, by decide⟩
  |  75 => ⟨14, by decide⟩
  |  76 => ⟨14, by decide⟩
  |  77 => ⟨ 2, by decide⟩
  |  78 => ⟨ 9, by decide⟩
  |  79 => ⟨ 4, by decide⟩
  |  80 => ⟨ 8, by decide⟩
  |  81 => ⟨10, by decide⟩
  |  82 => ⟨ 7, by decide⟩
  |  83 => ⟨ 5, by decide⟩
  |  84 => ⟨ 9, by decide⟩
  |  85 => ⟨ 0, by decide⟩
  |  86 => ⟨ 0, by decide⟩
  |  87 => ⟨12, by decide⟩
  |  88 => ⟨12, by decide⟩
  |  89 => ⟨ 4, by decide⟩
  |  90 => ⟨ 0, by decide⟩
  |  91 => ⟨ 9, by decide⟩
  |  92 => ⟨10, by decide⟩
  |  93 => ⟨ 1, by decide⟩
  |  94 => ⟨ 8, by decide⟩
  |  95 => ⟨ 6, by decide⟩
  |  96 => ⟨ 6, by decide⟩
  |  97 => ⟨ 7, by decide⟩
  |  98 => ⟨ 8, by decide⟩
  |  99 => ⟨ 4, by decide⟩
  | 100 => ⟨10, by decide⟩
  | 101 => ⟨ 6, by decide⟩
  | 102 => ⟨ 1, by decide⟩
  | 103 => ⟨ 9, by decide⟩
  | 104 => ⟨12, by decide⟩
  | 105 => ⟨ 2, by decide⟩
  | 106 => ⟨ 0, by decide⟩
  | 107 => ⟨13, by decide⟩
  | 108 => ⟨ 9, by decide⟩
  | 109 => ⟨11, by decide⟩
  | 110 => ⟨ 7, by decide⟩
  | 111 => ⟨ 3, by decide⟩
  | 112 => ⟨ 4, by decide⟩
  | 113 => ⟨ 9, by decide⟩
  | 114 => ⟨ 3, by decide⟩
  | 115 => ⟨11, by decide⟩
  | 116 => ⟨ 1, by decide⟩
  | 117 => ⟨14, by decide⟩
  | 118 => ⟨ 5, by decide⟩
  | 119 => ⟨ 8, by decide⟩
  | 120 => ⟨11, by decide⟩
  | 121 => ⟨ 5, by decide⟩
  | 122 => ⟨ 6, by decide⟩
  | 123 => ⟨10, by decide⟩
  | 124 => ⟨ 2, by decide⟩
  | 125 => ⟨12, by decide⟩
  | 126 => ⟨13, by decide⟩
  | _   => ⟨ 0, by decide⟩

/-- Все 15 состояний `attractors7` попарно различны. -/
theorem attractors7_injective :
    ∀ i j : Fin 15, attractors7 i = attractors7 j → i = j := by
  decide

/-- После 7 тактов любая из 128 конфигураций попадает в `attractors7`. -/
theorem evol7_lands_in_attractors :
    ∀ u : Fin 128, evolRing7 7 u = attractors7 (idx7 u) := by
  decide

/-- Замкнутость 15 аттракторов под действием `stepRing7`. -/
theorem attractors7_closed :
    ∀ k : Fin 15, stepRing7 (attractors7 k) = attractors7 (nextAttr7 k) := by
  decide

/-- Теорема 1 (верхняя граница ёмкости для ВСЕХ `t ≥ 7`):
    при любом `t ≥ 7` каждое достижимое состояние принадлежит 15-элементному
    множеству `attractors7` (`|B_t^(7)| ≤ 15 < 2^4`, ёмкость `C_t^(7) ≤ 4` бита). -/
theorem ring7_capacity_bound_all_time (t : Nat) (ht : t ≥ 7) (u : Fin 128) :
    ∃ k : Fin 15, evolRing7 t u = attractors7 k := by
  have hgen : ∀ d : Nat, evolRing7 (d + 7) u = attractors7 (iterNextAttr7 d (idx7 u)) := by
    intro d
    induction d with
    | zero =>
      simpa [iterNextAttr7] using evol7_lands_in_attractors u
    | succ d ih =>
      have h : (d + 1) + 7 = (d + 7) + 1 := by omega
      rw [h]
      unfold evolRing7 iterNextAttr7
      rw [ih, attractors7_closed]
  have ht_eq : t = (t - 7) + 7 := by omega
  rw [ht_eq]
  exact ⟨iterNextAttr7 (t - 7) (idx7 u), hgen (t - 7)⟩

/-- У каждого из 15 состояний есть прообраз на любом шаге, в том числе до шага 7. -/
theorem ring7_attractors_reachable (t : Nat) (k : Fin 15) :
    ∃ u : Fin 128, evolRing7 t u = attractors7 k := by
  have predecessors : ∀ j : Fin 15, ∃ i : Fin 15, nextAttr7 i = j := by decide
  induction t generalizing k with
  | zero => exact ⟨attractors7 k, rfl⟩
  | succ t ih =>
    obtain ⟨i, hi⟩ := predecessors k
    obtain ⟨u, hu⟩ := ih i
    exact ⟨u, by rw [evolRing7, hu, attractors7_closed, hi]⟩

/-- При `t ≥ 7` список `attractors7` перечисляет весь образ эволюции.
    Единственность индекса каждого состояния даёт `attractors7_injective`. -/
theorem ring7_reachable_iff_attractor (t : Nat) (ht : 7 ≤ t) (v : Fin 128) :
    (∃ u : Fin 128, evolRing7 t u = v) ↔ ∃ k : Fin 15, attractors7 k = v := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨k, hk⟩ := ring7_capacity_bound_all_time t ht u
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact ring7_attractors_reachable t k

/-- Число различных достижимых состояний. Каждое возможное конечное состояние
    встречается в `List.finRange 128` ровно один раз. -/
def ring7ImageSize (t : Nat) : Nat :=
  (List.finRange 128).countP (fun v => decide (∃ u : Fin 128, evolRing7 t u = v))

/-- При каждом `t ≥ 7` образ эволюции содержит ровно 15 состояний. -/
theorem ring7_exact_image_size (t : Nat) (ht : 7 ≤ t) : ring7ImageSize t = 15 := by
  unfold ring7ImageSize
  calc
    _ = (List.finRange 128).countP (fun v => decide (∃ k : Fin 15, attractors7 k = v)) := by
      apply List.countP_congr
      intro v _
      simpa only [decide_eq_true_eq] using ring7_reachable_iff_attractor t ht v
    _ = 15 := by decide

/-- С момента `s` сдвиг на положительное число тактов `p` сохраняет состояние
    каждой орбиты во все моменты `t ≥ s`. -/
def Ring7PeriodicFrom (s p : Nat) : Prop :=
  0 < p ∧ ∀ t : Nat, s ≤ t → ∀ u : Fin 128, evolRing7 (t + p) u = evolRing7 t u

/-- 7 — наименьший момент, с которого возможен общий положительный период. -/
theorem ring7_minimal_preperiod :
    (∃ p : Nat, Ring7PeriodicFrom 7 p) ∧
    ∀ s p : Nat, Ring7PeriodicFrom s p → 7 ≤ s := by
  refine ⟨⟨14, by decide, evolRing7_period14⟩, ?_⟩
  intro s p hp
  by_cases hs : 7 ≤ s
  · exact hs
  · obtain ⟨hpos, hperiod⟩ := hp
    have atSix : evolRing7 6 5 = 88 := by decide
    have outside : ∀ k : Fin 15, (88 : Fin 128) ≠ attractors7 k := by decide
    obtain ⟨k, hk⟩ := ring7_capacity_bound_all_time (6 + p) (by omega) 5
    rw [hperiod 6 (by omega) 5, atSix] at hk
    exact False.elim (outside k hk)

/-- Каждый общий период при любом начале периодичности кратен 14.
    На орбите входа 1 проверяем все остатки сдвига от 0 до 13. -/
theorem ring7_period_dvd (s p : Nat) (h : Ring7PeriodicFrom s p) : 14 ∣ p := by
  have hreturn : ∀ r : Fin 14,
      evolRing7 (7 + r.val) 1 = evolRing7 7 1 → r.val = 0 := by decide
  -- Момент 7 + 14*s лежит после начала периодичности и имеет ту же фазу, что и 7.
  have hlate := h.2 (7 + 14 * s) (by omega) 1
  have heq : evolRing7 (7 + p) 1 = evolRing7 7 1 := calc
    evolRing7 (7 + p) 1 = evolRing7 (7 + p + 14 * s) 1 := (evolRing7_add_mul14 s p 1).symm
    _ = evolRing7 (7 + 14 * s) 1 := by
      rw [Nat.add_right_comm 7 p]
      exact hlate
    _ = evolRing7 7 1 := by simpa using evolRing7_add_mul14 s 0 1
  have hred : evolRing7 (7 + p) 1 = evolRing7 (7 + p % 14) 1 := by
    simpa using evolRing7_reduce (7 + p) (by omega) 1
  have hmod := hreturn ⟨p % 14, Nat.mod_lt _ (by decide)⟩ (hred.symm.trans heq)
  exact Nat.dvd_of_mod_eq_zero hmod

/-- 14 — общий период с момента 7 и наименьший положительный общий период
    среди всех возможных моментов начала периодичности. -/
theorem ring7_minimal_common_period :
    Ring7PeriodicFrom 7 14 ∧ ∀ s p : Nat, Ring7PeriodicFrom s p → 14 ≤ p := by
  refine ⟨⟨by decide, evolRing7_period14⟩, ?_⟩
  intro s p h
  exact Nat.le_of_dvd h.1 (ring7_period_dvd s p h)

-- ============================================================================
-- 3. ПОЛНЫЙ ПРИЧИННЫЙ НОСИТЕЛЬ `D_t^(7) = ℤ_7` ДЛЯ ВСЕХ `t ≥ 7`
-- ============================================================================

/-- Таблица явных свидетелей существенности `(r : Fin 14, j : Fin 7) ↦ u : Fin 128`. -/
def witnessEss7 (r : Fin 14) (j : Fin 7) : Fin 128 :=
  match r.val, j.val with
  |  0, 0 => ⟨  4, by decide⟩
  |  0, 1 => ⟨  0, by decide⟩
  |  0, 2 => ⟨  0, by decide⟩
  |  0, 3 => ⟨  1, by decide⟩
  |  0, 4 => ⟨  0, by decide⟩
  |  0, 5 => ⟨  1, by decide⟩
  |  0, 6 => ⟨  2, by decide⟩
  |  1, 0 => ⟨  4, by decide⟩
  |  1, 1 => ⟨  0, by decide⟩
  |  1, 2 => ⟨  0, by decide⟩
  |  1, 3 => ⟨  0, by decide⟩
  |  1, 4 => ⟨  0, by decide⟩
  |  1, 5 => ⟨  0, by decide⟩
  |  1, 6 => ⟨  5, by decide⟩
  |  2, 0 => ⟨  4, by decide⟩
  |  2, 1 => ⟨  0, by decide⟩
  |  2, 2 => ⟨  1, by decide⟩
  |  2, 3 => ⟨  1, by decide⟩
  |  2, 4 => ⟨  1, by decide⟩
  |  2, 5 => ⟨  0, by decide⟩
  |  2, 6 => ⟨  0, by decide⟩
  |  3, 0 => ⟨  0, by decide⟩
  |  3, 1 => ⟨  0, by decide⟩
  |  3, 2 => ⟨  0, by decide⟩
  |  3, 3 => ⟨  2, by decide⟩
  |  3, 4 => ⟨  1, by decide⟩
  |  3, 5 => ⟨  0, by decide⟩
  |  3, 6 => ⟨  0, by decide⟩
  |  4, 0 => ⟨  4, by decide⟩
  |  4, 1 => ⟨  5, by decide⟩
  |  4, 2 => ⟨  0, by decide⟩
  |  4, 3 => ⟨  0, by decide⟩
  |  4, 4 => ⟨  1, by decide⟩
  |  4, 5 => ⟨  0, by decide⟩
  |  4, 6 => ⟨  2, by decide⟩
  |  5, 0 => ⟨ 10, by decide⟩
  |  5, 1 => ⟨  8, by decide⟩
  |  5, 2 => ⟨  0, by decide⟩
  |  5, 3 => ⟨  0, by decide⟩
  |  5, 4 => ⟨  0, by decide⟩
  |  5, 5 => ⟨  0, by decide⟩
  |  5, 6 => ⟨  0, by decide⟩
  |  6, 0 => ⟨  0, by decide⟩
  |  6, 1 => ⟨  5, by decide⟩
  |  6, 2 => ⟨  0, by decide⟩
  |  6, 3 => ⟨  2, by decide⟩
  |  6, 4 => ⟨  2, by decide⟩
  |  6, 5 => ⟨  1, by decide⟩
  |  6, 6 => ⟨  0, by decide⟩
  |  7, 0 => ⟨  0, by decide⟩
  |  7, 1 => ⟨  0, by decide⟩
  |  7, 2 => ⟨  0, by decide⟩
  |  7, 3 => ⟨  0, by decide⟩
  |  7, 4 => ⟨  4, by decide⟩
  |  7, 5 => ⟨  1, by decide⟩
  |  7, 6 => ⟨  0, by decide⟩
  |  8, 0 => ⟨  4, by decide⟩
  |  8, 1 => ⟨  5, by decide⟩
  |  8, 2 => ⟨  1, by decide⟩
  |  8, 3 => ⟨  0, by decide⟩
  |  8, 4 => ⟨  0, by decide⟩
  |  8, 5 => ⟨  1, by decide⟩
  |  8, 6 => ⟨  0, by decide⟩
  |  9, 0 => ⟨  0, by decide⟩
  |  9, 1 => ⟨ 13, by decide⟩
  |  9, 2 => ⟨ 11, by decide⟩
  |  9, 3 => ⟨  0, by decide⟩
  |  9, 4 => ⟨  0, by decide⟩
  |  9, 5 => ⟨  0, by decide⟩
  |  9, 6 => ⟨  0, by decide⟩
  | 10, 0 => ⟨  0, by decide⟩
  | 10, 1 => ⟨  0, by decide⟩
  | 10, 2 => ⟨  3, by decide⟩
  | 10, 3 => ⟨  0, by decide⟩
  | 10, 4 => ⟨  1, by decide⟩
  | 10, 5 => ⟨  1, by decide⟩
  | 10, 6 => ⟨  2, by decide⟩
  | 11, 0 => ⟨  0, by decide⟩
  | 11, 1 => ⟨  0, by decide⟩
  | 11, 2 => ⟨  0, by decide⟩
  | 11, 3 => ⟨  0, by decide⟩
  | 11, 4 => ⟨  0, by decide⟩
  | 11, 5 => ⟨  3, by decide⟩
  | 11, 6 => ⟨  2, by decide⟩
  | 12, 0 => ⟨  0, by decide⟩
  | 12, 1 => ⟨  8, by decide⟩
  | 12, 2 => ⟨  9, by decide⟩
  | 12, 3 => ⟨  1, by decide⟩
  | 12, 4 => ⟨  0, by decide⟩
  | 12, 5 => ⟨  0, by decide⟩
  | 12, 6 => ⟨  2, by decide⟩
  | 13, 0 => ⟨  0, by decide⟩
  | 13, 1 => ⟨  0, by decide⟩
  | 13, 2 => ⟨  1, by decide⟩
  | 13, 3 => ⟨  3, by decide⟩
  | 13, 4 => ⟨  0, by decide⟩
  | 13, 5 => ⟨  0, by decide⟩
  | _,  _ => ⟨  0, by decide⟩

/-- Конечный сертификат (14 × 7 = 98 пар): на всем периоде `t ∈ [7..20]`
    каждая из 7 входных координат причинно влияет на `obs0`. -/
theorem ring7_essential_base :
    ∀ (r : Fin 14) (j : Fin 7),
      let u := witnessEss7 r j
      obs0 (evolRing7 (7 + r.val) u) ≠ obs0 (evolRing7 (7 + r.val) (flipBit7 j u)) := by
  decide

/-- Теорема 2 (персистентная существенность всех 7 бит для ВСЕХ `t ≥ 7`):
    для любого `t ≥ 7` и любой координаты `j ∈ ℤ_7` существует пара конфигураций,
    различающихся только в бите `j` и дающих разные выходы в ячейке `0`. -/
theorem ring7_all_bits_essential_all_time (t : Nat) (ht : t ≥ 7) (j : Fin 7) :
    ∃ u : Fin 128, obs0 (evolRing7 t u) ≠ obs0 (evolRing7 t (flipBit7 j u)) := by
  let r : Fin 14 := ⟨(t - 7) % 14, Nat.mod_lt (t - 7) (by decide)⟩
  let u := witnessEss7 r j
  refine ⟨u, ?_⟩
  rw [evolRing7_reduce t ht u, evolRing7_reduce t ht (flipBit7 j u)]
  exact ring7_essential_base r j

/-- Главная теорема (персистентное расцепление ёмкости и причинного носителя на `ℤ_7`):
    для ВСЕХ `t ≥ 7` состояние сжимается в 15 значений (`C_t^(7) = 4 < 7`), но все 7 входных
    координат навсегда остаются причинно существенными (`D_t^(7) = ℤ_7`). -/
theorem ring7_persistent_decoupling (t : Nat) (ht : t ≥ 7) :
    (∀ u : Fin 128, ∃ k : Fin 15, evolRing7 t u = attractors7 k) ∧
    (∀ j : Fin 7, ∃ u : Fin 128, obs0 (evolRing7 t u) ≠ obs0 (evolRing7 t (flipBit7 j u))) :=
  ⟨fun u => ring7_capacity_bound_all_time t ht u,
   fun j => ring7_all_bits_essential_all_time t ht j⟩

-- ============================================================================
-- 4. КОНТРАСТ С ЛИНЕЙНЫМ ПРАВИЛОМ RULE 90 НА КОЛЬЦЕ `ℤ_8`
-- ============================================================================

/-- Один шаг линейного правила Rule 90 (`l ⊕ r`) на кольце `ℤ_8`. -/
def stepRing8_r90 (u : Fin 256) : Fin 256 :=
  let c := u.val
  let l := ((c <<< 1) ||| (c >>> 7)) &&& 255
  let r := ((c >>> 1) ||| ((c &&& 1) <<< 7)) &&& 255
  ⟨(l ^^^ r) &&& 255, Nat.lt_of_le_of_lt Nat.and_le_right (by decide : 255 < 256)⟩

def evolRing8_r90 : Nat → Fin 256 → Fin 256
  | 0,     u => u
  | t + 1, u => stepRing8_r90 (evolRing8_r90 t u)

/-- Линейный Rule 90 на `ℤ_8` полностью схлопывается в нулевую конфигурацию за 4 такта (`C_t = 0, D_t = ∅`). -/
theorem rule90_ring8_collapses_at_4 :
    ∀ u : Fin 256, evolRing8_r90 4 u = ⟨0, by decide⟩ := by
  decide

end Rule110RingDecoupling
