/-!
# ContinuousSubject110

Четыре истории из §4.3 «110 OBSERVER» на бесконечной прямой с нулевым фоном.
В потоковой модели последовательность эпизодов задаётся извне, а регистр `q`
передаётся между эпизодами. Один эпизод состоит из четырёх шагов Rule 110,
записи обновлённого регистра в клетку −1 и пятого шага.
-/

namespace ContinuousSubject110

/-- Локальное правило Rule 110: f(l, c, r) = c ⊕ r ⊕ cr ⊕ lcr -/
def rule110 (l c r : Bool) : Bool :=
  xor (xor (xor c r) (c && r)) (l && c && r)

/-- Конфигурация бесконечной решётки -/
abbrev Grid := Int → Bool

/-- Один синхронный шаг эволюции Rule 110 -/
def step (g : Grid) : Grid :=
  fun i => rule110 (g (i - 1)) (g i) (g (i + 1))

/-- n шагов эволюции -/
def evolve : Nat → Grid → Grid
  | 0,     g => g
  | n + 1, g => evolve n (step g)

/-- Запись одного бита q в клетку pos (инжекция субъекта в среду) -/
def inject (pos : Int) (q : Bool) (g : Grid) : Grid :=
  fun i => if i = pos then q else g i

/-- Теорема 1 (Алгебраический гейт Rule 110, ур. 11 препринта):
    при левом соседе = 1 обновление клетки реализует точный XOR. -/
theorem rule110_xor_gate (z k : Bool) :
    rule110 true z k = xor z k := by
  cases z <;> cases k <;> rfl

/-- Данные одного эпизода. Поля фиксируют входы локального гейта;
    глобальное слияние конкретных пар доказывается ниже. -/
structure Episode where
  sensorZ  : Bool  -- показание датчика Z = U_2(3) на такте 2
  contextK : Bool  -- локальный контекст K = U_4(0) на такте 4
  mergedU4 : Grid  -- слившаяся конфигурация среды на такте 4
  h_left   : mergedU4 (-2) = true
  h_right  : mergedU4 0 = contextK

/-- Непрерывный субъект: минимальный носитель D_dyn (1 бит пластичности) -/
structure Subject where
  q : Bool

/-- Шаг реального времени на одном эпизоде:
    1. Считывание датчика Z на такте 2 -> эндогенное обновление q' = q ⊕ Z.
    2. Сброс внешней истории (среда в состоянии mergedU4).
    3. Инжекция q' в клетку -1 и один штатный шаг Rule 110 -> выход в (-1). -/
def runEpisode (s : Subject) (ep : Episode) : Subject × Bool :=
  let q' := xor s.q ep.sensorZ
  let u5 := step (inject (-1) q' ep.mergedU4)
  ({ q := q' }, u5 (-1))

/-- Выход одного эпизода в точности равен (q ⊕ Z) ⊕ K -/
theorem runEpisode_output (s : Subject) (ep : Episode) :
    (runEpisode s ep).2 = xor (xor s.q ep.sensorZ) ep.contextK := by
  unfold runEpisode step inject
  simp [ep.h_left, ep.h_right, rule110_xor_gate]

/-- Потоковое исполнение на произвольной последовательности эпизодов.
    Возвращает финальное состояние субъекта и список реальных выходов. -/
def runStream (s : Subject) : List Episode → Subject × List Bool
  | [] => (s, [])
  | ep :: rest =>
      let (s', out) := runEpisode s ep
      let (sFinal, outs) := runStream s' rest
      (sFinal, out :: outs)

/-- Накопленная чётность показаний датчиков по истории эпизодов -/
def parity (q0 : Bool) (eps : List Episode) : Bool :=
  eps.foldl (fun acc ep => xor acc ep.sensorZ) q0

/-- Теорема 2 (Инвариант непрерывного субъекта):
    после любой конечной цепочки эпизодов внутреннее состояние субъекта
    в точности равно накопленной чётности q0 ⊕ Z_1 ⊕ ... ⊕ Z_n. -/
theorem stream_state_invariant (s : Subject) (eps : List Episode) :
    (runStream s eps).1.q = parity s.q eps := by
  induction eps generalizing s with
  | nil => rfl
  | cons ep rest ih =>
      simp only [runStream, runEpisode, parity, List.foldl]
      exact ih { q := xor s.q ep.sensorZ }

/-- Вспомогательная лемма о XOR с отрицанием -/
theorem xor_not_left (a b : Bool) : xor (!a) b = !(xor a b) := by
  cases a <;> cases b <;> rfl

/-- Теорема 3 (Контрфактическое вмешательство G5 — донорская подмена / инверсия):
    подмена внутреннего бита субъекта (q → !q) при ИДЕНТИЧНОЙ последовательности
    слившихся сред и входов детерминированно обращает КАЖДЫЙ последующий выход. -/
theorem donor_swap_flips_all_future_outputs (s : Subject) (eps : List Episode) :
    (runStream { q := !s.q } eps).2 = (runStream s eps).2.map (!·) := by
  induction eps generalizing s with
  | nil => rfl
  | cons ep rest ih =>
      have h_out :
          (runEpisode { q := !s.q } ep).2 = !((runEpisode s ep).2) := by
        rw [runEpisode_output, runEpisode_output, xor_not_left, xor_not_left]
      have h_state :
          (runEpisode { q := !s.q } ep).1 = { q := !(runEpisode s ep).1.q } := by
        simp only [runEpisode, xor_not_left]
      simp only [runStream, List.map, h_out, h_state]
      congr 1
      exact ih (runEpisode s ep).1

/-- Теорема 4 (Невозможность без D_dyn / критерий T1–T4):
    любой декодер без внутреннего состояния, видящий только слившуюся среду U_4,
    вынужден ошибаться хотя бы на одной из двух историй с разными q. -/
theorem no_stateless_decoder (ep : Episode) (q1 q2 : Bool) (hneq : q1 ≠ q2)
    (decoder : Grid → Bool) :
    decoder ep.mergedU4 ≠ (runEpisode { q := q1 } ep).2 ∨
    decoder ep.mergedU4 ≠ (runEpisode { q := q2 } ep).2 := by
  rw [runEpisode_output, runEpisode_output]
  cases q1 <;> cases q2 <;> cases ep.sensorZ <;> cases ep.contextK <;>
    cases h : decoder ep.mergedU4 <;> simp_all

/- === Привязка к 4 конструктивным свидетелям из §4.3 === -/

/-- Построение бесконечной конфигурации с нулевым фоном по 20-битному слову на [-6, 13] -/
def fromWord20 (bits : List Bool) : Grid :=
  fun i =>
    if -6 ≤ i ∧ i ≤ 13 then
      bits.getD (Int.toNat (i + 6)) false
    else
      false

/-- Строка (K,Y) = (0,0) из §4.3: 00000001100001000000. -/
def w00 : Grid := fromWord20
  [false,false,false,false,false,false,false,true,true,false,false,false,false,true,false,false,false,false,false,false]
/-- Строка (0,1): 00000001100101000000. -/
def w01 : Grid := fromWord20
  [false,false,false,false,false,false,false,true,true,false,false,true,false,true,false,false,false,false,false,false]
/-- Строка (1,0): 00010111010001000010. -/
def w10 : Grid := fromWord20
  [false,false,false,true,false,true,true,true,false,true,false,false,false,true,false,false,false,false,true,false]
/-- Строка (1,1): 00010111010101000010. -/
def w11 : Grid := fromWord20
  [false,false,false,true,false,true,true,true,false,true,false,true,false,true,false,false,false,false,true,false]

/-- Лемма о конечном носителе: нулевой фон вне [lo, hi] расширяется максимум на 1 за такт -/
theorem step_zero_outside {g : Grid} {lo hi : Int}
    (h : ∀ i, i < lo ∨ hi < i → g i = false) :
    ∀ i, i < lo - 1 ∨ hi + 1 < i → step g i = false := by
  intro i hi_out
  unfold step
  have hL : g (i - 1) = false := h (i - 1) (by omega)
  have hC : g i = false       := h i       (by omega)
  have hR : g (i + 1) = false := h (i + 1) (by omega)
  simp [hL, hC, hR, rule110]

theorem evolve_zero_outside (n : Nat) {g : Grid} {lo hi : Int}
    (h : ∀ i, i < lo ∨ hi < i → g i = false) :
    ∀ i, i < lo - n ∨ hi + n < i → evolve n g i = false := by
  induction n generalizing g lo hi with
  | zero =>
      intro i hi_out
      exact h i (by omega)
  | succ k ih =>
      intro i hi_out
      have h1 := step_zero_outside h
      exact ih h1 i (by omega)

theorem fromWord20_zero_outside (bits : List Bool) :
    ∀ i, i < -6 ∨ 13 < i → fromWord20 bits i = false := by
  intro i hi_out
  unfold fromWord20
  split
  · omega
  · rfl

private theorem outside_of_not_inside {lo hi i : Int} (h : ¬(lo ≤ i ∧ i ≤ hi)) :
    i < lo ∨ hi < i := by
  rcases Int.lt_or_le i lo with lt | le
  · exact .inl lt
  · exact .inr (Int.lt_of_not_ge (fun upper => h ⟨le, upper⟩))

/-- В каждой паре симметрическая разность начальных конфигураций равна {5}. -/
theorem initial_diff_only_at_five (i : Int) :
    (w00 i ≠ w01 i ↔ i = 5) ∧ (w10 i ≠ w11 i ↔ i = 5) := by
  rcases Decidable.em (-6 ≤ i ∧ i ≤ 13) with hin | hin
  · have inside : ∀ p : Fin 20, let j : Int := (p.val : Int) - 6
          (w00 j ≠ w01 j ↔ j = 5) ∧ (w10 j ≠ w11 j ↔ j = 5) := by decide
    let p : Fin 20 := ⟨(i + 6).toNat, by omega⟩
    have hp : (p.val : Int) - 6 = i := by simp [p]; omega
    simpa only [hp] using inside p
  · have hout := outside_of_not_inside hin
    clear hin
    have h5 : i ≠ 5 := by omega
    simp [w00, w01, w10, w11, fromWord20_zero_outside _ i hout, h5]

theorem initial_values :
    w00 5 = false ∧ w01 5 = true ∧ w10 5 = false ∧ w11 5 = true := by decide

/-- Полное слияние двух 20-битных слов на ВСЕЙ бесконечной прямой к такту 4:
    вне [-10, 17] оба равны false, внутри [-10, 17] проверяется конечным перебором. -/
theorem merge_on_line_4 (b1 b2 : List Bool)
    (h_mid : ∀ k : Fin 28,
      evolve 4 (fromWord20 b1) ((k.val : Int) - 10) =
      evolve 4 (fromWord20 b2) ((k.val : Int) - 10)) :
    ∀ i : Int, evolve 4 (fromWord20 b1) i = evolve 4 (fromWord20 b2) i := by
  intro i
  rcases Decidable.em (-10 ≤ i ∧ i ≤ 17) with hin | hin
  · let k : Fin 28 := ⟨Int.toNat (i + 10), by omega⟩
    have hk : (k.val : Int) - 10 = i := by simp [k]; omega
    simpa [hk] using h_mid k
  · have hout := outside_of_not_inside hin
    clear hin
    have h1 := evolve_zero_outside 4 (fromWord20_zero_outside b1) i (by omega)
    have h2 := evolve_zero_outside 4 (fromWord20_zero_outside b2) i (by omega)
    rw [h1, h2]

/-- Вычислительная проверка слияния обеих пар на всей бесконечной прямой (t = 4) -/
theorem merge_K0 : ∀ i : Int, evolve 4 w00 i = evolve 4 w01 i :=
  merge_on_line_4 _ _ (by decide)

theorem merge_K1 : ∀ i : Int, evolve 4 w10 i = evolve 4 w11 i :=
  merge_on_line_4 _ _ (by decide)

/-- Вычислительная проверка показаний датчика Z = U_2(3) и контекста K = U_4(0) -/
theorem sensor_values :
    evolve 2 w00 3 = false ∧
    evolve 2 w01 3 = true  ∧
    evolve 2 w10 3 = true  ∧
    evolve 2 w11 3 = false := by decide

theorem context_values :
    evolve 4 w00 0 = false ∧
    evolve 4 w01 0 = false ∧
    evolve 4 w10 0 = true  ∧
    evolve 4 w11 0 = true := by decide

theorem left_gate_values :
    evolve 4 w00 (-2) = true ∧ evolve 4 w01 (-2) = true ∧
    evolve 4 w10 (-2) = true ∧ evolve 4 w11 (-2) = true := by decide

/-- Конкретные конструктивные эпизоды из реальной эволюции Rule 110 -/
def ep00 : Episode where
  sensorZ  := evolve 2 w00 3
  contextK := evolve 4 w00 0
  mergedU4 := evolve 4 w00
  h_left   := by decide
  h_right  := rfl

def ep01 : Episode where
  sensorZ  := evolve 2 w01 3
  contextK := evolve 4 w01 0
  mergedU4 := evolve 4 w01
  h_left   := by decide
  h_right  := rfl

def ep10 : Episode where
  sensorZ  := evolve 2 w10 3
  contextK := evolve 4 w10 0
  mergedU4 := evolve 4 w10
  h_left   := by decide
  h_right  := rfl

def ep11 : Episode where
  sensorZ  := evolve 2 w11 3
  contextK := evolve 4 w11 0
  mergedU4 := evolve 4 w11
  h_left   := by decide
  h_right  := rfl

/-- Индексы четырёх предъявленных историй, в порядке (K,Y). -/
inductive Witness where
  | k0y0 | k0y1 | k1y0 | k1y1

def Witness.initial : Witness → Grid
  | .k0y0 => w00
  | .k0y1 => w01
  | .k1y0 => w10
  | .k1y1 => w11

def Witness.episode : Witness → Episode
  | .k0y0 => ep00
  | .k0y1 => ep01
  | .k1y0 => ep10
  | .k1y1 => ep11

/-- При нулевом начальном регистре пятый такт возвращает исходный бит Y. -/
theorem witness_return (w : Witness) :
    (runEpisode ⟨false⟩ w.episode).2 = w.initial 5 := by
  cases w <;> decide

def witnessFor : Bool → Bool → Witness
  | false, false => .k0y0
  | false, true  => .k0y1
  | true,  false => .k1y0
  | true,  true  => .k1y1

/-- При любом фиксированном K две истории стартуют с одним q = 0.
    Полные решётки перед записью совпадают, но требуемые выходы различны. -/
theorem concrete_no_stateless_decoder (k : Bool) (decoder : Grid → Bool) :
    let a := (witnessFor k false).episode
    let b := (witnessFor k true).episode
    a.mergedU4 = b.mergedU4 ∧
      (decoder a.mergedU4 ≠ (runEpisode ⟨false⟩ a).2 ∨
       decoder b.mergedU4 ≠ (runEpisode ⟨false⟩ b).2) := by
  dsimp only
  have merged : (witnessFor k false).episode.mergedU4 = (witnessFor k true).episode.mergedU4 := by
    cases k
    · exact funext merge_K0
    · exact funext merge_K1
  refine ⟨merged, ?_⟩
  rw [witness_return, witness_return, ← merged]
  have y0 : (witnessFor k false).initial 5 = false := by cases k <;> decide
  have y1 : (witnessFor k true).initial 5 = true := by cases k <;> decide
  rw [y0, y1]
  cases decoder (witnessFor k false).episode.mergedU4 <;> decide

/-- На пятом такте клетка −4 равна 1 при обеих записях. В любой из
    четырёх начальных конфигураций она равна 0. Следующий эпизод
    задаётся внешней средой, даже если координаты входа и выхода совпадают. -/
theorem witness_restart_coordinate (current next : Witness) (bit : Bool) :
    step (inject (-1) bit current.episode.mergedU4) (-4) = true ∧
    next.initial (-4) = false := by
  constructor
  · cases current <;> cases bit <;> decide
  · cases next <;> decide

/-- Любой конечный список строк таблицы задаёт вычислимый поток эпизодов. -/
theorem concrete_stream_invariants (s : Subject) (worlds : List Witness) :
    (runStream s (worlds.map Witness.episode)).1.q = parity s.q (worlds.map Witness.episode) ∧
    (runStream ⟨!s.q⟩ (worlds.map Witness.episode)).2 =
      (runStream s (worlds.map Witness.episode)).2.map (!·) :=
  ⟨stream_state_invariant _ _, donor_swap_flips_all_future_outputs _ _⟩

/-- Первые n предъявленных эпизодов бесконечного внешнего расписания. -/
def witnessPrefix (worlds : Nat → Witness) (n : Nat) : List Episode :=
  (List.range n).map (fun i => (worlds i).episode)

/-- Регистр перед n-м эпизодом (нумерация с нуля). -/
def subjectAt (s : Subject) (worlds : Nat → Witness) (n : Nat) : Subject :=
  (runStream s (witnessPrefix worlds n)).1

def outputAt (s : Subject) (worlds : Nat → Witness) (n : Nat) : Bool :=
  (runEpisode (subjectAt s worlds n) (worlds n).episode).2

theorem parity_not_initial (q : Bool) (eps : List Episode) :
    parity (!q) eps = !(parity q eps) := by
  induction eps generalizing q with
  | nil => rfl
  | cons ep rest ih =>
    change parity (xor (!q) ep.sensorZ) rest = !(parity (xor q ep.sensorZ) rest)
    rw [xor_not_left, ih]

/-- Поточечный закон для одного и того же бесконечного расписания:
    перед каждым эпизодом регистр равен чётности его конечного прошлого,
    а инверсия начального бита обращает действительный выход этого эпизода. -/
theorem infinite_witness_stream (s : Subject) (worlds : Nat → Witness) (n : Nat) :
    (subjectAt s worlds n).q = parity s.q (witnessPrefix worlds n) ∧
    outputAt ⟨!s.q⟩ worlds n = !(outputAt s worlds n) := by
  constructor
  · exact stream_state_invariant _ _
  · simp only [outputAt, runEpisode_output, subjectAt, stream_state_invariant,
      parity_not_initial, xor_not_left]


#print axioms rule110_xor_gate
#print axioms runEpisode_output
#print axioms stream_state_invariant
#print axioms xor_not_left
#print axioms donor_swap_flips_all_future_outputs
#print axioms no_stateless_decoder
#print axioms step_zero_outside
#print axioms evolve_zero_outside
#print axioms fromWord20_zero_outside
#print axioms outside_of_not_inside
#print axioms initial_diff_only_at_five
#print axioms initial_values
#print axioms merge_on_line_4
#print axioms merge_K0
#print axioms merge_K1
#print axioms sensor_values
#print axioms context_values
#print axioms left_gate_values
#print axioms witness_return
#print axioms concrete_no_stateless_decoder
#print axioms witness_restart_coordinate
#print axioms concrete_stream_invariants
#print axioms parity_not_initial
#print axioms infinite_witness_stream

end ContinuousSubject110
