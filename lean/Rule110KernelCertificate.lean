/-!
# Rule 110: directly computed finite boundary obligations

Both checkers compute their data directly from the transition rule. The
BitVec / Fin correspondence is proved in Rule110BitVecBridge. The two
Boolean results have been evaluated with #eval; kernel proofs of their
truth remain open. See Rule110KernelAudit.md.
-/

namespace Rule110KernelCert

abbrev RingBV := BitVec 1320

/-- Cyclic left rotation by one. Bit index i is physical coordinate i. -/
def rotL1 (u : RingBV) : RingBV :=
  (u <<< 1) ||| (u >>> 1319)

/-- Cyclic right rotation by one. -/
def rotR1 (u : RingBV) : RingBV :=
  (u >>> 1) ||| (u <<< 1319)

/-- Cyclic left rotation; used only for 0 < d < 1320. -/
def rotL (d : Nat) (u : RingBV) : RingBV :=
  (u <<< d) ||| (u >>> (1320 - d))

/-- Cyclic right rotation; used only for 0 < d < 1320. -/
def rotR (d : Nat) (u : RingBV) : RingBV :=
  (u >>> d) ||| (u <<< (1320 - d))

/-- Rule 110 in algebraic normal form. -/
def ringStepBV (u : RingBV) : RingBV :=
  let l := rotL1 u
  let r := rotR1 u
  (u ^^^ r) ^^^ ((u &&& r) ^^^ (l &&& u &&& r))

/-- Evolution uses the same t+1 = step (evolve t) convention as Rule110Complete. -/
def ringEvolveBV : Nat → RingBV → RingBV
  | 0, u => u
  | t + 1, u => ringStepBV (ringEvolveBV t u)

/-- Flip bit 660, corresponding to spatial coordinate 0. -/
def flipCenterBV (u : RingBV) : RingBV :=
  u ^^^ (1#1320 <<< 660)

/-- Periodic word, with physical coordinate i - 660 and phase ph. -/
def initRingBV (word : List Bool) (ph : Nat) : RingBV :=
  let len := word.length
  if len == 0 then 0#1320
  else
    (List.range 1320).foldl (init := 0#1320) fun acc i =>
      let idx := ((i + 660 + ph) % len)
      if word.getD idx false then acc ||| (1#1320 <<< i) else acc

/-- All 20 left phases from three primitive words. -/
def leftPhaseSpecs : List (List Bool × Nat) :=
  let w1 := [false, false, false, true, true, true, true, false, false, true]
  let w2 := [true, false, true, true]
  let w3 := [false, false, true, false, true, true]
  (List.range 10).map (fun ph => (w1, ph)) ++
  (List.range 4).map (fun ph => (w2, ph)) ++
  (List.range 6).map (fun ph => (w3, ph))

/-- Six selected right phases. -/
def rightPhaseSpecs : List (List Bool × Nat) :=
  [ ([false, true], 0),
    ([false, false, true], 0),
    ([false, false, false, false, true], 3),
    ([false, false, true, false, true], 2),
    ([false, false, true, true, true], 1),
    ([false, false, false, false, false, false, true, false, false, true], 4) ]

/-- Evolve once through time, retaining exactly `len+1` states from `start`.
   This bounded loop avoids a well-founded-recursion proof obligation. -/
def collectTraj (start len : Nat) (b0 y0 : RingBV) : Array (RingBV × RingBV) := Id.run do
  let mut b := b0
  let mut y := y0
  let mut acc : Array (RingBV × RingBV) := #[]
  for t in [:start + len + 1] do
    if t >= start then
      acc := acc.push (b, y)
    if t < start + len then
      b := ringStepBV b
      y := ringStepBV y
  return acc

/-- e_t = t - floor(t/3). -/
def edgeNat (t : Nat) : Nat := t - t / 3

/-- Reverses the order of the extracted high-to-low bits, indexed by depth. -/
def extractDown (u : RingBV) (hi w : Nat) : Nat :=
  (List.range w).foldl (init := 0) fun acc k =>
    if u.getLsbD (hi - k) then acc ||| (1 <<< k) else acc

/-- Extract bits low-to-high, indexed by depth. -/
def extractUp (u : RingBV) (lo w : Nat) : Nat :=
  (List.range w).foldl (init := 0) fun acc k =>
    if u.getLsbD (lo + k) then acc ||| (1 <<< k) else acc

/-- The 20 left phases have full-ring background shift, depth-167
    30-step Y recurrence, and width-106 base coverage. -/
def verifyLeftInKernel : Bool :=
  let trajs := leftPhaseSpecs.map fun (w, ph) =>
    let b0 := initRingBV w ph
    collectTraj 300 60 b0 (flipCenterBV b0)
  let bgAndTileOk := trajs.all fun tr =>
    (List.range 30).all fun idx =>
      let t := 300 + idx
      let (bOld, yOld) := tr.getD idx (0#1320, 0#1320)
      let (bNew, yNew) := tr.getD (idx + 30) (0#1320, 0#1320)
      let bgOk := bNew == rotL 20 bOld
      let eOld := 660 + edgeNat t
      let eNew := 660 + edgeNat (t + 30)
      let tileOk := extractDown yOld eOld 167 == extractDown yNew eNew 167
      bgOk && tileOk
  let fullMask106 : Nat := (1 <<< 106) - 1
  let covOk := (List.range 30).all fun idx =>
    let t := 300 + idx
    let eOld := 660 + edgeNat t
    let unionMask := trajs.foldl (init := 0) fun acc tr =>
      let (bOld, yOld) := tr.getD idx (0#1320, 0#1320)
      acc ||| extractDown (bOld ^^^ yOld) eOld 106
    unionMask == fullMask106
  bgAndTileOk && covOk

/-- The six right phases have full-ring background shift, depth-8
    40-step Y recurrence, and width-8 base coverage. -/
def verifyRightInKernel : Bool :=
  let trajs := rightPhaseSpecs.map fun (w, ph) =>
    let b0 := initRingBV w ph
    collectTraj 300 80 b0 (flipCenterBV b0)
  let bgAndTileOk := trajs.all fun tr =>
    (List.range 40).all fun idx =>
      let t := 300 + idx
      let (bOld, yOld) := tr.getD idx (0#1320, 0#1320)
      let (bNew, yNew) := tr.getD (idx + 40) (0#1320, 0#1320)
      let bgOk := bNew == rotR 40 bOld
      let sOld := 660 - t
      let sNew := 660 - (t + 40)
      let tileOk := extractUp yOld sOld 8 == extractUp yNew sNew 8
      bgOk && tileOk
  let fullMask8 : Nat := 0xff
  let covOk := (List.range 40).all fun idx =>
    let t := 300 + idx
    let sOld := 660 - t
    let unionMask := trajs.foldl (init := 0) fun acc tr =>
      let (bOld, yOld) := tr.getD idx (0#1320, 0#1320)
      acc ||| extractUp (bOld ^^^ yOld) sOld 8
    unionMask == fullMask8
  bgAndTileOk && covOk

end Rule110KernelCert
