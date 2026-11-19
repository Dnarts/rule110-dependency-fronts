import Bridge
import Rule110FrontGlue

namespace Rails.EtherWedge
open Rule110Complete Rule110Fin1320Bridge Rule110LocalWindow Rule110FrontGlue Rule110Ether
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

inductive Phase | a | b | c deriving DecidableEq
private def k : Phase → Int | .a => 0 | .b => 3 | .c => 5
private def d : Phase → Int | .a => 12 | .b => 12 | .c => 6
private def E (z : Int) : Config := fun x => ether (x+z)
private theorem ev (t : Nat) (z x : Int) : evolve t (E z) x = ether (x+z+4*t) := by
  rw [show E z = shift (-z) ether by funext j; simp [E,shift]]
  rw [evolve_shift, evolve_ether]
  unfold shift
  congr 1 <;> omega
private theorem per (x y : Int) (h : x%14=y%14) : ether x = ether y := by
  unfold ether
  rw [h]
private def initial : Phase → V
  | .a => 0xec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8eb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23e#5520
  | .b => 0x7d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d90f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647#5520
  | .c => 0x1f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f657d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91#5520
private def snap : Phase → V
  | .a => 0xec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb3afb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23ec8fb23eec8fb23ec8fb23ec8fb23ec8fb23ec8fb23#5520
  | .b => 0x7d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d9647d91f647d91f6591f647d91f647d91f647d91f647d7c7d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f6477d91f647d91f647d91f647d91f647d91f64#5520
  | .c => 0x1f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f6591f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f64647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91f647d91df647d91f647d91f647d91f647d91f647d9#5520
private theorem snapshot (p : Phase) : run 210 (initial p) = snap p := by cases p <;> decide +kernel
private def before (p : Phase) (right : Bool) := k p + if right then d p else 0
private def after (p : Phase) (right : Bool) := k p + if right then 0 else d p
private def lo (r : Bool) : Int := if r then 40 else -120
private def hi (r : Bool) : Int := if r then 155 else -50
private def wall (p : Phase) (r : Bool) : Config := fun x =>
  if x < lo r then E (before p r) x else if hi r < x then E (after p r) x else line (snap p) x
private theorem base (p : Phase) :
    evolve 210 (flipZero (E (k p))) = splice 0 (wall p false) (wall p true) := by
  funext x
  by_cases h : -220 ≤ x ∧ x ≤ 220
  · have eq := evolve_agree_window 210 (flipZero (E (k p))) (line (initial p)) x (by
      intro j hj hk
      apply finite_interval (fun z => flipZero (E (k p)) z = line (initial p) z) (-430) 861 _ j <;> try omega
      cases p <;> decide +kernel)
    rw [eq, ← line_run, snapshot]
    apply finite_interval (fun z => line (snap p) z = splice 0 (wall p false) (wall p true) z) (-220) 441 _ x <;> try omega
    cases p <;> decide +kernel
  · rw [outer _ _ _ (by omega),ev]
    by_cases hx : x ≤ 0
    · simp [splice,wall,lo,before,E,hx,show x < -120 by omega]
      apply per; omega
    · simp [splice,wall,lo,hi,after,E,hx,show ¬x < 40 by omega,show 155 < x by omega]
      apply per; omega

private def period (r : Bool) : Nat := if r then 3 else 4
private def delta (r : Bool) : Int := if r then 2 else -2
private theorem ret (p : Phase) (r : Bool) :
    evolve (period r) (wall p r) = shift (delta r) (wall p r) := by
  funext x
  by_cases hl : x < lo r - 5
  · rw [evolve_agree_window _ _ (E (before p r)) x (by
      intro j hj hk
      have : j < lo r := by cases r <;> simp [period] at * <;> omega
      simp [wall,this]), ev]
    have h : x-delta r < lo r := by cases r <;> simp [delta] at * <;> omega
    simp only [shift,wall,h,ite_true,E]
    apply per
    cases r <;> simp [delta,period] <;> omega
  by_cases hr : hi r + 5 < x
  · have ord : lo r ≤ hi r := by cases r <;> decide
    rw [evolve_agree_window _ _ (E (after p r)) x (by
      intro j hj hk
      have : hi r < j := by cases r <;> simp [period] at * <;> omega
      simp [wall,this,show ¬j < lo r by omega]), ev]
    have h : hi r < x-delta r := by cases r <;> simp [delta] at * <;> omega
    simp only [shift,wall,h,show ¬x-delta r < lo r by omega,ite_false,ite_true,E]
    apply per
    cases r <;> simp [delta,period] <;> omega
  cases r
  · apply finite_interval (fun z => evolve 4 (wall p false) z = shift (-2) (wall p false) z) (-125) 81 _ x <;> try {simp [lo,hi] at *; omega}
    cases p <;> decide +kernel
  · apply finite_interval (fun z => evolve 3 (wall p true) z = shift 2 (wall p true) z) 35 126 _ x <;> try {simp [lo,hi] at *; omega}
    cases p <;> decide +kernel
private def inside (r : Bool) (n : Nat) (x : Int) : Prop :=
  if r then x-2*(↑(n/3):Int)+(↑(n%3):Int)<40
  else -50+(↑(n%4):Int)<x+2*(↑(n/4):Int)
private theorem inner (p : Phase) (r : Bool) (n : Nat) (x : Int) (h : inside r n x) :
    evolve n (wall p r) x = ether (x+k p+d p+4*n) := by
  let P := period r
  let u := n%P
  let q := n/P
  have hn : n = u+P*q := (Nat.mod_add_div n P).symm
  calc
    _ = evolve (u+P*q) (wall p r) x := congrArg (fun m => evolve m (wall p r) x) hn
    _ = _ := by
      rw [evolve_add,travelling_return _ _ _ (ret p r),evolve_shift]
      change evolve u (wall p r) (x-(q:Int)*delta r) = _
      rw [evolve_agree_window _ _ (E (k p + d p)) _ (by
        intro j hj hk
        cases r <;> simp [inside,u,q,P,period,delta] at h hj hk
        · simp [wall,lo,hi,after,show ¬j < -120 by omega,show -50 < j by omega]
        · simp [wall,lo,before,show j < 40 by omega]), ev]
      apply per
      cases r <;> simp [u,q,P,period,delta] <;> omega

private theorem glue (p : Phase) (n : Nat) :
    evolve (n+210) (flipZero (E (k p))) =
      splice 0 (evolve n (wall p false)) (evolve n (wall p true)) := by
  rw [evolve_add,base]
  apply evolve_splice (fun _ => 0) _ _ (by intro t; omega)
  intro t x hl hr
  rw [inner p false t x (by simp [inside]; omega),inner p true t x (by simp [inside]; omega)]

private theorem cover (z : Int) : ∃ p : Phase, ether (z+k p) ≠ ether (z+k p+d p) := by
  let j : Fin 14 := ⟨(z%14).toNat,by omega⟩
  have hj : (j.val:Int)=z%14 := by dsimp [j]; omega
  have tab : ∀ i : Fin 14,
      let hit := fun p => ether ((i.val:Int)+k p) ≠ ether ((i.val:Int)+k p+d p)
      hit .a ∨ hit .b ∨ hit .c := by decide
  have aux (p : Phase) (h : ether ((j.val:Int)+k p) ≠ ether ((j.val:Int)+k p+d p)) :
      ∃ p : Phase, ether (z+k p) ≠ ether (z+k p+d p) := by
    refine ⟨p,?_⟩
    rwa [per (z+k p) ((j.val:Int)+k p) (by omega),
      per (z+k p+d p) ((j.val:Int)+k p+d p) (by omega)]
  rcases tab j with h|h|h
  · exact aux .a h
  · exact aux .b h
  · exact aux .c h

theorem right_sector (t : Nat) (x : Int) (ht : 4000 ≤ t)
    (hl : -(((7*t)/30 : Nat):Int) ≤ x)
    (hr : x ≤ (↑(t-t/3):Int)-106) : Rule110KernelCert.EssentialAt t (-x) := by
  obtain ⟨p,hp⟩ := cover (x+4*t)
  apply essential (E (k p))
  let n := t-210
  have hn : n+210=t := by dsimp [n]; omega
  have h := glue p n
  rw [hn] at h
  rw [ev,h]
  have hy : splice 0 (evolve n (wall p false)) (evolve n (wall p true)) x =
      ether (x+k p+d p+4*n) := by
    by_cases hx : x ≤ 0
    · simpa only [splice,hx,ite_true] using inner p false n x (by simp [inside,n]; omega)
    · simpa only [splice,hx,ite_false] using inner p true n x (by simp [inside,n]; omega)
  rw [hy, per (x+k p+4*t) (x+4*t+k p) (by omega),
    per (x+k p+d p+4*n) (x+4*t+k p+d p) (by omega)]
  exact hp
#print axioms right_sector
theorem half_sector (t : Nat) (x : Int) (ht : 210 ≤ t)
    (hl : 60-((t/2 : Nat):Int) ≤ x)
    (hr : x ≤ (↑(t-t/3):Int)-106) : Rule110KernelCert.EssentialAt t (-x) := by
  obtain ⟨p,hp⟩ := cover (x+4*t)
  apply essential (E (k p))
  let n := t-210
  have hn : n+210=t := by dsimp [n]; omega
  have h := glue p n
  rw [hn] at h
  rw [ev,h]
  have hy : splice 0 (evolve n (wall p false)) (evolve n (wall p true)) x =
      ether (x+k p+d p+4*n) := by
    by_cases hx : x ≤ 0
    · simpa only [splice,hx,ite_true] using inner p false n x (by simp [inside,n]; omega)
    · simpa only [splice,hx,ite_false] using inner p true n x (by simp [inside,n]; omega)
  rw [hy, per (x+k p+4*t) (x+4*t+k p) (by omega),
    per (x+k p+d p+4*n) (x+4*t+k p+d p) (by omega)]
  exact hp
#print axioms half_sector
end Rails.EtherWedge
