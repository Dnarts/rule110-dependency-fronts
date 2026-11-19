import Crystal50Wedge
import Crystal50Packed
import Crystal50Seam
namespace Rails.Crystal50Wedge
open Rule110Complete Rule110LocalWindow Rule110Fin1320Bridge Crystal50Graph

private abbrev tm (j : Nat) := 2450+2*j
private abbrev a (j : Nat) : Int := -350-(j:Int)
private def pack (n : Nat) (g : Nat → Bool) :=
  (List.range n).foldl (fun z k => z + (g k).toNat * 2^k) 0
private theorem ps (n) (g : Nat → Bool) :
    pack (n+1) g = pack n g + (g n).toNat * 2^n := by simp [pack,List.range_succ]
private theorem pb (n) (g : Nat → Bool) : pack n g < 2^n := by
  induction n with
  | zero => change 0 < 1; decide
  | succ n ih => rw [ps,Nat.pow_succ]; cases h : g n <;> simp at * <;> omega
private theorem pbit (n) (g : Nat → Bool) (k) (hk : k<n) :
    (pack n g).testBit k = g k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [ps,Nat.add_comm,Nat.mul_comm (g n).toNat,Nat.testBit_two_pow_mul_add _ (pb n g)]
    split
    · exact ih ‹_›
    · have : k=n := by omega
      subst k
      cases h : g n <;> simp

private theorem bitShrink (s k : Nat) : (shrink s).testBit k =
    f (s.testBit k) (s.testBit (k+1)) (s.testBit (k+2)) := by
  simp only [shrink,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftRight]
  rw [Nat.add_comm 1 k,Nat.add_comm 2 k]
  cases s.testBit k <;> cases s.testBit (k+1) <;> cases s.testBit (k+2) <;> rfl

private theorem shrinkRead (m v : Nat) (C : Config) (b : Int)
    (h : ∀ k : Nat, k<m+2 → C (b+k) = v.testBit k) (k : Nat) (hk : k<m) :
    step C (b+1+k) = (shrink v).testBit k := by
  unfold step
  rw [bitShrink,show b+1+(k:Int)-1=b+k by omega,
    show b+1+(k:Int)+1=b+((k+2:Nat):Int) by omega,
    show b+1+(k:Int)=b+((k+1:Nat):Int) by omega,h _ (by omega),h _ (by omega),h _ (by omega)]

private def graphs : Phase → Array Row
  | .p0 => graph0
  | .p1 => graph1
  | .p2 => graph2
  | .p3 => graph3
  | .p7 => graph7
  | .p9 => graph9
private def row (p : Phase) (j : Nat) := (graphs p)[j%50]!
private def start : Phase → Nat
  | .p0 => 47 | .p1 => 26 | .p2 => 87 | .p3 => 85 | .p7 => 18 | .p9 => 19
private theorem start_mem (p) : start p < (row p 0).size := by cases p <;> decide +kernel
private theorem start_word (p) : pack 16 (fun k => line (snap p) (-350+(k:Int))) =
    entry (row p 0) (start p) % 65536 := by
  cases p
  · exact base0
  · exact base1
  · exact base2
  · exact base3
  · exact base7
  · exact base9
private theorem closedRow (p) (j : Nat) : valid p (j%50) (row p j) (row p (j+1)) = true := by
  unfold row
  rw [show (j+1)%50=(j%50+1)%50 by omega]
  cases p
  · exact closed0 ⟨j%50,by omega⟩
  · exact closed1 ⟨j%50,by omega⟩
  · exact closed2 ⟨j%50,by omega⟩
  · exact closed3 ⟨j%50,by omega⟩
  · exact closed7 ⟨j%50,by omega⟩
  · exact closed9 ⟨j%50,by omega⟩
private abbrev word (p : Phase) (j i : Nat) := entry (row p j) i % 65536
private abbrev input (p : Phase) (j i : Nat) (r : Bool) :=
  ctx p (j%50) + word p j i * 16 + r.toNat * 1048576
private abbrev output (p : Phase) (j i : Nat) (r : Bool) := shrink (shrink (input p j i r))
private theorem transition (p : Phase) (j i : Nat) (hi : i < (row p j).size) (r : Bool) :
    ∃ z < (row p (j+1)).size,
      (output p j i r).testBit 0 = Cm p (tm j+2) (a j-2) ∧
      ((output p j i r) >>> 1)%65536 = word p (j+1) z := by
  have h := closedRow p j
  unfold valid at h
  have hi' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have hr := List.all_eq_true.mp hi' r.toNat (by cases r <;> decide)
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hr
  refine ⟨_, hr.1.1, hr.1.2.trans ?_,hr.2⟩
  unfold Cm
  congr 1
  · rw [show (2452+2*(j%50))%50=(tm j+2)%50 by dsimp [tm]; omega]
  · dsimp [a]; omega

private def Medium (p : Phase) (j : Nat) := ∀ x : Int,
  -(tm j:Int)+1300 ≤ x → x < a j → Y p (tm j) x = Cm p (tm j) x
private def Window (p : Phase) (j i : Nat) := ∀ k : Nat, k<16 →
    Y p (tm j) (a j+k) = (word p j i).testBit k
private theorem inputRead (p : Phase) (j i : Nat) (hm : Medium p j) (hw : Window p j i)
    (k : Nat) (hk : k<21) :
    Y p (tm j) (a j-4+k) = (input p j i (Y p (tm j) (a j+16))).testBit k := by
  let g := fun k : Nat => Cm p (tm (j%50)) (a (j%50)-4+k)
  let w := word p j i
  let r := Y p (tm j) (a j+16)
  have hc : ctx p (j%50) = pack 4 g := rfl
  have hwlt : w<65536 := Nat.mod_lt _ (by decide)
  have hclt := pb 4 g
  change _ = (ctx p (j%50)+w*16+r.toNat*1048576).testBit k
  rw [hc,show pack 4 g+w*16+r.toNat*1048576=2^20*r.toNat+(2^4*w+pack 4 g) by omega,
    Nat.testBit_two_pow_mul_add _ (show 2^4*w+pack 4 g < 2^20 by omega)]
  split
  · rw [Nat.testBit_two_pow_mul_add _ hclt]
    split
    · rename_i h4
      rw [pbit _ _ _ h4,hm _ (by dsimp [tm,a]; omega) (by omega)]
      dsimp [g,Cm,tm,a]
      rw [show (2450+2*(j%50))%50=(2450+2*j)%50 by omega,
        show (-350-((j:Int)%50)-4+(k:Int))%50=(-350-(j:Int)-4+k)%50 by omega]
    · have h := hw (k-4) (by omega)
      simpa only [show a j+((k-4:Nat):Int)=a j-4+k by omega] using h
  · have : k=20 := by omega
    subst k
    rw [show a j-4+(20:Nat)=a j+16 by omega]
    change r = r.toNat.testBit 0
    cases r <;> rfl

private theorem mediumSteps (p : Phase) (n s : Nat) : evolve n (Cm p s) = Cm p (n+s) := by
  induction n with
  | zero => simp [evolve]
  | succ n ih => rw [evolve,Nat.succ_add,ih]; exact funext (Cm_step p (n+s))

private theorem carry (p : Phase) (n s : Nat) (x : Int)
    (h : ∀ z : Int, x-n≤z → z≤x+n → Y p s z=Cm p s z) :
    Y p (n+s) x = Cm p (n+s) x := by
  unfold Y
  rw [evolve_add,← mediumSteps p n s]
  exact evolve_agree_window n _ _ x h

private theorem invariant (p : Phase) (j : Nat) :
    Medium p j ∧ ∃ i < (row p j).size, Window p j i := by
  induction j with
  | zero =>
    constructor
    · intro x lo hi
      exact initialMedium p x (by dsimp [tm] at lo; omega) hi
    · refine ⟨start p,start_mem p,?_⟩
      intro k hk
      unfold word
      rw [← start_word,pbit _ _ _ hk]
      exact readSnap p 0 _ (by dsimp [a]; omega) (by dsimp [a]; omega)
  | succ j ih =>
    obtain ⟨hm,i,hi,hw⟩ := ih
    let r := Y p (tm j) (a j+16)
    obtain ⟨z,hz,hout,hword⟩ := transition p j i hi r
    have ht : tm (j+1) = tm j+2 := by dsimp [tm]; omega
    have ha : a (j+1) = a j-1 := by dsimp [a]; omega
    have read := shrinkRead 19 _ _ _ (inputRead p j i hm hw)
    have read2 := shrinkRead 17 _ _ _ read
    have bits (k : Nat) (hk : k<17) :
        Y p (tm (j+1)) (a j-2+k) = (output p j i r).testBit k := by
      rw [ht]
      change step (step (Y p (tm j))) _ = _; unfold output; dsimp only [r]
      simpa only [show a j-4+1+1=a j-2 by omega] using read2 k hk
    constructor
    · intro x lo hi'
      by_cases hl : x < -(tm j:Int)+1302
      · let n := 2*(j+1)
        let k := x+(tm (j+1):Int)
        have h := seam p n k (by dsimp [k,tm] at *; omega) (by dsimp [k,tm] at *; omega)
        simpa only [show n+2450=tm (j+1) by dsimp [tm,n]; omega,
          show -((n:Nat)+2450:Int)+k=x by dsimp [n,k,tm]; omega] using h
      · by_cases hr : x < a j-2
        · rw [show tm (j+1)=2+tm j by omega]
          apply carry
          intro u lu ru
          apply hm <;> omega
        · have hx : x=a j-2 := by rw [ha] at hi'; omega
          subst x
          simpa only [Int.ofNat_zero,Int.add_zero] using (bits 0 (by decide)).trans (ht.symm ▸ hout)
    · refine ⟨z,hz,?_⟩
      intro k hk
      have hb := bits (k+1) (by omega)
      rw [← hword]
      change _ = (((output p j i r) >>> 1) % 2^16).testBit k
      rw [Nat.testBit_mod_two_pow,decide_eq_true hk]
      simpa only [Nat.testBit_shiftRight, Bool.true_and, Nat.add_comm 1 k,ha,
        show a j-2+((k+1:Nat):Int)=a j-1+k by omega] using hb

theorem wedge_all (t : Nat) (x : Int) (ht : 2485 ≤ t)
    (hl : -(t:Int)+1302 ≤ x) (hr : x ≤ 59-((t/2:Nat):Int)) :
    Rule110KernelCert.EssentialAt t (-x) := by
  apply essential_of_cm t x (by omega)
  intro p
  let j := (t-2450)/2
  have hm := (invariant p j).1
  change Y p t x = Cm p t x
  by_cases he : t=tm j
  · rw [he]
    apply hm <;> dsimp [tm,a,j] at * <;> omega
  · have ho : t=1+tm j := by dsimp [tm,j] at *; omega
    rw [ho]
    apply carry
    intro u lu ru
    apply hm <;> dsimp [tm,a,j] at * <;> omega

#print axioms wedge_all
end Rails.Crystal50Wedge
