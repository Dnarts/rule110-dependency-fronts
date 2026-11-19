import Bridge
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192
set_option maxHeartbeats 0
namespace Rails.Finite
open Rule110Complete Rule110LocalWindow Rule110Fin1320Bridge
abbrev Pair := V × V
def tick (z : Pair) : Pair := (advance z.1, advance z.2)
def diff : List Pair → V
  | [] => 0
  | z::zs => (z.1 ^^^ z.2) ||| diff zs
theorem hit {zs : List Pair} {k : Nat} (h : (diff zs).getLsbD k = true) :
    ∃ z ∈ zs, z.1.getLsbD k ≠ z.2.getLsbD k := by
  induction zs with
  | nil => simp [diff] at h
  | cons z zs ih =>
    simp only [diff,BitVec.getLsbD_or,BitVec.getLsbD_xor,Bool.or_eq_true] at h
    rcases h with h|h
    · exact ⟨z,by simp,by intro he; simp [he] at h⟩
    · obtain ⟨w,hw,hd⟩ := ih h
      exact ⟨w,by simp [hw],hd⟩
def mask (t : Nat) : V := (BitVec.ofNat 5520 (2^(t+(t-t/3)+1)-1)) <<< (2760-t)
def checkRows : Nat → Nat → List Pair → Bool
  | 0,_,_ => true
  | n+1,t,zs => (diff zs &&& mask t == mask t) && checkRows n (t+1) (zs.map tick)
def orbit (z : Pair) (n : Nat) : Pair := (run n z.1,run n z.2)
theorem checkSound (n t : Nat) (zs : List Pair) (h : checkRows n t zs=true)
    (r : Nat) (hr : r<n) : diff (zs.map (fun z => orbit z r)) &&& mask (t+r) = mask (t+r) := by
  induction n generalizing t zs r with
  | zero => omega
  | succ n ih =>
    simp only [checkRows,Bool.and_eq_true,beq_iff_eq] at h
    cases r with
    | zero => simpa [orbit,run] using h.1
    | succ r =>
      have hh := ih (t+1) (zs.map tick) h.2 r (by omega)
      simpa [List.map_map,Function.comp_def,orbit,tick,run, show t+1+r=t+(r+1) by omega] using hh
theorem maskOn (t : Nat) (ht : t<2485) (x : Int) (hl : -(t:Int)≤x) (hr : x≤(t-t/3:Nat)) :
    (mask t).getLsbD (pos x) = true := by
  have hx : 0 ≤ x+2760 ∧ x+2760<5520 := by omega
  unfold mask pos
  rw [Int.emod_eq_of_lt hx.1 hx.2,BitVec.getLsbD_shiftLeft]
  rw [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one]; simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,decide_eq_false_iff_not]; omega
def seeds : List V := [(8,244),(10,632),(10,976),(10,576),(4,13),(6,52),(6,48)].flatMap
    fun (n,w) => (List.range n).map (input n w)
def pairs := seeds.map (fun u => (u,defect u))

def iterate : Nat → List Pair → List Pair
  | 0,zs => zs
  | n+1,zs => iterate n (zs.map tick)
theorem concatenate (m n t : Nat) (zs : List Pair)
    (h : checkRows m t zs=true) (h' : checkRows n (t+m) (iterate m zs)=true) :
    checkRows (m+n) t zs=true := by
  induction m generalizing t zs with
  | zero => simpa [iterate] using h'
  | succ m ih =>
    rw [Nat.succ_add,checkRows,Bool.and_eq_true]
    simp only [checkRows,Bool.and_eq_true] at h
    refine ⟨h.1,ih _ _ h.2 ?_⟩
    simpa only [iterate,show t+1+m=t+(m+1) by omega] using h'
end Rails.Finite
