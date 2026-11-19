import CertFinal
namespace Rails.Finite
open Rule110Complete Rule110LocalWindow Rule110Fin1320Bridge
theorem finite_all (t : Nat) (ht : t<2485) (x : Int) (hl : -(t:Int)≤x) (hr : x≤(t-t/3:Nat)) :
    Rule110KernelCert.EssentialAt t (-x) := by
  have h := checkSound 2485 0 pairs certificate t ht
  have hh := congrArg (fun s : V => s.getLsbD (pos x)) h
  simp only [Nat.zero_add,BitVec.getLsbD_and,maskOn t ht x hl hr,Bool.and_true] at hh
  obtain ⟨z,hz,hd⟩ := hit hh
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hq
  apply essential (line u)
  rw [local_obs u t x (by omega) (by omega),←line_run]
  exact hd
#print axioms finite_all
end Rails.Finite
