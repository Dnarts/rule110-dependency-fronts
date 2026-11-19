import Rule110RightCheckpoints
namespace Rule110KernelCert
theorem right_boundary_width20 (t k : Nat) (ht : 300 ≤ t) (hk : k < 20) :
    EssentialAt t ((t : Int) - k) := by
  have h := strip_all rightPos 20 16 (by decide) RightCheckpoints.strip_base t k ht hk
  rw [show -rightPos t k = (t : Int) - k by unfold rightPos; omega] at h
  exact h

#print axioms right_boundary_width20
end Rule110KernelCert
