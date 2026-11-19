import Rule110KernelCertificate

namespace Rule110KernelCert

theorem ringEvolveBV_add (a b : Nat) (u : RingBV) :
    ringEvolveBV (a + b) u = ringEvolveBV a (ringEvolveBV b u) := by
  induction a with
  | zero => simp [ringEvolveBV]
  | succ a ih => simp [Nat.succ_add, ringEvolveBV, ih]

end Rule110KernelCert
