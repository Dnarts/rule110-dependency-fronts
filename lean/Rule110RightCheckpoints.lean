import Rule110RightCoverage00

set_option exponentiation.threshold 2048
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Rule110KernelCert.RightCheckpoints

theorem strip_base (r k : Nat) (hr : r < 16) (hk : k < 20) :
    ∃ u : RingBV, Repeats rightPos 20 16 u ∧ Differs u (300 + r) (rightPos (300 + r) k) := by
  have cases_r : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
  rcases cases_r with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact coverage_300 k hk
  · exact coverage_301 k hk
  · exact coverage_302 k hk
  · exact coverage_303 k hk
  · exact coverage_304 k hk
  · exact coverage_305 k hk
  · exact coverage_306 k hk
  · exact coverage_307 k hk
  · exact coverage_308 k hk
  · exact coverage_309 k hk
  · exact coverage_310 k hk
  · exact coverage_311 k hk
  · exact coverage_312 k hk
  · exact coverage_313 k hk
  · exact coverage_314 k hk
  · exact coverage_315 k hk

end Rule110KernelCert.RightCheckpoints
