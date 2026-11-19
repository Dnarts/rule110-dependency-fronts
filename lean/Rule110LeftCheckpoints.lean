import Rule110LeftCoverage00
import Rule110LeftCoverage05
import Rule110LeftCoverage10
import Rule110LeftCoverage15
import Rule110LeftCoverage20
import Rule110LeftCoverage25

set_option exponentiation.threshold 2048
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Rule110KernelCert.LeftCheckpoints

theorem strip_base (r k : Nat) (hr : r < 30) (hk : k < 106) :
    ∃ u : RingBV, Repeats leftPos 106 30 u ∧ Differs u (300 + r) (leftPos (300 + r) k) := by
  have cases_r : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 := by omega
  rcases cases_r with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact coverage_316 k hk
  · exact coverage_317 k hk
  · exact coverage_318 k hk
  · exact coverage_319 k hk
  · exact coverage_320 k hk
  · exact coverage_321 k hk
  · exact coverage_322 k hk
  · exact coverage_323 k hk
  · exact coverage_324 k hk
  · exact coverage_325 k hk
  · exact coverage_326 k hk
  · exact coverage_327 k hk
  · exact coverage_328 k hk
  · exact coverage_329 k hk

end Rule110KernelCert.LeftCheckpoints
