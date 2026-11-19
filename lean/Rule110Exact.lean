import Finite
import Late
namespace Rails
open Rule110Complete Rule110KernelCert

/-- Exact essential input coordinates for the output at the origin. -/
theorem essential_iff (t : Nat) (j : Int) :
    EssentialAt t j ↔ -((t-t/3 : Nat) : Int) ≤ j ∧ j ≤ (t:Int) := by
  constructor
  · rintro ⟨u,v,agree,diff⟩
    constructor
    · apply Int.le_of_not_gt
      intro h
      exact diff (left_dependency_bound t u v j (fun i hi => agree i (by omega)) h)
    · apply Int.le_of_not_gt
      intro h
      exact diff (right_dependency_bound t u v j (fun i hi => agree i (by omega)) h)
  · rintro ⟨hl,hr⟩
    by_cases ht : t<2485
    · simpa only [Int.neg_neg] using Finite.finite_all t ht (-j) (by omega) (by omega)
    · exact late_all t j (by omega) hl hr
#print axioms essential_iff
end Rails
