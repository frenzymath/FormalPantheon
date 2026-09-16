import Waring.LargeNumber.ChenMinorEstimate
import Waring.LargeNumber.ChenRepresentationExtraction

/-!
# Chen's large-number representation theorem

This is the final large-number conclusion of Chen's proof
[CHEN1964-EN, p. 1568; CHEN1964-ZH, p. 734].
-/

set_option autoImplicit false

namespace Waring.LargeNumber

open Waring.Statement

/-- Every target at Chen's final threshold is a sum of at most thirty-seven
natural fifth powers. -/
theorem chen_large_number_representation
    {N : Nat} (hN : 10 ^ 785 <= N) :
    HasPowerSumRepresentation 5 37 N := by
  exact chen_large_number_representation_of_minor_bound hN
    (norm_chenMinorConvolution_lt hN)

end Waring.LargeNumber
