import Waring.FiniteRange
import Waring.LargeNumber.ChenLargeNumber
import Waring.LowerBound

/-!
# The proof that `g(5) = 37`

The theorem statement and finite/large split follow [CHEN1964-EN, p. 1547;
CHEN1964-ZH, p. 715], with the completed large-number proof ending at
[CHEN1964-EN, p. 1568; CHEN1964-ZH, p. 734].
-/

set_option autoImplicit false

namespace Waring

open Statement

/-- The finite certificate below the threshold and Chen's circle method above
it together make thirty-seven a universal fifth-power Waring bound. -/
theorem thirtySeven_isUniversal :
    IsUniversalWaringBound 5 37 := by
  intro N hNPositive
  by_cases hNFinite : N <= 10 ^ 785
  · exact chen_finite_range hNPositive hNFinite
  · exact LargeNumber.chen_large_number_representation
      (Nat.le_of_lt (lt_of_not_ge hNFinite))

namespace Main

/-- The classical Waring number for fifth powers is exactly thirty-seven. -/
theorem g_five_eq_thirtySeven : Statement.MainTheorem := by
  change IsLeastUniversalWaringBound 5 37
  constructor
  · exact thirtySeven_isUniversal
  · intro t ht
    exact universal_bound_five_ge_thirtySeven ht

end Main

end Waring
