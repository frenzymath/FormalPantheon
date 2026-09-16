import PrimesRestrictedDigits.BasicEstimates.BuchstabSlabRemainder
import PrimesRestrictedDigits.BasicEstimates.BuchstabMainIntegral

/-!
# The weighted prime sum in the Buchstab induction

This file combines the Eq. (7.45) residual and main-integral evaluation from
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7, p. 218.
-/

open Finset
open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The weighted prime sum has the expected Buchstab endpoint difference under
the explicit global weak PNT remainder premise. -/
theorem abs_sum_prime_buchstabPrimeWeight_sub_buchstabDifference_le
    {m : Nat} {x u C : Real}
    (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) (hu : u ≤ (m : Real) + 1)
    (hlower : 2 ≤ x ^ (1 / u)) (hC : 0 ≤ C)
    (hPNT : ∀ t : Real, 2 ≤ t →
      |primeRemainder t| ≤ C * t / Real.log t ^ 2) :
    |(∑ p ∈
        (naturalLeftClosedRightOpenInterval (x ^ (1 / u))
          (x ^ (1 / (m : Real)))).filter Nat.Prime,
        buchstabPrimeWeight x p) -
      x / Real.log x *
        (u * buchstabFunction u -
          (m : Real) * buchstabFunction (m : Real))| ≤
      ((m : Real) + 1) ^ 2 *
          (2 + C / 2 + 3 * C / Real.log 2) *
        (x / Real.log x ^ 2) := by
  rw [← integral_buchstabPrimeWeight_div_log_eq_buchstabDifference hx hm hmu]
  exact abs_sum_prime_buchstabPrimeWeight_sub_main_le
    hx hm hmu hu hlower hC hPNT

end PrimesRestrictedDigits
