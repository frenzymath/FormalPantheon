import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Type I level for repeated Section 6 terminals

The repeated prime square lies strictly below the saving-`100` Type I cutoff. Strictness comes
from the exponent gap, since the source prime interval retains its weak upper endpoint.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Twice the Section 6 gap remains strictly below the pure-power Type I
exponent used for repeated prime squares. -/
theorem two_mul_sectionSixThetaGap_lt_repeatedTypeIExponent
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    2 * sectionSixThetaGap epsilon < 50 / 77 - epsilon / 2 := by
  rw [sectionSixThetaGap_eq]
  linarith

/-- Every prime in the exact source interval `(X^delta, X^theta]` has square
strictly below the canonical repeated-terminal Type I cutoff. -/
theorem sectionSixPrimeSquare_lt_repeatedTypeILevel
    {epsilon delta X : Real} {q : Nat}
    (hepsilon : 0 < epsilon) (hX : 1 < X)
    (hq : q ∈ sievePrimeInterval (X ^ delta)
      (X ^ sectionSixThetaGap epsilon)) :
    ((q * q : Nat) : Real) < X ^ (50 / 77 - epsilon / 2) := by
  have hqUpper : (q : Real) ≤ X ^ sectionSixThetaGap epsilon :=
    (mem_sievePrimeInterval.mp hq).2.2
  have hqNonneg : 0 ≤ (q : Real) := Nat.cast_nonneg q
  have hthresholdNonneg : 0 ≤ X ^ sectionSixThetaGap epsilon := by
    positivity
  have hsquare : (q : Real) ^ 2 ≤
      (X ^ sectionSixThetaGap epsilon) ^ 2 :=
    (sq_le_sq₀ hqNonneg hthresholdNonneg).2 hqUpper
  have hbasePos : 0 < X := zero_lt_one.trans hX
  have hpower : X ^ (2 * sectionSixThetaGap epsilon) <
      X ^ (50 / 77 - epsilon / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt hX
      (two_mul_sectionSixThetaGap_lt_repeatedTypeIExponent epsilon hepsilon)
  calc
    ((q * q : Nat) : Real) = (q : Real) ^ 2 := by norm_num [pow_two]
    _ ≤ (X ^ sectionSixThetaGap epsilon) ^ 2 := hsquare
    _ = X ^ (2 * sectionSixThetaGap epsilon) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hbasePos.le]
      congr 1
      ring
    _ < X ^ (50 / 77 - epsilon / 2) := hpower

end

end PrimesRestrictedDigits
