import Waring.Analytic.ChenSevenResidueApproximation
import Waring.Analytic.ChenTenRepresentation

/-!
# Pointwise major-arc approximation for Chen's Lemma 10

This file connects the named Lemma 10 Weyl sum to the project's checked
uniform residue-class quadrature theorem [CHEN1964-EN, p. 1562, equation (28);
CHEN1964-ZH, p. 728, equation (24)].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The named Weyl sum is the zero-based range sum used by the earlier
analytic modules. -/
theorem fifthPowerExponentialSum_eq_sum_range
    (P : Nat) (alpha : Real) :
    fifthPowerExponentialSum P alpha =
      ∑ x ∈ Finset.range P, realFifthPowerExponential alpha x := by
  unfold fifthPowerExponentialSum
  rw [Fin.sum_univ_eq_sum_range]

/-- The source-shaped major-arc approximation with the internally checked
uniform error `6*q`. -/
theorem norm_fifthPowerExponentialSum_sub_majorTerm_le
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hP : 0 < P)
    (hz : |z| <= 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖fifthPowerExponentialSum P ((a : Real) / q + z) -
        (q : Complex)⁻¹ * completePowerSum 5 (a : ZMod q) *
          fifthPerturbationIntegral z P‖ <=
      6 * q := by
  rw [fifthPowerExponentialSum_eq_sum_range]
  have hsum :
      (∑ x ∈ Finset.range P,
          realFifthPowerExponential ((a : Real) / q + z) x) =
        ∑ x ∈ Finset.range P,
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((a : Real) / q + z) * (((1 + x : Nat) : Real) ^ 5))) := by
    apply Finset.sum_congr rfl
    intro x _
    unfold realFifthPowerExponential realFifthPowerPhase
    congr 1
    push_cast
    ring
  rw [hsum]
  exact
    norm_sum_range_exp_fifth_sub_complete_mul_integral_le
      chenSeven_residueApproximation q a z P hP hz

end Waring.Analytic
