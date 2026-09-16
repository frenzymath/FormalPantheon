import PrimesRestrictedDigits.Fourier.HybridResidueCRT
import PrimesRestrictedDigits.Fourier.HybridDenominatorSplit
import PrimesRestrictedDigits.Fourier.ContinuousTransformSquaredVariation
import PrimesRestrictedDigits.Fourier.ClosedWindowMaximum

/-!
# Residual squared-transform sums for the hybrid Sigma branches

These definitions name the two residual factors left after the complete-grid estimates in
published Lemma 10.7, equations (10.14)--(10.15).
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The residual squared-transform sum in the first hybrid Sigma branch. -/
def decimalHybridFirstSquaredResidualSum
    (digit : Fin 10) (q d k v : Nat) (delta : Real) : Real :=
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  ∑ c : ReducedResidue (q * (d₁ * d₂)),
    closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeSqAt digit v)
      (((10 ^ k : Nat) : Real) * delta)
      ((c.val.val : Real) / (q * (d₁ * d₂) : Nat))

/-- The residual squared-transform sum in the second hybrid Sigma branch. -/
def decimalHybridSecondSquaredResidualSum
    (digit : Fin 10) (q d k v : Nat) (delta : Real) : Real :=
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  ∑ c : ReducedResidue (q * d₁),
    closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeSqAt digit v)
      (((10 ^ k * 10 ^ v : Nat) : Real) * delta)
      ((c.val.val : Real) / (q * d₁ : Nat))

/-- The first residual sum is nonnegative for every nonnegative window. -/
theorem decimalHybridFirstSquaredResidualSum_nonneg
    (digit : Fin 10) (q d k v : Nat) {delta : Real}
    (hdelta : 0 ≤ delta) :
    0 ≤ decimalHybridFirstSquaredResidualSum digit q d k v delta := by
  dsimp [decimalHybridFirstSquaredResidualSum]
  apply Finset.sum_nonneg
  intro c hc
  apply closedWindowMaximum_nonneg
  · exact normalizedPaddedDigitFourierMagnitudeSqAt_continuous digit v
  · intro z
    rw [normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq]
    positivity
  · exact mul_nonneg (by positivity) hdelta

/-- The second residual sum is nonnegative for every nonnegative window. -/
theorem decimalHybridSecondSquaredResidualSum_nonneg
    (digit : Fin 10) (q d k v : Nat) {delta : Real}
    (hdelta : 0 ≤ delta) :
    0 ≤ decimalHybridSecondSquaredResidualSum digit q d k v delta := by
  dsimp [decimalHybridSecondSquaredResidualSum]
  apply Finset.sum_nonneg
  intro c hc
  apply closedWindowMaximum_nonneg
  · exact normalizedPaddedDigitFourierMagnitudeSqAt_continuous digit v
  · intro z
    rw [normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq]
    positivity
  · exact mul_nonneg (by positivity) hdelta

end

end PrimesRestrictedDigits
