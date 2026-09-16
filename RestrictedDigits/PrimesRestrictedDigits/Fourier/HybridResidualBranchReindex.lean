import PrimesRestrictedDigits.Fourier.HybridResidualPrefix
import PrimesRestrictedDigits.Fourier.HybridSigmaResidualSums

/-!
# Residual Branch Reindexing

This file identifies the two residual squared-transform sums `Sigma3'` and `Sigma5'` following
equation (10.13) with the source sum bounded in equation (10.16). See `MAYNARD-PRD-PUBLISHED`,
pp. 183--185.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

private def reducedResidueCongr {m n : Nat} (h : m = n) :
    ReducedResidue m ≃ ReducedResidue n :=
  Equiv.cast (congrArg ReducedResidue h)

@[simp]
private theorem reducedResidueCongr_val {m n : Nat} (h : m = n)
    (a : ReducedResidue m) :
    (reducedResidueCongr h a).val.val = a.val.val := by
  subst n
  rfl

/-- The first residual branch, summed over the source denominator band, is
the source sum with fixed factor `(d1 * d2) * q1`. -/
theorem sum_decimalHybridFirstSquaredResidualSum_eq_hybridResidualReducedSourceSum
    (digit : Fin 10) (q₁ d k v Q₂ : Nat) (delta : Real) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
        decimalHybridFirstSquaredResidualSum digit (q₁ * q₂) d k v delta) =
      hybridResidualReducedSourceSum digit v ((d₁ * d₂) * q₁) Q₂
        (((10 ^ k : Nat) : Real) * delta) := by
  classical
  dsimp only [decimalHybridFirstSquaredResidualSum]
  rw [hybridResidualReducedSourceSum]
  apply Finset.sum_congr rfl
  intro q₂ _
  let hmod : (q₁ * q₂) *
        (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
          hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) =
      ((hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
          hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) * q₁) * q₂ := by
    ac_rfl
  let e := reducedResidueCongr hmod
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  rw [reducedResidueCongr_val]
  congr 2
  exact_mod_cast hmod

/-- The second residual branch, summed over the source denominator band, is
the source sum with fixed factor `d1 * q1`. -/
theorem sum_decimalHybridSecondSquaredResidualSum_eq_hybridResidualReducedSourceSum
    (digit : Fin 10) (q₁ d k v Q₂ : Nat) (delta : Real) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    (∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
        decimalHybridSecondSquaredResidualSum digit (q₁ * q₂) d k v delta) =
      hybridResidualReducedSourceSum digit v (d₁ * q₁) Q₂
        (((10 ^ k * 10 ^ v : Nat) : Real) * delta) := by
  classical
  dsimp only [decimalHybridSecondSquaredResidualSum]
  rw [hybridResidualReducedSourceSum]
  apply Finset.sum_congr rfl
  intro q₂ _
  let hmod : (q₁ * q₂) *
        hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) =
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) * q₁) * q₂ := by
    ac_rfl
  let e := reducedResidueCongr hmod
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  rw [reducedResidueCongr_val]
  congr 2
  exact_mod_cast hmod

end

end PrimesRestrictedDigits
