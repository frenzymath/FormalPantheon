import PrimesRestrictedDigits.Fourier.Normalized

/-!
# Fourier product weights for bilinear frequency pairs

This small module keeps the common nonnegative grid weight independent of the Cauchy and
structured-cell implementations.
-/

namespace PrimesRestrictedDigits

/-- The product of the two normalized digit Fourier magnitudes. -/
noncomputable def bilinearPairFourierWeight
    (digit : Fin 10) (length : Nat)
    (pair : Fin (10 ^ length) × Fin (10 ^ length)) : Real :=
  normalizedPaddedDigitFourierMagnitude digit length pair.1.val *
    normalizedPaddedDigitFourierMagnitude digit length pair.2.val

theorem bilinearPairFourierWeight_nonneg
    (digit : Fin 10) (length : Nat)
    (pair : Fin (10 ^ length) × Fin (10 ^ length)) :
    0 <= bilinearPairFourierWeight digit length pair := by
  exact mul_nonneg
    (normalizedPaddedDigitFourierMagnitude_nonneg digit length pair.1.val)
    (normalizedPaddedDigitFourierMagnitude_nonneg digit length pair.2.val)

end PrimesRestrictedDigits
