import PrimesRestrictedDigits.Fourier.LargeSieveScaleLoss

/-!
# Explicit constants for the repaired hybrid estimates

These constants freeze the quantitative statements.
-/

namespace PrimesRestrictedDigits

/-- The common coefficient for a separated family in the repaired hybrid
sampling estimate. -/
def hybridSamplingConstant : Real := 13000000000000000

/-- The common coefficient in both source-facing conclusions of published
Lemma 10.6. -/
def hybridConstant : Real := 50000000000000000

end PrimesRestrictedDigits
