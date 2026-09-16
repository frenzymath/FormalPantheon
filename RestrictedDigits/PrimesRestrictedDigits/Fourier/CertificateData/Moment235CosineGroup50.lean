import PrimesRestrictedDigits.Fourier.CertificateData.Moment235CosineGroup49

/-! The half-period endpoint of the exact signed cosine cache. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

def moment235CosineEndpoint : Int := -999999993529079954370440183642

theorem moment235CosineEndpoint_certificate :
    (moment235CosineScale : Int) *
        rationalCosineUpper20D20FixedNumerator 50000 <=
      (rationalCosineUpper20D20FixedDenominator : Int) *
        moment235CosineEndpoint := by
  decide +kernel

end PrimesRestrictedDigits
