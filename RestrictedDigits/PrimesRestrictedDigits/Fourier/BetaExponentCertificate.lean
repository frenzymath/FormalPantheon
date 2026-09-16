import PrimesRestrictedDigits.Fourier.DyadicHornerCertificate
import Mathlib.Tactic.NormNum

/-!
# Exact dyadic exponent for the powered certificate

The fixed 30-bit fraction here is bookkeeping for the later `235 / 154`
moment.  It supplies no endpoint or spectral estimate.
-/

namespace PrimesRestrictedDigits

def betaBits30 : List Bool :=
  [true, true, false, false, false, false,
    true, true, false, true, false, true,
    false, false, true, true, false, false,
    false, true, true, true, false, true,
    true, true, true, false, true, true]

theorem betaBits30_length : betaBits30.length = 30 := by
  norm_num [betaBits30]

theorem dyadicExponent_betaBits30 :
    dyadicExponent betaBits30 = (819251067 : ℝ) / 1073741824 := by
  norm_num [betaBits30, dyadicExponent, boolReal]

theorem two_mul_dyadicExponent_betaBits30_le :
    2 * dyadicExponent betaBits30 ≤ (235 / 154 : ℝ) := by
  rw [dyadicExponent_betaBits30]
  norm_num

end PrimesRestrictedDigits
