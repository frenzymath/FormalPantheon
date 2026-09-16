import PrimesRestrictedDigits.PrimeNumberTheorem.PerronPole
import Mathlib.Analysis.Complex.CauchyIntegral
/-! # PerronRectangle -/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- Cauchy's exact boundary identity for the entire regularized numerator. -/
theorem perronRegularized_rectangle_identity {y sigma T : Real} (hy : 0 < y) :
    (∫ r in (0 : Real)..sigma,
          perronRegularizedCpow y (r + (-T) * Complex.I)) -
        (∫ r in (0 : Real)..sigma,
          perronRegularizedCpow y (r + T * Complex.I)) +
        Complex.I * (∫ t in (-T)..T,
          perronRegularizedCpow y (sigma + t * Complex.I)) -
        Complex.I * (∫ t in (-T)..T,
          perronRegularizedCpow y (0 + t * Complex.I)) = 0 := by
  simpa only [ofReal_zero, zero_add, smul_eq_mul, ofReal_neg, ofReal_mul,
    ofReal_ofNat] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (perronRegularizedCpow y) (Complex.mk 0 (-T)) (Complex.mk sigma T)
      (differentiable_perronRegularizedCpow hy).differentiableOn

end PrimesRestrictedDigits
