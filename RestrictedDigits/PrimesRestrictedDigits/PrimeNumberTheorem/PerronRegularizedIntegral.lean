import PrimesRestrictedDigits.PrimeNumberTheorem.PerronPole
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-! # PerronRegularizedIntegral -/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/- The regularized numerator becomes a finite Fourier integral on the
   imaginary axis.  The interval orientation records whether `y` is below or
   above one. -/
theorem perronRegularizedCpow_imaginary {y t : Real} (hy : 0 < y) :
    perronRegularizedCpow y ((t : Complex) * Complex.I) =
      ∫ u in (0 : Real)..Real.log y,
        Complex.exp (((t : Complex) * Complex.I) * (u : Complex)) := by
  by_cases ht : t = 0
  · subst t
    simp only [ofReal_zero, zero_mul, perronRegularizedCpow, dslope_same,
      Complex.exp_zero, intervalIntegral.integral_const, sub_zero]
    rw [(Complex.hasStrictDerivAt_const_cpow
      (x := (y : Complex)) (y := 0)
        (Or.inl <| Complex.ofReal_ne_zero.mpr hy.ne')).hasDerivAt.deriv]
    rw [Complex.cpow_zero, one_mul, ← Complex.ofReal_log hy.le]
    norm_num
  · have htI : (t : Complex) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
    rw [integral_exp_mul_complex htI]
    rw [perronRegularizedCpow, dslope_of_ne _ htI]
    simp only [slope, sub_zero, cpow_zero, vsub_eq_sub, smul_eq_mul,
      ]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
    rw [Complex.ofReal_log hy.le]
    norm_num
    rw [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
    ring_nf

end PrimesRestrictedDigits
