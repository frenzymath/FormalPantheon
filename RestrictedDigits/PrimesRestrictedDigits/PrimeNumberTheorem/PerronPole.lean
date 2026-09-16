import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Regularization of the pole in Perron's kernel

For a positive real base `y`, this module isolates the removable part of
`y ^ s / s`. This is the simple pole occurring in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eq. (5.3), p. 137.
-/

open Complex Set

namespace PrimesRestrictedDigits

/-- The entire extension of `((y : Complex) ^ s - 1) / s` across `s = 0`. -/
noncomputable def perronRegularizedCpow (y : Real) (s : Complex) : Complex :=
  dslope (fun z : Complex => (y : Complex) ^ z) 0 s

/-- The removable part of the positive-base Perron kernel is entire. -/
theorem differentiable_perronRegularizedCpow {y : Real} (hy : 0 < y) :
    Differentiable Complex (perronRegularizedCpow y) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2 <|
    (differentiable_id.const_cpow
      (.inl <| Complex.ofReal_ne_zero.mpr hy.ne')).differentiableOn

/-- Away from zero, split the Perron kernel into its entire part and its
simple pole. -/
theorem perronCpow_div_eq_regularized_add_inv {y : Real} (_hy : 0 < y)
    {s : Complex} (hs : s ≠ 0) :
    (y : Complex) ^ s / s = perronRegularizedCpow y s + 1 / s := by
  rw [perronRegularizedCpow, dslope_of_ne _ hs]
  simp only [slope, sub_zero, cpow_zero, vsub_eq_sub, smul_eq_mul]
  field_simp
  ring

end PrimesRestrictedDigits
