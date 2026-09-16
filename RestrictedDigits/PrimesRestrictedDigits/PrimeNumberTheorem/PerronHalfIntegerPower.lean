import PrimesRestrictedDigits.PrimeNumberTheorem.PerronHalfInteger

/-!
# Complex power at the half-integer Perron cutoff

The positive cutoff `X - 1 / 2` on the line `1 / log X + I * t` has uniformly bounded
complex-power norm. This is the cutoff factor used in the contour step of Proposition 9.3.
-/

namespace PrimesRestrictedDigits

/-- The complex power at the half-integer Perron cutoff costs less than three,
uniformly in the vertical height. -/
theorem norm_halfIntegerPerronCutoffCpow_le_three
    {X : Nat} (hX : 4 ≤ X) (t : Real) :
    ‖((((X : Real) - 1 / 2 : Real) : Complex) ^
        ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
          Complex.I * (t : Complex)))‖ ≤ 3 := by
  have hXPos : (0 : Real) < X := by positivity
  have hcutoffPos : (0 : Real) < (X : Real) - 1 / 2 := by
    have hXR : (4 : Real) ≤ X := by exact_mod_cast hX
    linarith
  have hlogPos : 0 < Real.log (X : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < X by omega)
  have hsigmaPos : 0 < (Real.log (X : Real))⁻¹ := inv_pos.mpr hlogPos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hcutoffPos]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
    sub_zero, add_zero]
  calc
    ((X : Real) - 1 / 2) ^ (Real.log (X : Real))⁻¹ ≤
        (X : Real) ^ (Real.log (X : Real))⁻¹ := by
      apply Real.rpow_le_rpow hcutoffPos.le
      · linarith
      · exact hsigmaPos.le
    _ ≤ Real.exp 1 := Real.rpow_inv_log_le_exp_one
    _ ≤ 3 := Real.exp_one_lt_three.le

end PrimesRestrictedDigits
