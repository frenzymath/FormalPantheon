import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The dimension-one Rosser conjugate

This calibrates Iwaniec's Section 6 parameter from the normalized conjugate polynomial in
`IWANIEC-ROSSER-SIEVE-1980`, Eq. (5.2) and Example 2, printed pp. 180--181.
-/

namespace PrimesRestrictedDigits

/-- The normalized conjugate polynomial for `a = b = kappa = 1`. -/
def dimensionOneRosserConjugate (s : Real) : Real :=
  s - 1

/-- Iwaniec's Section 6 parameter: `beta - 1` is the largest positive root of
the normalized conjugate polynomial. -/
def dimensionOneRosserBeta : Real :=
  2

/-- The explicit dimension-one polynomial satisfies Iwaniec's conjugate
equation `(s * q(s))' = q(s) + q(s + 1)`. -/
theorem dimensionOneRosserConjugate_equation (s : Real) :
    HasDerivAt (fun t => t * dimensionOneRosserConjugate t)
      (dimensionOneRosserConjugate s +
        dimensionOneRosserConjugate (s + 1)) s := by
  change HasDerivAt (fun t : Real => t * (t - 1))
    ((s - 1) + (s + 1 - 1)) s
  have h := (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have hfun : id * (fun t : Real => id t - 1) =
      (fun t : Real => t * (t - 1)) := by
    funext t
    rfl
  rw [hfun] at h
  change HasDerivAt (fun t : Real => t * (t - 1))
    (1 * (s - 1) + s * 1) s at h
  convert h using 1
  all_goals ring

/-- The normalized dimension-one conjugate has exactly one real root. -/
theorem dimensionOneRosserConjugate_eq_zero_iff (s : Real) :
    dimensionOneRosserConjugate s = 0 <-> s = 1 := by
  simp only [dimensionOneRosserConjugate, sub_eq_zero]

/-- The normalized dimension-one conjugate is positive exactly beyond its
root. -/
theorem dimensionOneRosserConjugate_pos_iff (s : Real) :
    0 < dimensionOneRosserConjugate s <-> 1 < s := by
  simp [dimensionOneRosserConjugate]

/-- The number `beta - 1 = 1` is the largest positive root, as required at
the start of Iwaniec's Section 6. -/
theorem dimensionOneRosserBeta_isGreatest_positiveRoot :
    IsGreatest
      {s : Real | 0 < s ∧ dimensionOneRosserConjugate s = 0}
      (dimensionOneRosserBeta - 1) := by
  constructor
  · norm_num [dimensionOneRosserConjugate, dimensionOneRosserBeta]
  · intro s hs
    change 0 < s ∧ dimensionOneRosserConjugate s = 0 at hs
    rw [dimensionOneRosserConjugate_eq_zero_iff] at hs
    norm_num [dimensionOneRosserBeta, hs.2]

theorem one_lt_dimensionOneRosserBeta :
    1 < dimensionOneRosserBeta := by
  norm_num [dimensionOneRosserBeta]

end PrimesRestrictedDigits
