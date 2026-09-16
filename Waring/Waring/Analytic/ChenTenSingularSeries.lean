import Waring.Analytic.ChenTenSingularCoefficient
import Mathlib.Analysis.PSeries

/-!
# Absolute convergence of Chen's singular series

The finite coefficient bound from Lemma 2 gives an absolutely convergent
series before any Euler-product rearrangement [CHEN1964-EN, pp. 1561,
1565-1567; CHEN1964-ZH, pp. 728, 731-733].
-/

namespace Waring.Analytic

open scoped ComplexConjugate

/-- Chen's singular coefficient extended by zero to modulus zero. -/
noncomputable def chenTenSingularCoefficientNat
    (n q : Nat) : Complex :=
  if hq : q = 0 then 0
  else @chenTenSingularCoefficient q ⟨hq⟩ n

@[simp] theorem chenTenSingularCoefficientNat_zero (n : Nat) :
    chenTenSingularCoefficientNat n 0 = 0 := by
  simp [chenTenSingularCoefficientNat]

@[simp] theorem chenTenSingularCoefficientNat_one (n : Nat) :
    chenTenSingularCoefficientNat n 1 = 1 := by
  simp [chenTenSingularCoefficientNat]

/-- The quadratic majorant holds uniformly after extension to modulus zero. -/
theorem norm_chenTenSingularCoefficientNat_le
    (n q : Nat) :
    ‖chenTenSingularCoefficientNat n q‖ <=
      (40 : Real) ^ 15 * (q : Real) ^ (-2 : Real) := by
  by_cases hq : q = 0
  · subst q
    simp [chenTenSingularCoefficientNat]
    positivity
  · simp only [chenTenSingularCoefficientNat, dif_neg hq]
    exact @norm_chenTenSingularCoefficient_le_chenTwo q ⟨hq⟩ n

/-- Chen's singular coefficients are absolutely summable in the modulus. -/
theorem summable_chenTenSingularCoefficientNat (n : Nat) :
    Summable (chenTenSingularCoefficientNat n) := by
  have hmajor :
      Summable (fun q : Nat =>
        (40 : Real) ^ 15 * (q : Real) ^ (-2 : Real)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left ((40 : Real) ^ 15)
  exact hmajor.of_norm_bounded
    (fun q => norm_chenTenSingularCoefficientNat_le n q)

/-- Chen's absolutely convergent singular series. -/
noncomputable def chenTenSingularSeries (n : Nat) : Complex :=
  ∑' q : Nat, chenTenSingularCoefficientNat n q

/-- The defining coefficient family sums to the singular series. -/
theorem hasSum_chenTenSingularCoefficientNat (n : Nat) :
    HasSum (chenTenSingularCoefficientNat n)
      (chenTenSingularSeries n) :=
  (summable_chenTenSingularCoefficientNat n).hasSum

/-- The singular series is fixed by complex conjugation. -/
theorem conj_chenTenSingularSeries (n : Nat) :
    conj (chenTenSingularSeries n) = chenTenSingularSeries n := by
  unfold chenTenSingularSeries
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro q
  by_cases hq : q = 0
  · subst q
    simp
  · simp [chenTenSingularCoefficientNat, hq,
      @conj_chenTenSingularCoefficient q ⟨hq⟩ n]

/-- Chen's singular series is real-valued. -/
theorem chenTenSingularSeries_im_eq_zero (n : Nat) :
    (chenTenSingularSeries n).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_chenTenSingularSeries n)

end Waring.Analytic
