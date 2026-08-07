import BoundedGaps.BombieriVinogradov.Analytic.RectangleReciprocalWedgeIntegral

/-!
# Finite principal-part sums on rectangle boundaries

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 58--59, equation
(5.13), evaluates a positively oriented rectangle boundary by the enclosed
residue sum. This file extends SEM-520's independently proved one-principal-
part identity to a finite set of distinct interior locations.

The theorem is generic and unnormalized. It does not define a residue or
construct the later removable Dirichlet remainder. Semantic review: `SEM-521`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory
open scoped BigOperators

noncomputable section

private lemma continuous_horizontal_principal_part
    (c p : ℂ) (y : ℝ) (hy : y ≠ p.im) :
    Continuous (fun x : ℝ => c / ((x : ℂ) + y * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_ofReal.add (continuous_const.mul continuous_const)).sub
      continuous_const)
  intro x
  change ((x : ℂ) + (y : ℂ) * I - p) ≠ 0
  apply sub_ne_zero.mpr
  intro h
  have him := congrArg Complex.im h
  apply hy
  simpa using him

private lemma continuous_vertical_principal_part
    (c p : ℂ) (x : ℝ) (hx : x ≠ p.re) :
    Continuous (fun y : ℝ => c / ((x : ℂ) + y * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const)
  intro y
  change ((x : ℂ) + (y : ℂ) * I - p) ≠ 0
  apply sub_ne_zero.mpr
  intro h
  have hre := congrArg Complex.re h
  apply hx
  simpa using hre

/-- The positive rectangle-boundary integral of a finite sum of reciprocal
principal parts is `2 * pi * I` times the sum of their coefficients.

The `Finset` indexes each location once; analytic multiplicity belongs in the
coefficient. The strict inequalities both orient the rectangle and keep every
pole off its four boundary edges. -/
theorem
    wedgeIntegral_add_wedgeIntegral_finset_sum_div_sub_eq_two_pi_I_mul_sum
    (z w : ℂ) (P : Finset ℂ) (c : ℂ → ℂ)
    (hP : ∀ p ∈ P,
      z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im) :
    Complex.wedgeIntegral z w (fun s => ∑ p ∈ P, c p / (s - p)) +
        Complex.wedgeIntegral w z (fun s => ∑ p ∈ P, c p / (s - p)) =
      (2 * Real.pi * I) * ∑ p ∈ P, c p := by
  classical
  have hbottom : ∀ p ∈ P,
      IntervalIntegrable
        (fun x : ℝ => c p / ((x : ℂ) + z.im * I - p)) volume z.re w.re := by
    intro p hp
    exact (continuous_horizontal_principal_part (c p) p z.im
      (ne_of_lt (hP p hp).2.2.1)).intervalIntegrable _ _
  have htop : ∀ p ∈ P,
      IntervalIntegrable
        (fun x : ℝ => c p / ((x : ℂ) + w.im * I - p)) volume w.re z.re := by
    intro p hp
    exact (continuous_horizontal_principal_part (c p) p w.im
      (ne_of_gt (hP p hp).2.2.2)).intervalIntegrable _ _
  have hright : ∀ p ∈ P,
      IntervalIntegrable
        (fun y : ℝ => c p / ((w.re : ℂ) + y * I - p)) volume z.im w.im := by
    intro p hp
    exact (continuous_vertical_principal_part (c p) p w.re
      (ne_of_gt (hP p hp).2.1)).intervalIntegrable _ _
  have hleft : ∀ p ∈ P,
      IntervalIntegrable
        (fun y : ℝ => c p / ((z.re : ℂ) + y * I - p)) volume w.im z.im := by
    intro p hp
    exact (continuous_vertical_principal_part (c p) p z.re
      (ne_of_lt (hP p hp).1)).intervalIntegrable _ _
  have hzw :
      Complex.wedgeIntegral z w (fun s => ∑ p ∈ P, c p / (s - p)) =
        ∑ p ∈ P, Complex.wedgeIntegral z w (fun s => c p / (s - p)) := by
    simp only [Complex.wedgeIntegral]
    rw [intervalIntegral.integral_finsetSum hbottom,
      intervalIntegral.integral_finsetSum hright]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  have hwz :
      Complex.wedgeIntegral w z (fun s => ∑ p ∈ P, c p / (s - p)) =
        ∑ p ∈ P, Complex.wedgeIntegral w z (fun s => c p / (s - p)) := by
    simp only [Complex.wedgeIntegral]
    rw [intervalIntegral.integral_finsetSum htop,
      intervalIntegral.integral_finsetSum hleft]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  rw [hzw, hwz, ← Finset.sum_add_distrib]
  calc
    (∑ p ∈ P, (Complex.wedgeIntegral z w (fun s => c p / (s - p)) +
        Complex.wedgeIntegral w z (fun s => c p / (s - p)))) =
        ∑ p ∈ P, (2 * Real.pi * I) * c p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact wedgeIntegral_add_wedgeIntegral_div_sub_eq_two_pi_I_mul z w p (c p)
        (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2.1 (hP p hp).2.2.2
    _ = (2 * Real.pi * I) * ∑ p ∈ P, c p := by
      rw [Finset.mul_sum]

end

end BoundedGaps.Maynard
