import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaPrimitiveShallowCandidates
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaRectangleBoundary

/-!
# Dirichlet explicit-formula contour edges

The positive rectangle identity in `KoukoulopoulosDistributionPrimesPrelim2022`,
printed pp. 58--59, equation (5.13), and pp. 114--115, solves for the upward
right edge as the sum of the crossed singularity contributions and the other
three edges. This file records that exact normalization and a common
source-shaped bound for the normalized remainder.

It does not classify primitive candidates, select a height, or identify the
right edge with an arithmetic sum. Semantic review: `SEM-532`.
-/

namespace BoundedGaps.Maynard

open Complex Set
open scoped BigOperators Interval

noncomputable section

/-- The right vertical edge after the `ds = i dt` parametrization and the
`1 / (2 * pi * i)` contour normalization. -/
noncomputable def dirichletExplicitFormulaNormalizedRightEdge
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x U : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -U..U,
      dirichletExplicitFormulaIntegrand chi x
        (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)

/-- The normalized sum of the lower, upper, and left contour edges after
solving the positive rectangle identity for the right edge. -/
noncomputable def dirichletExplicitFormulaShallowContourRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x U : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    (I * (∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
          dirichletExplicitFormulaIntegrand chi x
            ((sigma : ℂ) - U * I)) -
      I * (∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
          dirichletExplicitFormulaIntegrand chi x
            ((sigma : ℂ) + U * I)) +
      (∫ t in -U..U,
        dirichletExplicitFormulaIntegrand chi x
          (((-1 / 2 : ℝ) : ℂ) + t * I)))

/-- Exact shallow contour decomposition with the positive rectangle
orientation. -/
theorem dirichletExplicitFormulaNormalizedRightEdge_eq_sum_add_remainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x U : ℝ} (hx : 1 < x) (hU : 0 < U)
    (hinside : dirichletExplicitFormulaCandidateSingularities chi
        (((-1 / 2 : ℝ) : ℂ) - U * I)
        (((1 + 1 / Real.log x : ℝ) : ℂ) + U * I) ⊆
      interior (Complex.Rectangle
        (((-1 / 2 : ℝ) : ℂ) - U * I)
        (((1 + 1 / Real.log x : ℝ) : ℂ) + U * I))) :
    dirichletExplicitFormulaNormalizedRightEdge chi x U =
      (∑ rho ∈
          dirichletExplicitFormulaShallowCandidateSingularitiesFinset chi x U,
        dirichletExplicitFormulaCandidateContribution chi x rho) +
      dirichletExplicitFormulaShallowContourRemainder chi x U := by
  classical
  let z : ℂ := ((-1 / 2 : ℝ) : ℂ) - U * I
  let w : ℂ := ((1 + 1 / Real.log x : ℝ) : ℂ) + U * I
  let F : ℂ → ℂ := dirichletExplicitFormulaIntegrand chi x
  let S : ℂ :=
    ∑ rho ∈ dirichletExplicitFormulaCandidateSingularitiesFinset chi z w,
      dirichletExplicitFormulaCandidateContribution chi x rho
  let lower : ℂ :=
    ∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
      F ((sigma : ℂ) - U * I)
  let upper : ℂ :=
    ∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
      F ((sigma : ℂ) + U * I)
  let right : ℂ :=
    ∫ t in -U..U,
      F (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)
  let left : ℂ :=
    ∫ t in -U..U, F (((-1 / 2 : ℝ) : ℂ) + t * I)
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hinvLog : 0 < (Real.log x)⁻¹ := inv_pos.mpr hlog
  have hzwRe : z.re ≤ w.re := by
    dsimp [z, w]
    norm_num
    linarith
  have hzwIm : z.im ≤ w.im := by
    dsimp [z, w]
    norm_num
    linarith
  have hposition : ∀ rho ∈
      dirichletExplicitFormulaCandidateSingularitiesFinset chi z w,
      z.re < rho.re ∧ rho.re < w.re ∧
        z.im < rho.im ∧ rho.im < w.im := by
    intro rho hrho
    have hrhoSet : rho ∈ dirichletExplicitFormulaCandidateSingularities chi z w :=
      mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff.mp hrho
    have hrhoInterior := hinside hrhoSet
    rw [Complex.Rectangle, Complex.interior_reProdIm,
      uIcc_of_le hzwRe, uIcc_of_le hzwIm, interior_Icc, interior_Icc,
      Complex.mem_reProdIm] at hrhoInterior
    exact ⟨hrhoInterior.1.1, hrhoInterior.1.2,
      hrhoInterior.2.1, hrhoInterior.2.2⟩
  have hboundary :=
    wedgeIntegral_add_wedgeIntegral_dirichletExplicitFormulaIntegrand_eq_mul_sum_candidateContribution
      chi x z w hposition
  change Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F =
    (2 * Real.pi * I) * S at hboundary
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at hboundary
  have hboundary' :
      lower - upper + I * right - I * left =
        (2 * Real.pi * I) * S := by
    simpa [lower, upper, right, left, z, w, ofReal_neg,
      sub_eq_add_neg] using hboundary
  have hIright :
      I * right = (2 * Real.pi * I) * S - lower + upper + I * left := by
    linear_combination hboundary'
  have hmainMul :
      -I * ((2 * Real.pi * I) * S) =
        ((2 * Real.pi : ℝ) : ℂ) * S := by
    calc
      _ = (-I * I) * (((2 * Real.pi : ℝ) : ℂ) * S) := by
        push_cast
        ring
      _ = _ := by rw [neg_mul, I_mul_I]; simp
  have hleftMul : -I * (I * left) = left := by
    rw [← mul_assoc, neg_mul, I_mul_I]
    simp
  have hright :
      right = ((2 * Real.pi : ℝ) : ℂ) * S +
        I * lower - I * upper + left := by
    calc
      _ = -I * (I * right) := by
        rw [← mul_assoc, neg_mul, I_mul_I]
        simp
      _ = -I * ((2 * Real.pi * I) * S - lower + upper + I * left) := by
        rw [hIright]
      _ = _ := by
        rw [mul_add, mul_add, mul_sub]
        rw [hmainMul, hleftMul]
        ring
  have htwoPi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast Real.two_pi_pos.ne'
  have hfinset :
      dirichletExplicitFormulaCandidateSingularitiesFinset chi z w =
        dirichletExplicitFormulaShallowCandidateSingularitiesFinset chi x U := by
    simp [z, w, dirichletExplicitFormulaShallowCandidateSingularitiesFinset,
      abs_of_pos hU]
    norm_num
  rw [dirichletExplicitFormulaNormalizedRightEdge,
    dirichletExplicitFormulaShallowContourRemainder]
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹) * right = _
  rw [hright]
  rw [← hfinset]
  change _ = S + (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    (I * lower - I * upper + left)
  field_simp [htwoPi]
  ring

/-- A common source-shaped bound on the three non-right contour edges bounds
the normalized shallow contour remainder. -/
theorem norm_dirichletExplicitFormulaShallowContourRemainder_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x U A C E : ℝ} (hC : 2 ≤ C) (hE : 0 ≤ E)
    (hlower : ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
        dirichletExplicitFormulaIntegrand chi x
          ((sigma : ℂ) - U * I)‖ ≤ 640 * A * C * E)
    (hupper : ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
        dirichletExplicitFormulaIntegrand chi x
          ((sigma : ℂ) + U * I)‖ ≤ 640 * A * C * E)
    (hleft : ‖∫ t in -U..U,
        dirichletExplicitFormulaIntegrand chi x
          (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 720 * A * E) :
    ‖dirichletExplicitFormulaShallowContourRemainder chi x U‖ ≤
      1640 * A * C * E := by
  let lower : ℂ :=
    ∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
      dirichletExplicitFormulaIntegrand chi x ((sigma : ℂ) - U * I)
  let upper : ℂ :=
    ∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
      dirichletExplicitFormulaIntegrand chi x ((sigma : ℂ) + U * I)
  let left : ℂ :=
    ∫ t in -U..U,
      dirichletExplicitFormulaIntegrand chi x
        (((-1 / 2 : ℝ) : ℂ) + t * I)
  change ‖lower‖ ≤ 640 * A * C * E at hlower
  change ‖upper‖ ≤ 640 * A * C * E at hupper
  change ‖left‖ ≤ 720 * A * E at hleft
  have hAE : 0 ≤ A * E := by
    rcases hE.eq_or_lt with hEzero | hEpos
    · rw [← hEzero]
      simp
    · have hnonneg : 0 ≤ 720 * A * E := (norm_nonneg left).trans hleft
      nlinarith
  have htwoAE_le : 2 * (A * E) ≤ C * (A * E) :=
    mul_le_mul_of_nonneg_right hC hAE
  have hinvNorm : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.two_pi_pos]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.one_le_pi_div_two])
  have hremainderNorm :
      ‖I * lower - I * upper + left‖ ≤
        ‖lower‖ + ‖upper‖ + ‖left‖ := by
    calc
      ‖I * lower - I * upper + left‖ ≤
          ‖I * lower - I * upper‖ + ‖left‖ := norm_add_le _ _
      _ ≤ (‖I * lower‖ + ‖I * upper‖) + ‖left‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = ‖lower‖ + ‖upper‖ + ‖left‖ := by simp
  have hproduct :
      ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ *
          ‖I * lower - I * upper + left‖ ≤
        1640 * A * C * E := by
    calc
      ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ *
        ‖I * lower - I * upper + left‖ ≤
        1 * ‖I * lower - I * upper + left‖ :=
        mul_le_mul_of_nonneg_right hinvNorm (norm_nonneg _)
      _ ≤ ‖lower‖ + ‖upper‖ + ‖left‖ := by
        simpa using hremainderNorm
      _ ≤ (640 * A * C * E) + (640 * A * C * E) + 720 * A * E := by
        gcongr
      _ ≤ 1640 * A * C * E := by
        nlinarith
  simpa [dirichletExplicitFormulaShallowContourRemainder,
    lower, upper, left, norm_mul] using hproduct

end

end BoundedGaps.Maynard
