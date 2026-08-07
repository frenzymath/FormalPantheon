import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateInterior
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaContourEdges
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaSelectedHeight
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaShallowCorrection
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionHorizontalEdge
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionLeftEdge
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaHorizontalEdge
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaLeftEdge

/-!
# Selected-height Dirichlet explicit-formula contour

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115, moves the
modified logarithmic-derivative integral to a height selected uniformly before
the Perron endpoint. This file composes the exact shallow rectangle, the two
horizontal estimates, the fixed left-edge estimate, the shallow candidate
correction, and the selected/requested zero shell.

It does not identify the normalized right edge with a prime-counting sum.
That modified Perron inversion is the separate SEM-533 milestone. Semantic
review: `SEM-532`.
-/

namespace BoundedGaps.Maynard

open Complex Set
open scoped BigOperators Interval

noncomputable section

/-- One height, selected before `x`, gives the source-shaped shallow contour
expansion at every later Perron endpoint. -/
theorem
    exists_nat_norm_dirichletExplicitFormulaNormalizedRightEdge_sub_mainZeroTerms_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∃ C : ℕ, 2 ≤ C ∧
        ∀ (q : ℕ) [NeZero q]
          (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
            ∀ T : ℝ, 2 ≤ T →
              ∃ U : ℝ, U ∈ Set.Icc T (T + 1) ∧
                (∀ rho : ℂ,
                  (rho ≠ 1 ∨ chi ≠ 1) →
                    DirichletCharacter.LFunction chi rho = 0 →
                      (1 / ((C : ℝ) *
                          Real.log ((q : ℝ) * (T + 2))) ≤
                        |U - rho.im|) ∧
                      (1 / ((C : ℝ) *
                          Real.log ((q : ℝ) * (T + 2))) ≤
                        |U + rho.im|)) ∧
                ∀ x : ℝ, T ≤ x →
                  ‖dirichletExplicitFormulaNormalizedRightEdge chi x U -
                      dirichletExplicitFormulaMainZeroTerms chi x T‖ ≤
                    1700 * (A : ℝ) * C *
                      dirichletExplicitFormulaErrorScale x q T := by
  obtain ⟨Aph, hAph, hprimitiveHorizontal⟩ :=
    exists_nat_norm_intervalIntegral_dirichletExplicitFormulaIntegrand_primitive_horizontal_le
  obtain ⟨Azh, hAzh, hzetaHorizontal⟩ :=
    exists_nat_norm_intervalIntegral_dirichletExplicitFormulaIntegrand_modOne_horizontal_le
  obtain ⟨Apl, hApl, hprimitiveLeft⟩ :=
    exists_nat_norm_intervalIntegral_dirichletExplicitFormulaIntegrand_primitive_leftEdge_le
  obtain ⟨Azl, hAzl, hzetaLeft⟩ :=
    exists_nat_norm_intervalIntegral_dirichletExplicitFormulaIntegrand_modOne_leftEdge_le
  obtain ⟨As, hAs, hshell⟩ :=
    exists_nat_norm_dirichletNontrivialZeroKernelSum_selected_sub_requested_le
  obtain ⟨C, hC, hselect⟩ :=
    exists_nat_guardedLFunctionZero_twoSided_clearance
  let A := Aph + Azh + Apl + Azl + As
  have hA : 37 ≤ A := by
    dsimp [A]
    omega
  have hAphA : Aph ≤ A := by dsimp [A]; omega
  have hAzhA : Azh ≤ A := by dsimp [A]; omega
  have hAplA : Apl ≤ A := by dsimp [A]; omega
  have hAzlA : Azl ≤ A := by dsimp [A]; omega
  have hAsA : As ≤ A := by dsimp [A]; omega
  refine ⟨A, hA, C, hC, ?_⟩
  intro q _ chi hchi T hT
  obtain ⟨U, hU, hclear⟩ := hselect q chi T hT
  refine ⟨U, hU, hclear, ?_⟩
  intro x hTx
  let E := dirichletExplicitFormulaErrorScale x q T
  have hx : 2 ≤ x := hT.trans hTx
  have hxone : 1 < x := one_lt_two.trans_le hx
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hUpos : 0 < U := by linarith [hT, hU.1]
  have hCReal : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hCNonneg : (0 : ℝ) ≤ C := by linarith
  have hE : 0 ≤ E := by
    dsimp [E, dirichletExplicitFormulaErrorScale]
    positivity
  have hscaleWithC :
      ∀ (Ai : ℕ), Ai ≤ A → ∀ K : ℝ, 0 ≤ K →
        K * (Ai : ℝ) * C * E ≤ K * (A : ℝ) * C * E := by
    intro Ai hAi K hK
    apply mul_le_mul_of_nonneg_right _ hE
    apply mul_le_mul_of_nonneg_right _ hCNonneg
    apply mul_le_mul_of_nonneg_left _ hK
    exact_mod_cast hAi
  have hscaleWithoutC :
      ∀ (Ai : ℕ), Ai ≤ A → ∀ K : ℝ, 0 ≤ K →
        K * (Ai : ℝ) * E ≤ K * (A : ℝ) * E := by
    intro Ai hAi K hK
    apply mul_le_mul_of_nonneg_right _ hE
    apply mul_le_mul_of_nonneg_left _ hK
    exact_mod_cast hAi
  have hinside :
      dirichletExplicitFormulaCandidateSingularities chi
          (((-1 / 2 : ℝ) : ℂ) - U * I)
          (((1 + 1 / Real.log x : ℝ) : ℂ) + U * I) ⊆
        interior (Complex.Rectangle
          (((-1 / 2 : ℝ) : ℂ) - U * I)
          (((1 + 1 / Real.log x : ℝ) : ℂ) + U * I)) := by
    convert
      dirichletExplicitFormulaCandidateSingularities_subset_interior_of_clearance
        chi 0 C hxone hT hU hC hclear using 1 <;> norm_num
  have hcontour :=
    dirichletExplicitFormulaNormalizedRightEdge_eq_sum_add_remainder
      chi hxone hUpos hinside
  have hcandidates :=
    sum_dirichletExplicitFormulaShallowCandidateContribution_eq_mainZeroTerms_add_correction_of_isPrimitive
      chi hchi x U hxone
  have hcorrection :=
    norm_dirichletExplicitFormulaShallowMainTermCorrection_le_four_mul_errorScale
      chi hT hTx
  have hshellRaw := hshell q chi hchi x T U hT hTx hU
  have hedgeBounds :
      (‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
          dirichletExplicitFormulaIntegrand chi x
            ((sigma : ℂ) + U * I)‖ ≤
          640 * (A : ℝ) * C * E) ∧
      (‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
          dirichletExplicitFormulaIntegrand chi x
            ((sigma : ℂ) - U * I)‖ ≤
          640 * (A : ℝ) * C * E) ∧
      ‖∫ t in -U..U,
          dirichletExplicitFormulaIntegrand chi x
            (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        720 * (A : ℝ) * E := by
    by_cases hqOne : q = 1
    · subst q
      have hchiOne : chi = (1 : DirichletCharacter ℂ 1) :=
        Subsingleton.elim _ _
      subst chi
      have hclearOne : ∀ rho : ℂ,
          (rho ≠ 1 ∨ (1 : DirichletCharacter ℂ 1) ≠ 1) →
            DirichletCharacter.LFunction
                (1 : DirichletCharacter ℂ 1) rho = 0 →
              (1 / ((C : ℝ) * Real.log (T + 2)) ≤
                |U - rho.im|) ∧
              (1 / ((C : ℝ) * Real.log (T + 2)) ≤
                |U + rho.im|) := by
        simpa using hclear
      have hh := hzetaHorizontal C hC x T U hT hTx hU hclearOne
      have hl := hzetaLeft x T U hT hTx hU
      have hhUpper :
          ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
              dirichletExplicitFormulaIntegrand
                (1 : DirichletCharacter ℂ 1) x
                ((sigma : ℂ) + U * I)‖ ≤
            640 * (Azh : ℝ) * C * E := by
        calc
          _ ≤ 640 * (Azh : ℝ) * C * x * Real.log x ^ 2 / T := hh.1
          _ = 640 * (Azh : ℝ) * C * E := by
            dsimp [E, dirichletExplicitFormulaErrorScale]
            ring_nf
      have hhLower :
          ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
              dirichletExplicitFormulaIntegrand
                (1 : DirichletCharacter ℂ 1) x
                ((sigma : ℂ) - U * I)‖ ≤
            640 * (Azh : ℝ) * C * E := by
        calc
          _ ≤ 640 * (Azh : ℝ) * C * x * Real.log x ^ 2 / T := hh.2
          _ = 640 * (Azh : ℝ) * C * E := by
            dsimp [E, dirichletExplicitFormulaErrorScale]
            ring_nf
      have hlBound :
          ‖∫ t in -U..U,
              dirichletExplicitFormulaIntegrand
                (1 : DirichletCharacter ℂ 1) x
                (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
            720 * (Azl : ℝ) * E := by
        calc
          _ ≤ 720 * (Azl : ℝ) * x * Real.log x ^ 2 / T := hl
          _ = 720 * (Azl : ℝ) * E := by
            dsimp [E, dirichletExplicitFormulaErrorScale]
            ring_nf
      exact ⟨hhUpper.trans (hscaleWithC Azh hAzhA 640 (by norm_num)),
        hhLower.trans (hscaleWithC Azh hAzhA 640 (by norm_num)),
        hlBound.trans (hscaleWithoutC Azl hAzlA 720 (by norm_num))⟩
    · have hq : 1 < q := by
        have hqpos := Nat.pos_of_ne_zero (NeZero.ne q)
        omega
      have hh :=
        hprimitiveHorizontal C hC q hq chi hchi x T U hT hTx hU hclear
      have hl := hprimitiveLeft q hq chi hchi x T U hT hTx hU
      have hlogEq :
          Real.log ((q : ℝ) * x) = Real.log (x * (q : ℝ)) := by
        rw [mul_comm]
      have hhUpper :
          ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
              dirichletExplicitFormulaIntegrand chi x
                ((sigma : ℂ) + U * I)‖ ≤
            640 * (Aph : ℝ) * C * E := by
        calc
          _ ≤ 640 * (Aph : ℝ) * C * x *
              Real.log ((q : ℝ) * x) ^ 2 / T := hh.1
          _ = 640 * (Aph : ℝ) * C * E := by
            rw [hlogEq]
            dsimp [E, dirichletExplicitFormulaErrorScale]
            ring_nf
      have hhLower :
          ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
              dirichletExplicitFormulaIntegrand chi x
                ((sigma : ℂ) - U * I)‖ ≤
            640 * (Aph : ℝ) * C * E := by
        calc
          _ ≤ 640 * (Aph : ℝ) * C * x *
              Real.log ((q : ℝ) * x) ^ 2 / T := hh.2
          _ = 640 * (Aph : ℝ) * C * E := by
            rw [hlogEq]
            dsimp [E, dirichletExplicitFormulaErrorScale]
            ring_nf
      have hlBound :
          ‖∫ t in -U..U,
              dirichletExplicitFormulaIntegrand chi x
                (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
            720 * (Apl : ℝ) * E := by
        calc
          _ ≤ 720 * (Apl : ℝ) * x *
              Real.log ((q : ℝ) * x) ^ 2 / T := hl
          _ = 720 * (Apl : ℝ) * E := by
            rw [hlogEq]
            dsimp [E, dirichletExplicitFormulaErrorScale]
            ring_nf
      exact ⟨hhUpper.trans (hscaleWithC Aph hAphA 640 (by norm_num)),
        hhLower.trans (hscaleWithC Aph hAphA 640 (by norm_num)),
        hlBound.trans (hscaleWithoutC Apl hAplA 720 (by norm_num))⟩
  have hremainder :=
    norm_dirichletExplicitFormulaShallowContourRemainder_le
      chi hCReal hE hedgeBounds.2.1 hedgeBounds.1 hedgeBounds.2.2
  have hshellBound :
      ‖dirichletNontrivialZeroKernelSum chi x U -
          dirichletNontrivialZeroKernelSum chi x T‖ ≤
        32 * (A : ℝ) * E := by
    exact hshellRaw.trans (hscaleWithoutC As hAsA 32 (by norm_num))
  have hmainDifference :
      ‖dirichletExplicitFormulaMainZeroTerms chi x U -
          dirichletExplicitFormulaMainZeroTerms chi x T‖ =
        ‖dirichletNontrivialZeroKernelSum chi x U -
          dirichletNontrivialZeroKernelSum chi x T‖ := by
    have heq :
        dirichletExplicitFormulaMainZeroTerms chi x U -
            dirichletExplicitFormulaMainZeroTerms chi x T =
          -(dirichletNontrivialZeroKernelSum chi x U -
            dirichletNontrivialZeroKernelSum chi x T) := by
      simp only [dirichletExplicitFormulaMainZeroTerms]
      ring_nf
    rw [heq, norm_neg]
  have hdecomp :
      dirichletExplicitFormulaNormalizedRightEdge chi x U -
          dirichletExplicitFormulaMainZeroTerms chi x T =
        dirichletExplicitFormulaShallowContourRemainder chi x U +
          dirichletExplicitFormulaShallowMainTermCorrection chi x +
          (dirichletExplicitFormulaMainZeroTerms chi x U -
            dirichletExplicitFormulaMainZeroTerms chi x T) := by
    rw [hcontour, hcandidates]
    ring_nf
  rw [hdecomp]
  calc
    _ ≤ ‖dirichletExplicitFormulaShallowContourRemainder chi x U‖ +
          ‖dirichletExplicitFormulaShallowMainTermCorrection chi x‖ +
          ‖dirichletExplicitFormulaMainZeroTerms chi x U -
            dirichletExplicitFormulaMainZeroTerms chi x T‖ := norm_add₃_le
    _ ≤ 1640 * (A : ℝ) * C * E + 4 * E + 32 * (A : ℝ) * E := by
      rw [hmainDifference]
      gcongr
    _ ≤ 1700 * (A : ℝ) * C * E := by
      have hAReal : (37 : ℝ) ≤ A := by exact_mod_cast hA
      have hANonneg : (0 : ℝ) ≤ A := by linarith
      have hAE : 0 ≤ (A : ℝ) * E := mul_nonneg hANonneg hE
      nlinarith [mul_nonneg (sub_nonneg.mpr hCReal) hAE,
        mul_nonneg (sub_nonneg.mpr hAReal) hE]
    _ = 1700 * (A : ℝ) * C *
        dirichletExplicitFormulaErrorScale x q T := by rfl

end

end BoundedGaps.Maynard
