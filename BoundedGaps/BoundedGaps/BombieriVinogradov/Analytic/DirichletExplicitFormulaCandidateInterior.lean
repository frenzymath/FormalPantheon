import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateSingularities
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaVerticalEdges
import BoundedGaps.BombieriVinogradov.Analytic.DirichletGoodHeightZeroCoverage

/-!
# Interior containment at a selected Dirichlet explicit-formula height

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115, selects a
horizontal height and moves the contour with real edges `-N-1/2` and
`1+1/log x` across ordinary L-function zeros and the separate principal pole.
This file combines SEM-502, SEM-513, and SEM-514 to put every candidate
strictly inside that same selected rectangle while retaining the quantitative
horizontal clearance.

Common-radius selection and circle consumption remain separate. Semantic
review: `SEM-515`.
-/

namespace BoundedGaps.Maynard

open Complex Set

noncomputable section

/-- Quantitative two-sided clearance places every guarded candidate strictly
inside the prescribed explicit-formula rectangle. -/
theorem
    dirichletExplicitFormulaCandidateSingularities_subset_interior_of_clearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x T U : ℝ} (N C : ℕ)
    (hx : 1 < x) (hT : 2 ≤ T) (hU : U ∈ Set.Icc T (T + 1))
    (hC : 2 ≤ C)
    (hclear : ∀ rho : ℂ,
      (rho ≠ 1 ∨ chi ≠ 1) →
        DirichletCharacter.LFunction chi rho = 0 →
          (1 / ((C : ℝ) * Real.log ((q : ℝ) * (T + 2))) ≤
              |U - rho.im|) ∧
          (1 / ((C : ℝ) * Real.log ((q : ℝ) * (T + 2))) ≤
              |U + rho.im|)) :
    dirichletExplicitFormulaCandidateSingularities chi
        (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) - U * Complex.I)
        (((1 + 1 / Real.log x : ℝ) : ℂ) + U * Complex.I) ⊆
      interior (Complex.Rectangle
        (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) - U * Complex.I)
        (((1 + 1 / Real.log x : ℝ) : ℂ) + U * Complex.I)) := by
  have hUpos : 0 < U := by linarith [hT, hU.1]
  have himEdges : -U ≤ U := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hreEdges : -(N : ℝ) - 1 / 2 ≤ 1 + 1 / Real.log x := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith [one_div_pos.mpr hlogx]
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hscale : (1 : ℝ) < (q : ℝ) * (T + 2) := by
    have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq
    nlinarith [mul_le_mul hq (show (4 : ℝ) ≤ T + 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 4) hq0]
  have hlogScale : 0 < Real.log ((q : ℝ) * (T + 2)) :=
    Real.log_pos hscale
  have hCreal : (0 : ℝ) < C := by exact_mod_cast (by omega : 0 < C)
  have hdelta :
      0 < 1 / ((C : ℝ) * Real.log ((q : ℝ) * (T + 2))) :=
    one_div_pos.mpr (mul_pos hCreal hlogScale)
  intro rho hrho
  rw [mem_dirichletExplicitFormulaCandidateSingularities_iff] at hrho
  have hrect := hrho.1
  rw [Complex.Rectangle, Complex.mem_reProdIm] at hrect
  norm_num at hrect
  have hreEdges' : -(N : ℝ) - 1 / 2 ≤ 1 + (Real.log x)⁻¹ := by
    simpa only [one_div] using hreEdges
  rw [uIcc_of_le hreEdges', uIcc_of_le himEdges] at hrect
  have hrealNe : rho.re ≠ -(N : ℝ) - 1 / 2 ∧
      rho.re ≠ 1 + 1 / Real.log x := by
    rcases hrho.2 with hpole | hzero
    · rcases hpole with ⟨_, rfl⟩
      constructor
      · have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        norm_num
        linarith
      · intro h
        have hinv : 0 < 1 / Real.log x := one_div_pos.mpr hlogx
        change (1 : ℝ) = 1 + 1 / Real.log x at h
        linarith
    · have hvert := LFunction_ne_zero_on_dirichletExplicitFormulaVerticalEdges
          chi x hx N rho.im
      constructor
      · intro hre
        apply hvert.1
        have hrhoEq :
            (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + rho.im * I) = rho := by
          apply Complex.ext
          · simpa using hre.symm
          · simp
        rw [hrhoEq]
        exact hzero.2
      · intro hre
        apply hvert.2
        have hrhoEq :
            (((1 + 1 / Real.log x : ℝ) : ℂ) + rho.im * I) = rho := by
          apply Complex.ext
          · simpa using hre.symm
          · simp
        rw [hrhoEq]
        exact hzero.2
  have himNe : rho.im ≠ -U ∧ rho.im ≠ U := by
    rcases hrho.2 with hpole | hzero
    · rcases hpole with ⟨_, rfl⟩
      constructor <;> norm_num <;> linarith
    · have hc := hclear rho hzero.1 hzero.2
      constructor
      · intro him
        rw [him, add_neg_cancel, abs_zero] at hc
        linarith [hc.2]
      · intro him
        rw [him, sub_self, abs_zero] at hc
        linarith [hc.1]
  have hright : rho.re ≤ 1 + 1 / Real.log x := by
    simpa only [one_div] using hrect.1.2
  have hcoordinates :
      rho.re ∈ Ioo (-(N : ℝ) - 1 / 2) (1 + 1 / Real.log x) ∧
        rho.im ∈ Ioo (-U) U := by
    exact ⟨⟨lt_of_le_of_ne hrect.1.1 hrealNe.1.symm,
        lt_of_le_of_ne hright hrealNe.2⟩,
      ⟨lt_of_le_of_ne hrect.2.1 himNe.1.symm,
        lt_of_le_of_ne hrect.2.2 himNe.2⟩⟩
  rw [Complex.Rectangle, Complex.interior_reProdIm]
  norm_num
  rw [uIcc_of_le hreEdges', uIcc_of_le himEdges,
    interior_Icc, interior_Icc, Complex.mem_reProdIm]
  simpa only [one_div] using hcoordinates

/-- One good height places every explicit-formula candidate strictly inside
the prescribed rectangle while retaining quantitative horizontal clearance. -/
theorem
    exists_nat_dirichletExplicitFormulaCandidateSingularities_subset_interior :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q)
        (x T : ℝ) (N : ℕ),
          1 < x → 2 ≤ T →
            ∃ T' : ℝ, T' ∈ Set.Icc T (T + 1) ∧
              (∀ rho : ℂ,
                (rho ≠ 1 ∨ chi ≠ 1) →
                  DirichletCharacter.LFunction chi rho = 0 →
                    (1 / ((C : ℝ) *
                        Real.log ((q : ℝ) * (T + 2))) ≤
                      |T' - rho.im|) ∧
                    (1 / ((C : ℝ) *
                        Real.log ((q : ℝ) * (T + 2))) ≤
                      |T' + rho.im|)) ∧
              (dirichletExplicitFormulaCandidateSingularities chi
                  (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) - T' * Complex.I)
                  (((1 + 1 / Real.log x : ℝ) : ℂ) + T' * Complex.I) ⊆
                interior
                  (Complex.Rectangle
                    (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) - T' * Complex.I)
                    (((1 + 1 / Real.log x : ℝ) : ℂ) + T' * Complex.I))) := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_nat_guardedLFunctionZero_twoSided_clearance
  refine ⟨C, hC, ?_⟩
  intro q _ chi x T N hx hT
  obtain ⟨T', hT', hclear⟩ := hselect q chi T hT
  refine ⟨T', hT', hclear, ?_⟩
  exact
    dirichletExplicitFormulaCandidateSingularities_subset_interior_of_clearance
      chi N C hx hT hT' hC hclear

end

end BoundedGaps.Maynard
