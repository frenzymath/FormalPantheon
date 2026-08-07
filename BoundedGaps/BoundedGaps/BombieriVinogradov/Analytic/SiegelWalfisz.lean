import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormula
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNonexceptionalZeroSum
import BoundedGaps.BombieriVinogradov.Analytic.SiegelExceptionalZeroKernel
import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfiszScale

/-!
# Siegel--Walfisz for nonprincipal character twists

This file composes the arbitrary-character explicit formula, the complete
exceptional/nonexceptional zero partition, and Siegel's exceptional-kernel
bound at the source height `exp (sqrt (log x))`.

Sources: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorems 11.3, 12.4,
and 12.10, and `DavenportMNTCh22SW1980`, equations (2)--(3). Semantic review:
`SEM-564`.
-/

namespace BoundedGaps.Maynard

open Filter

noncomputable section

/-- The natural-endpoint Siegel--Walfisz estimate for every complex
nonprincipal Dirichlet character, primitive or imprimitive. -/
theorem exists_siegelWalfisz_norm_twistedChebyshevSum_le :
    ∀ D : ℝ, 0 < D →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ (q : ℕ) [NeZero q]
              (chi : DirichletCharacter ℂ q), chi ≠ 1 →
                (q : ℝ) ≤ Real.log (x : ℝ) ^ D →
                  ‖twistedChebyshevSum x q chi‖ ≤
                    C * ((x : ℝ) * Real.exp
                      (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  intro D hD
  obtain ⟨K, _hK, hformula⟩ :=
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le
  obtain ⟨M, A, hM, _hA, _hcard, hnonexceptional⟩ :=
    exists_nat_card_dirichletExceptionalLFunctionZerosFinset_le_one_and_norm_dirichletNonexceptionalZeroKernelSum_le
  obtain ⟨cE, hcE, hexceptional⟩ :=
    exists_norm_dirichletExceptionalZeroKernelSum_lt D hD
  let cN : ℝ := 1 / (8 * (M : ℝ) ^ 2)
  let c : ℝ := min cE (min cN (1 / 2 : ℝ))
  let C : ℝ := (K : ℝ) + 96 * (A : ℝ) + 2
  have hcN : 0 < cN := by
    dsimp [cN]
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hM
    positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hcE (lt_min hcN (by norm_num))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hevent := eventually_siegelWalfiszHeight_conditions D hD M hM
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨X0, hX0⟩ := hevent
  have hX0four : 4 ≤ X0 := (hX0 X0 le_rfl).1
  refine ⟨C, c, hC, hc, X0, hX0four, ?_⟩
  intro x hxX q _ chi hchi hqlog
  obtain ⟨hx, hxlog, hheightTwo, hheightX, hlogHeight,
    habsorbFour, habsorbTwo⟩ := hX0 x hxX
  let T : ℝ := siegelWalfiszHeight x
  let u : ℝ := Real.sqrt (Real.log (x : ℝ))
  have hxReal : (4 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hqHeight : (q : ℝ) ≤ siegelWalfiszHeight x :=
    hqlog.trans hlogHeight
  have hformulaRaw := hformula q chi T hheightTwo x hx hheightX
  have hformulaHeight :
      ‖twistedChebyshevSum x q chi -
          dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ ≤
        (K : ℝ) * ((x : ℝ) * Real.exp (-(1 / 2 : ℝ) * u)) := by
    exact hformulaRaw.trans
      (by
        simpa [T, u] using
          (mul_dirichletExplicitFormulaErrorScale_siegelWalfiszHeight_le
            (K : ℝ) (Nat.cast_nonneg K) hxlog hqHeight habsorbFour))
  have hnonexceptionalRaw :=
    hnonexceptional q chi (x : ℝ) T hxReal hheightTwo hheightX
  have hnonexceptionalHeight :
      ‖dirichletNonexceptionalZeroKernelSum M chi (x : ℝ) T‖ ≤
        96 * (A : ℝ) * ((x : ℝ) * Real.exp (-cN * u)) := by
    exact hnonexceptionalRaw.trans
      (by
        simpa [T, u, cN] using
          (dirichletNonexceptionalSiegelWalfiszEnvelope_le
            A M hM hxlog hqHeight habsorbTwo))
  have hexceptionalRaw :=
    hexceptional M hM q chi (x : ℝ) T hxpos hxlog hqlog
  have hcEbound : c ≤ cE := min_le_left _ _
  have hcNbound : c ≤ cN :=
    (min_le_right cE (min cN (1 / 2 : ℝ))).trans (min_le_left _ _)
  have hcHalf : c ≤ (1 / 2 : ℝ) :=
    (min_le_right cE (min cN (1 / 2 : ℝ))).trans (min_le_right _ _)
  have hformulaCommon :
      ‖twistedChebyshevSum x q chi -
          dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ ≤
        (K : ℝ) * ((x : ℝ) * Real.exp (-c * u)) := by
    apply hformulaHeight.trans
    gcongr
  have hnonexceptionalCommon :
      ‖dirichletNonexceptionalZeroKernelSum M chi (x : ℝ) T‖ ≤
        96 * (A : ℝ) * ((x : ℝ) * Real.exp (-c * u)) := by
    apply hnonexceptionalHeight.trans
    gcongr
  have hexceptionalCommon :
      ‖dirichletExceptionalZeroKernelSum M chi (x : ℝ) T‖ ≤
        2 * ((x : ℝ) * Real.exp (-c * u)) := by
    apply (le_of_lt hexceptionalRaw).trans
    gcongr
  have hpartition :=
    dirichletNontrivialZeroKernelSum_eq_nonexceptional_add_exceptional
      M chi (x : ℝ) T
  have hmainZero :
      dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T =
        -(dirichletNonexceptionalZeroKernelSum M chi (x : ℝ) T +
          dirichletExceptionalZeroKernelSum M chi (x : ℝ) T) := by
    rw [dirichletExplicitFormulaMainZeroTerms, hpartition, if_neg hchi]
    ring
  calc
    ‖twistedChebyshevSum x q chi‖ =
        ‖(twistedChebyshevSum x q chi -
            dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T) -
          (dirichletNonexceptionalZeroKernelSum M chi (x : ℝ) T +
            dirichletExceptionalZeroKernelSum M chi (x : ℝ) T)‖ := by
      rw [hmainZero]
      congr 1
      ring
    _ ≤ ‖twistedChebyshevSum x q chi -
            dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ +
          ‖dirichletNonexceptionalZeroKernelSum M chi (x : ℝ) T +
            dirichletExceptionalZeroKernelSum M chi (x : ℝ) T‖ :=
      norm_sub_le _ _
    _ ≤ (K : ℝ) * ((x : ℝ) * Real.exp (-c * u)) +
          (96 * (A : ℝ) * ((x : ℝ) * Real.exp (-c * u)) +
            2 * ((x : ℝ) * Real.exp (-c * u))) := by
      apply add_le_add hformulaCommon
      exact (norm_add_le _ _).trans
        (add_le_add hnonexceptionalCommon hexceptionalCommon)
    _ = C * ((x : ℝ) * Real.exp
        (-c * Real.sqrt (Real.log (x : ℝ)))) := by
      dsimp [C, u]
      ring

end

end BoundedGaps.Maynard
