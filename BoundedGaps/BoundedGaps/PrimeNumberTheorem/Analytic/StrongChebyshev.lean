import BoundedGaps.BombieriVinogradov.Analytic.CenteredCharacterReduction
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormula
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNonexceptionalZeroSum
import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfiszScale

/-!
# Strong Chebyshev estimate

This file specializes the local Dirichlet explicit formula and zero-sum
estimate to the unique character modulo one. It implements the natural-
endpoint estimate in the proof of `KoukoulopoulosDistributionPrimesPrelim2022`,
Theorem 8.1, printed p. 89. Semantic review: `SEM-579`.
-/

namespace BoundedGaps.PrimeNumberTheorem

open Filter

noncomputable section

/-- The character twist at modulus one is the ordinary Chebyshev function. -/
theorem twistedChebyshevSum_one_eq_psi (x : ℕ) :
    BoundedGaps.Maynard.twistedChebyshevSum x 1
        (1 : DirichletCharacter ℂ 1) =
      (Chebyshev.psi (x : ℝ) : ℂ) := by
  have h := BoundedGaps.Maynard.centeredTwistedChebyshevSum_one x
  rw [BoundedGaps.Maynard.centeredTwistedChebyshevSum, if_pos rfl] at h
  exact sub_eq_zero.mp h

/-- The exceptional-zero filter is empty for the unique character modulo one. -/
theorem dirichletExceptionalLFunctionZerosFinset_one_eq_empty
    (M : ℕ) (T : ℝ) :
    BoundedGaps.Maynard.dirichletExceptionalLFunctionZerosFinset
        M (1 : DirichletCharacter ℂ 1) T = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro rho hrho
  have hexceptional :=
    (BoundedGaps.Maynard.mem_dirichletExceptionalLFunctionZerosFinset_iff.mp
      hrho).2.2
  obtain ⟨_, _, _, _, psi, hpsi, _⟩ := hexceptional
  exact hpsi.1 (DirichletCharacter.level_one psi)

/-- Consequently, the grouped exceptional kernel sum at modulus one vanishes. -/
theorem dirichletExceptionalZeroKernelSum_one_eq_zero
    (M : ℕ) (x T : ℝ) :
    BoundedGaps.Maynard.dirichletExceptionalZeroKernelSum
        M (1 : DirichletCharacter ℂ 1) x T = 0 := by
  rw [BoundedGaps.Maynard.dirichletExceptionalZeroKernelSum,
    dirichletExceptionalLFunctionZerosFinset_one_eq_empty]
  simp

/-- The strong natural-endpoint estimate for the Chebyshev psi function. -/
theorem exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℕ, X0 ≤ x →
          |Chebyshev.psi (x : ℝ) - (x : ℝ)| ≤
            C * ((x : ℝ) *
              Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨K, hK, hformula⟩ :=
    BoundedGaps.Maynard.exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le
  obtain ⟨M, A, hM, _hA, _hcard, hnonexceptional⟩ :=
    BoundedGaps.Maynard.exists_nat_card_dirichletExceptionalLFunctionZerosFinset_le_one_and_norm_dirichletNonexceptionalZeroKernelSum_le
  let cN : ℝ := 1 / (8 * (M : ℝ) ^ 2)
  let c : ℝ := min (1 / 2 : ℝ) cN
  let C : ℝ := (K : ℝ) + 96 * (A : ℝ)
  have hcN : 0 < cN := by
    dsimp [cN]
    have hMpos : (0 : ℝ) < M := by
      exact_mod_cast Nat.zero_lt_of_lt hM
    positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) hcN
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hevent :=
    BoundedGaps.Maynard.eventually_siegelWalfiszHeight_conditions
      1 one_pos M hM
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨X0, hX0⟩ := hevent
  have hX0four : 4 ≤ X0 := (hX0 X0 le_rfl).1
  refine ⟨C, c, hC, hc, X0, hX0four, ?_⟩
  intro x hxX
  obtain ⟨hx, hxlog, hheightTwo, hheightX, _hlogHeight,
    habsorbFour, habsorbTwo⟩ := hX0 x hxX
  let T : ℝ := BoundedGaps.Maynard.siegelWalfiszHeight x
  let u : ℝ := Real.sqrt (Real.log (x : ℝ))
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have hqHeight : (((1 : ℕ) : ℝ)) ≤
      BoundedGaps.Maynard.siegelWalfiszHeight x :=
    (by norm_num : (((1 : ℕ) : ℝ)) ≤ 2).trans hheightTwo
  have hformulaRaw := hformula 1
    (1 : DirichletCharacter ℂ 1) T hheightTwo x hx hheightX
  have hformulaHeight :
      ‖BoundedGaps.Maynard.twistedChebyshevSum x 1
            (1 : DirichletCharacter ℂ 1) -
          BoundedGaps.Maynard.dirichletExplicitFormulaMainZeroTerms
            (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ ≤
        (K : ℝ) * ((x : ℝ) * Real.exp (-(1 / 2 : ℝ) * u)) := by
    exact hformulaRaw.trans
      (by
        simpa [T, u] using
          (BoundedGaps.Maynard.mul_dirichletExplicitFormulaErrorScale_siegelWalfiszHeight_le
            (K : ℝ) (Nat.cast_nonneg K) hxlog hqHeight habsorbFour))
  have hnonexceptionalRaw := hnonexceptional 1
    (1 : DirichletCharacter ℂ 1) (x : ℝ) T
      (by exact_mod_cast hx) hheightTwo hheightX
  have hnonexceptionalHeight :
      ‖BoundedGaps.Maynard.dirichletNonexceptionalZeroKernelSum M
          (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ ≤
        96 * (A : ℝ) * ((x : ℝ) * Real.exp (-cN * u)) := by
    exact hnonexceptionalRaw.trans
      (by
        simpa only [T, u, cN] using
          (BoundedGaps.Maynard.dirichletNonexceptionalSiegelWalfiszEnvelope_le
            A M hM hxlog hqHeight habsorbTwo))
  have hcHalf : c ≤ (1 / 2 : ℝ) := min_le_left _ _
  have hcNbound : c ≤ cN := min_le_right _ _
  have hformulaCommon :
      ‖BoundedGaps.Maynard.twistedChebyshevSum x 1
            (1 : DirichletCharacter ℂ 1) -
          BoundedGaps.Maynard.dirichletExplicitFormulaMainZeroTerms
            (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ ≤
        (K : ℝ) * ((x : ℝ) * Real.exp (-c * u)) := by
    apply hformulaHeight.trans
    gcongr
  have hnonexceptionalCommon :
      ‖BoundedGaps.Maynard.dirichletNonexceptionalZeroKernelSum M
          (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ ≤
        96 * (A : ℝ) * ((x : ℝ) * Real.exp (-c * u)) := by
    apply hnonexceptionalHeight.trans
    gcongr
  have hmain :
      BoundedGaps.Maynard.dirichletExplicitFormulaMainZeroTerms
          (1 : DirichletCharacter ℂ 1) (x : ℝ) T =
        ((x : ℝ) : ℂ) -
          BoundedGaps.Maynard.dirichletNonexceptionalZeroKernelSum M
            (1 : DirichletCharacter ℂ 1) (x : ℝ) T := by
    rw [BoundedGaps.Maynard.dirichletExplicitFormulaMainZeroTerms,
      if_pos rfl,
      BoundedGaps.Maynard.dirichletNontrivialZeroKernelSum_eq_nonexceptional_add_exceptional,
      dirichletExceptionalZeroKernelSum_one_eq_zero]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  change ‖((Chebyshev.psi (x : ℝ) - (x : ℝ) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.ofReal_sub, ← twistedChebyshevSum_one_eq_psi]
  calc
    ‖BoundedGaps.Maynard.twistedChebyshevSum x 1
          (1 : DirichletCharacter ℂ 1) - ((x : ℝ) : ℂ)‖ =
        ‖(BoundedGaps.Maynard.twistedChebyshevSum x 1
            (1 : DirichletCharacter ℂ 1) -
              BoundedGaps.Maynard.dirichletExplicitFormulaMainZeroTerms
                (1 : DirichletCharacter ℂ 1) (x : ℝ) T) -
          BoundedGaps.Maynard.dirichletNonexceptionalZeroKernelSum M
            (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ := by
      rw [hmain]
      congr 1
      ring
    _ ≤ ‖BoundedGaps.Maynard.twistedChebyshevSum x 1
            (1 : DirichletCharacter ℂ 1) -
              BoundedGaps.Maynard.dirichletExplicitFormulaMainZeroTerms
                (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ +
          ‖BoundedGaps.Maynard.dirichletNonexceptionalZeroKernelSum M
            (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ := norm_sub_le _ _
    _ ≤ (K : ℝ) * ((x : ℝ) * Real.exp (-c * u)) +
          96 * (A : ℝ) * ((x : ℝ) * Real.exp (-c * u)) :=
      add_le_add hformulaCommon hnonexceptionalCommon
    _ = C * ((x : ℝ) *
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
      dsimp [C, u]
      ring

end

end BoundedGaps.PrimeNumberTheorem
