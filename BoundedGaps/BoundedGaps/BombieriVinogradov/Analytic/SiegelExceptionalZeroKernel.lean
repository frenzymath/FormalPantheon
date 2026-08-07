import BoundedGaps.BombieriVinogradov.Analytic.DirichletExceptionalZeroKernel
import BoundedGaps.BombieriVinogradov.Analytic.SiegelZeroFreeRegion

/-!
# Siegel control of the exceptional zero kernel

Siegel's real-character zero-free region supplies the uniform strict gap
required by the exceptional-kernel estimate. The constant is halved before
contraposition so that the nonvanishing region gives the strict zero bound
consumed by the kernel argument.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.10, printed
p. 127, and Theorem 12.4, printed pp. 121--122. Semantic review: `SEM-563`.
-/

noncomputable section

namespace BoundedGaps.Maynard

/-- Every complete exceptional point satisfies a strict Siegel-shaped gap,
uniformly in the synchronized exceptional scale. -/
theorem exists_dirichletExceptionalLFunctionZeroAtScale_re_lt :
    ∀ D : ℝ, 0 < D →
      ∃ c : ℝ, 0 < c ∧
        ∀ (M q : ℕ) [NeZero q]
          (chi : DirichletCharacter ℂ q) (rho : ℂ),
            IsDirichletExceptionalLFunctionZeroAtScale M chi rho →
              rho.re < 1 - c * (q : ℝ) ^ (-(2 * D)⁻¹) := by
  intro D hD
  let epsilon : ℝ := (2 * D)⁻¹
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨c0, hc0, hzeroFree⟩ :=
    exists_siegelRealCharacterZeroFree epsilon hepsilon
  let c : ℝ := c0 / 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  intro M q _ chi rho hexceptional
  obtain ⟨_, _, _, _, psi, hpsi, hchi, hsquare, him, _, _⟩ :=
    hexceptional
  subst psi
  have hzeroData :=
    (isNonprincipalNontrivialLFunctionZero_iff chi rho).mp hpsi
  have hrho : rho = (rho.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hzero :
      DirichletCharacter.LFunction chi (rho.re : ℂ) = 0 := by
    rw [← hrho]
    exact hzeroData.2.1
  let weight : ℝ := (q : ℝ) ^ (-epsilon)
  have hqPos : (0 : ℝ) < q := by
    exact_mod_cast NeZero.pos q
  have hweightPos : 0 < weight := by
    dsimp [weight]
    exact Real.rpow_pos_of_pos hqPos _
  have hcLt : c < c0 := by
    dsimp [c]
    linarith
  change rho.re < 1 - c * weight
  by_contra hgap
  have hthreshold : 1 - c0 * weight < 1 - c * weight := by
    nlinarith
  have hinput : 1 - c0 * weight < rho.re :=
    hthreshold.trans_le (le_of_not_gt hgap)
  exact (hzeroFree q chi hzeroData.1 hsquare rho.re
    (by simpa [weight] using hinput)) hzero

/-- The complete exceptional kernel contribution satisfies the exponential
Siegel--Walfisz error bound with one constant uniform in all later data. -/
theorem exists_norm_dirichletExceptionalZeroKernelSum_lt :
    ∀ D : ℝ, 0 < D →
      ∃ c : ℝ, 0 < c ∧
        ∀ M : ℕ, 2 ≤ M →
          ∀ (q : ℕ) [NeZero q]
            (chi : DirichletCharacter ℂ q) (x T : ℝ),
              0 < x → 1 ≤ Real.log x →
                (q : ℝ) ≤ Real.log x ^ D →
                  ‖dirichletExceptionalZeroKernelSum M chi x T‖ <
                    2 * (x * Real.exp
                      (-c * Real.sqrt (Real.log x))) := by
  intro D hD
  obtain ⟨c, hc, hgap⟩ :=
    exists_dirichletExceptionalLFunctionZeroAtScale_re_lt D hD
  refine ⟨c, hc, ?_⟩
  intro M hM
  exact norm_dirichletExceptionalZeroKernelSum_lt_of_uniform_gap hD hc hM
    (fun q _ chi rho hrho ↦ hgap M q chi rho hrho)

end BoundedGaps.Maynard
