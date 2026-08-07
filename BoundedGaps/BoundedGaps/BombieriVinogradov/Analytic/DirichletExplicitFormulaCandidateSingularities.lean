import BoundedGaps.BombieriVinogradov.Analytic.DirichletLZeroDivisor

/-!
# Dirichlet explicit-formula candidate singularities

`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 115, moves the
modified explicit-formula contour across the ordinary zeros of `L(s, chi)` and
the pole at one when `chi` is principal. This file collects the distinct
candidate locations in a closed rectangle and proves that the set is finite.

The ordinary-zero branch retains Mathlib's exact analyticity guard at the
principal pole. Multiplicity, boundary avoidance, disk selection, and contour
composition remain separate. Semantic review: `SEM-502`.
-/

noncomputable section

open Complex Set

namespace BoundedGaps.Maynard

/-- The distinct ordinary-L zero and principal-pole candidates in a closed
axis-parallel rectangle. -/
noncomputable def dirichletExplicitFormulaCandidateSingularities
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (z w : ℂ) : Set ℂ :=
  {rho | rho ∈ Complex.Rectangle z w ∧
    ((chi = 1 ∧ rho = 1) ∨
      ((rho ≠ 1 ∨ chi ≠ 1) ∧
        DirichletCharacter.LFunction chi rho = 0))}

@[simp]
theorem mem_dirichletExplicitFormulaCandidateSingularities_iff
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    {z w rho : ℂ} :
    rho ∈ dirichletExplicitFormulaCandidateSingularities chi z w ↔
      rho ∈ Complex.Rectangle z w ∧
        ((chi = 1 ∧ rho = 1) ∨
          ((rho ≠ 1 ∨ chi ≠ 1) ∧
            DirichletCharacter.LFunction chi rho = 0)) :=
  Iff.rfl

/-- Only finitely many ordinary-L zero and principal-pole candidates lie in a
closed rectangle. -/
theorem dirichletExplicitFormulaCandidateSingularities_finite
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (z w : ℂ) :
    (dirichletExplicitFormulaCandidateSingularities chi z w).Finite := by
  have finiteZeros : ∀ (f : ℂ → ℂ),
      Differentiable ℂ f → f ≠ 0 →
      {s | s ∈ Complex.Rectangle z w ∧ f s = 0}.Finite := by
    intro f hf hne
    let U := Complex.Rectangle z w
    have hA : AnalyticOnNhd ℂ f U := fun s _ => hf.analyticAt s
    have hfiniteSupport :
        (MeromorphicOn.divisor f U).support.Finite :=
      hA.meromorphicOn.divisor_support_finite_of_subset
        (isCompact_uIcc.reProdIm isCompact_uIcc) Set.Subset.rfl
    apply hfiniteSupport.subset
    rintro s ⟨hsU, hfs⟩
    have htop : analyticOrderAt f s ≠ ⊤ := by
      rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
        (fun u => hf.analyticAt u)]
      exact hne
    have horder : analyticOrderAt f s ≠ 0 :=
      (hf.analyticAt s).analyticOrderAt_ne_zero.mpr hfs
    rw [Function.mem_support,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hA hsU]
    lift analyticOrderAt f s to ℕ using htop with n hn
    simp only [ENat.map_coe, WithTop.untop₀_coe]
    exact_mod_cast horder
  rw [dirichletExplicitFormulaCandidateSingularities]
  by_cases hchi : chi = 1
  · subst chi
    let G : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ N
    have hGne : G ≠ 0 := by
      intro hzero
      have hGone : G 1 = 0 := by rw [hzero]; rfl
      exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N hGone
    have hGfinite := finiteZeros G
      (by simpa [G] using
        DirichletCharacter.differentiable_LFunctionTrivChar₁ N)
      hGne
    apply (hGfinite.union (Set.finite_singleton (1 : ℂ))).subset
    rintro rho ⟨hrhoRect, hpole | hzero⟩
    · exact Set.mem_union_right _ hpole.2
    · have hrhoOne : rho ≠ 1 := hzero.1.resolve_right (by simp)
      have htrivZero :
          DirichletCharacter.LFunctionTrivChar N rho = 0 :=
        hzero.2
      apply Set.mem_union_left
      refine ⟨hrhoRect, ?_⟩
      dsimp only [G]
      rw [DirichletCharacter.LFunctionTrivChar₁,
        Function.update_of_ne hrhoOne, htrivZero, mul_zero]
  · have hLne : DirichletCharacter.LFunction chi ≠ 0 := by
      intro hzero
      have htwo : DirichletCharacter.LFunction chi (2 : ℂ) = 0 := by
        rw [hzero]
        rfl
      exact (chi.LFunction_ne_zero_of_one_le_re
        (.inl hchi) (by norm_num)) htwo
    apply (finiteZeros (DirichletCharacter.LFunction chi)
      (DirichletCharacter.differentiable_LFunction hchi) hLne).subset
    rintro rho ⟨hrhoRect, hpole | hzero⟩
    · exact (hchi hpole.1).elim
    · exact ⟨hrhoRect, hzero.2⟩

end BoundedGaps.Maynard
