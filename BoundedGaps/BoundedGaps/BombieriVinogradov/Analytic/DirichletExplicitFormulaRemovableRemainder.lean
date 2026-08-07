import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaPerforatedRegularity

/-!
# Dirichlet explicit-formula removable remainder

`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 98, equation (9.6),
and printed pp. 112--115, Theorem 11.3 / equations (11.5)--(11.7), move the
modified logarithmic-derivative contour across multiplicity-counted ordinary
zeros and the separate principal pole.
After subtracting their exact finite principal parts, this file fills the
resulting removable singularities and proves differentiability on the whole
rectangle.

The extension is existential because totalized division gives the raw
remainder the wrong values at its centers. No contour identity or estimate is
asserted here. Semantic review: `SEM-522`.
-/

namespace BoundedGaps.Maynard

open Asymptotics Complex Filter Function Set
open scoped BigOperators Topology

noncomputable section

private noncomputable def principalPartSum
    (P : Finset ℂ) (c : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ rho ∈ P, c rho / (s - rho)

private noncomputable def fillFiniteRemovable
    (P : Finset ℂ) (g : ℂ → ℂ) (s : ℂ) : ℂ :=
  if s ∈ P then limUnder (𝓝[≠] s) g else g s

private lemma isLittleO_sub_self_inv_of_tendsto_mul
    {g : ℂ → ℂ} {rho : ℂ}
    (h : Tendsto (fun s => (s - rho) * g s) (𝓝[≠] rho) (𝓝 0)) :
    (fun s => g s - g rho) =o[𝓝[≠] rho] fun s => (s - rho)⁻¹ := by
  have hsub : Tendsto (fun s => (s - rho) * (g s - g rho))
      (𝓝[≠] rho) (𝓝 0) := by
    have hzero : Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho) (𝓝 0) := by
      have hfull : Tendsto (fun s : ℂ => s - rho) (𝓝 rho) (𝓝 (rho - rho)) :=
        (continuousAt_id.sub
          (continuousAt_const : ContinuousAt (fun _ : ℂ => rho) rho)).tendsto
      simpa using hfull.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun s : ℂ => (s - rho) * g rho)
        (𝓝[≠] rho) (𝓝 0) := by
      simpa using hzero.mul tendsto_const_nhds
    simpa only [mul_sub, sub_zero] using h.sub hconst
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with s hs
    intro hinv
    have hsrho : s - rho ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    exact (inv_ne_zero hsrho hinv).elim
  · simpa only [div_eq_mul_inv, inv_inv, mul_comm] using hsub

private theorem differentiableOn_update_limUnder_of_tendsto_mul
    {g : ℂ → ℂ} {U : Set ℂ} {rho : ℂ} (hrho : U ∈ 𝓝 rho)
    (hd : DifferentiableOn ℂ g (U \ {rho}))
    (h : Tendsto (fun s => (s - rho) * g s) (𝓝[≠] rho) (𝓝 0)) :
    DifferentiableOn ℂ
      (update g rho (limUnder (𝓝[≠] rho) g)) U :=
  Complex.differentiableOn_update_limUnder_of_isLittleO hrho hd
    (isLittleO_sub_self_inv_of_tendsto_mul h)

private theorem differentiableOn_fillFiniteRemovable_of_tendsto_mul
    (P : Finset ℂ) (g : ℂ → ℂ) (U : Set ℂ)
    (hP : ∀ rho ∈ P, rho ∈ interior U)
    (hd : ∀ s ∈ U, s ∉ P → DifferentiableAt ℂ g s)
    (hrem : ∀ rho ∈ P,
      Tendsto (fun s => (s - rho) * g s) (𝓝[≠] rho) (𝓝 0)) :
    DifferentiableOn ℂ (fillFiniteRemovable P g) U := by
  classical
  intro rho hrhoU
  by_cases hrhoP : rho ∈ P
  · let V : Set ℂ :=
      interior U ∩ ((P.erase rho : Finset ℂ) : Set ℂ)ᶜ
    have hEraseNhd : ((P.erase rho : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 rho :=
      (P.erase rho).finite_toSet.isClosed.compl_mem_nhds (by simp)
    have hV : V ∈ 𝓝 rho :=
      inter_mem (isOpen_interior.mem_nhds (hP rho hrhoP)) hEraseNhd
    have hdV : DifferentiableOn ℂ g (V \ {rho}) := by
      intro s hs
      apply (hd s (interior_subset hs.1.1) ?_).differentiableWithinAt
      intro hsP
      have hsrho : s ≠ rho := by simpa using hs.2
      exact hs.1.2 (by simpa [Finset.mem_erase, hsrho] using hsP)
    have hUpdate : DifferentiableAt ℂ
        (update g rho (limUnder (𝓝[≠] rho) g)) rho :=
      (differentiableOn_update_limUnder_of_tendsto_mul
        hV hdV (hrem rho hrhoP)).differentiableAt hV
    have heq : fillFiniteRemovable P g =ᶠ[𝓝 rho]
        update g rho (limUnder (𝓝[≠] rho) g) := by
      filter_upwards [hEraseNhd] with s hs
      by_cases hsrho : s = rho
      · subst s
        simp [fillFiniteRemovable, hrhoP]
      · have hsNotP : s ∉ P := by
          intro hsP
          exact hs (by simpa [Finset.mem_erase, hsrho] using hsP)
        simp [fillFiniteRemovable, hsNotP, Function.update_of_ne hsrho]
    exact (hUpdate.congr_of_eventuallyEq heq).differentiableWithinAt
  · have hPcompl : ((P : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 rho :=
      P.finite_toSet.isClosed.compl_mem_nhds (by simpa)
    have heq : fillFiniteRemovable P g =ᶠ[𝓝 rho] g := by
      filter_upwards [hPcompl] with s hs
      simp [fillFiniteRemovable, show s ∉ P by simpa using hs]
    exact ((hd rho hrhoU hrhoP).congr_of_eventuallyEq heq).differentiableWithinAt

private lemma tendsto_mul_principalPartSum
    (P : Finset ℂ) (c : ℂ → ℂ) {rho : ℂ} (hrho : rho ∈ P) :
    Tendsto (fun s => (s - rho) * principalPartSum P c s)
      (𝓝[≠] rho) (𝓝 (c rho)) := by
  classical
  have hzero : Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho) (𝓝 0) := by
    have hfull : Tendsto (fun s : ℂ => s - rho) (𝓝 rho) (𝓝 (rho - rho)) :=
      (continuousAt_id.sub
        (continuousAt_const : ContinuousAt (fun _ : ℂ => rho) rho)).tendsto
    simpa using hfull.mono_left nhdsWithin_le_nhds
  have hother : Tendsto
      (fun s => ∑ q ∈ P.erase rho, c q / (s - q)) (𝓝[≠] rho)
      (𝓝 (∑ q ∈ P.erase rho, c q / (rho - q))) := by
    apply tendsto_finsetSum
    intro q hq
    have hrhoq : rho - q ≠ 0 :=
      sub_ne_zero.mpr (Finset.mem_erase.mp hq).1.symm
    exact ((continuousAt_const.div
      (continuousAt_id.sub continuousAt_const) hrhoq).tendsto).mono_left
        nhdsWithin_le_nhds
  have hrhoTerm : Tendsto
      (fun s : ℂ => (s - rho) * (c rho / (s - rho)))
      (𝓝[≠] rho) (𝓝 (c rho)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsrho : s - rho ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hsrho]
  have htotal : Tendsto
      (fun s => (s - rho) * (c rho / (s - rho)) +
        (s - rho) * ∑ q ∈ P.erase rho, c q / (s - q))
      (𝓝[≠] rho) (𝓝 (c rho)) := by
    simpa only [add_zero, zero_mul] using hrhoTerm.add (hzero.mul hother)
  apply htotal.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [principalPartSum,
    ← Finset.add_sum_erase P (fun q => c q / (s - q)) hrho, mul_add]

private theorem differentiableOn_filledRemainder
    (P : Finset ℂ) (c : ℂ → ℂ) (f : ℂ → ℂ) (U : Set ℂ)
    (hP : ∀ rho ∈ P, rho ∈ interior U)
    (hd : ∀ s ∈ U, s ∉ P → DifferentiableAt ℂ f s)
    (hres : ∀ rho ∈ P,
      Tendsto (fun s => (s - rho) * f s) (𝓝[≠] rho) (𝓝 (c rho))) :
    DifferentiableOn ℂ
      (fillFiniteRemovable P
        (fun s => f s - principalPartSum P c s)) U := by
  classical
  apply differentiableOn_fillFiniteRemovable_of_tendsto_mul P
      (fun s => f s - principalPartSum P c s) U hP
  · intro s hsU hsP
    apply (hd s hsU hsP).sub
    apply DifferentiableAt.fun_sum
    intro rho hrho
    exact (differentiableAt_const (c rho)).div
      (differentiableAt_id.sub_const rho)
      (sub_ne_zero.mpr fun h => hsP (h ▸ hrho))
  · intro rho hrho
    have hf := hres rho hrho
    have hs := tendsto_mul_principalPartSum P c hrho
    simpa only [mul_sub, sub_self] using hf.sub hs

private theorem
    tendsto_sub_mul_dirichletExplicitFormulaIntegrand_eq_candidateContribution
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (rho : ℂ) :
    Tendsto
      (fun s => (s - rho) * dirichletExplicitFormulaIntegrand chi x s)
      (𝓝[≠] rho)
      (𝓝 (dirichletExplicitFormulaCandidateContribution chi x rho)) := by
  by_cases hchi : chi = 1
  · subst chi
    by_cases hrho : rho = 1
    · subst rho
      simpa [dirichletExplicitFormulaCandidateContribution] using
        (tendsto_sub_one_mul_dirichletExplicitFormulaIntegrand_one
          (N := N) x)
    · simpa [dirichletExplicitFormulaCandidateContribution, hrho] using
        (tendsto_sub_mul_dirichletExplicitFormulaIntegrand_one_of_ne_one
          (N := N) x rho hrho)
  · simpa [dirichletExplicitFormulaCandidateContribution, hchi] using
      (tendsto_sub_mul_dirichletExplicitFormulaIntegrand hchi x rho)

/-- Subtracting every exact candidate principal part leaves a function with a
complex-differentiable extension across the whole closed rectangle. -/
theorem
    exists_differentiableOn_dirichletExplicitFormulaIntegrand_sub_candidatePrincipalParts
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (z w : ℂ)
    (hinside :
      dirichletExplicitFormulaCandidateSingularities chi z w ⊆
        interior (Complex.Rectangle z w)) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (Complex.Rectangle z w) ∧
      Set.EqOn F
        (fun s =>
          dirichletExplicitFormulaIntegrand chi x s -
            ∑ rho ∈
              dirichletExplicitFormulaCandidateSingularitiesFinset chi z w,
              dirichletExplicitFormulaCandidateContribution chi x rho /
                (s - rho))
        ((dirichletExplicitFormulaCandidateSingularitiesFinset chi z w :
          Set ℂ)ᶜ) := by
  classical
  let P := dirichletExplicitFormulaCandidateSingularitiesFinset chi z w
  let g : ℂ → ℂ := fun s =>
    dirichletExplicitFormulaIntegrand chi x s -
      principalPartSum P
        (dirichletExplicitFormulaCandidateContribution chi x) s
  refine ⟨fillFiniteRemovable P g, ?_, ?_⟩
  · change DifferentiableOn ℂ
      (fillFiniteRemovable P (fun s =>
        dirichletExplicitFormulaIntegrand chi x s -
          principalPartSum P
            (dirichletExplicitFormulaCandidateContribution chi x) s))
      (Complex.Rectangle z w)
    apply differentiableOn_filledRemainder
    · intro rho hrho
      apply hinside
      exact
        mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff.mp hrho
    · intro s hsRect hsP
      apply
        differentiableAt_dirichletExplicitFormulaIntegrand_of_mem_rectangle_of_not_candidate
          chi x hsRect
      intro hsCandidate
      exact hsP
        (mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff.mpr
          hsCandidate)
    · intro rho _hrho
      exact
        tendsto_sub_mul_dirichletExplicitFormulaIntegrand_eq_candidateContribution
          chi x rho
  · intro s hs
    have hsP : s ∉ P := by
      change s ∉
        dirichletExplicitFormulaCandidateSingularitiesFinset chi z w
      exact hs
    simp [fillFiniteRemovable, g, principalPartSum, P, hsP]

end

end BoundedGaps.Maynard
