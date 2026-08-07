import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateCircleSum
import BoundedGaps.BombieriVinogradov.Analytic.ImprimitiveLFunctionTransport

/-!
# Transport of Dirichlet nontrivial zeros

Before moving the explicit-formula contour,
`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 115, equation
(11.7), replaces an arbitrary character by its primitive inducer. The finite
inducing Euler product has no zeros in the open right half-plane, so this
replacement preserves every nontrivial-zero location and its analytic
multiplicity.

Zeros on `Re(s)=0`, including zeros introduced by imprimitive Euler factors,
are trivial in the source and are intentionally absent here. Semantic review:
`SEM-524`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Filter Set
open scoped BigOperators Topology

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

private lemma primitiveCharacter_ne_one_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hpsi
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter]
  exact (DirichletCharacter.changeLevel_eq_one_iff
    chi.conductor_dvd_level).2 hpsi

/-- An ordinary Dirichlet-L zero in the strict open critical strip. -/
def IsDirichletNontrivialLFunctionZero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (rho : ℂ) : Prop :=
  DirichletCharacter.LFunction chi rho = 0 ∧
    0 < rho.re ∧ rho.re < 1

/-- An arbitrary character and its primitive inducer have exactly the same
nontrivial-zero locations. -/
theorem isDirichletNontrivialLFunctionZero_iff_inducingPrimitive
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (rho : ℂ) :
    IsDirichletNontrivialLFunctionZero chi rho ↔
      IsDirichletNontrivialLFunctionZero chi.primitiveCharacter rho := by
  by_cases hrhoOne : rho = 1
  · subst rho
    simp [IsDirichletNontrivialLFunctionZero]
  · constructor
    · rintro ⟨hzero, hre0, hre1⟩
      have hfactor :=
        LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
          (.inr hrhoOne)
      rw [hfactor] at hzero
      exact ⟨(mul_eq_zero.mp hzero).resolve_right
        (inducingEulerProduct_ne_zero_of_re_pos chi hre0), hre0, hre1⟩
    · rintro ⟨hzero, hre0, hre1⟩
      refine ⟨?_, hre0, hre1⟩
      rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
        (.inr hrhoOne), hzero, zero_mul]

/-- In the open right half-plane and away from the principal pole, inducing
Euler factors add no analytic multiplicity. -/
theorem
    analyticOrderNatAt_LFunction_eq_inducingPrimitive_of_re_pos_of_guard
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hguard : chi ≠ 1 ∨ rho ≠ 1) (hrho : 0 < rho.re) :
    analyticOrderNatAt (DirichletCharacter.LFunction chi) rho =
      analyticOrderNatAt
        (DirichletCharacter.LFunction chi.primitiveCharacter) rho := by
  let P : ℂ → ℂ := inducingEulerProduct chi
  have heq : DirichletCharacter.LFunction chi =ᶠ[𝓝 rho]
      fun z => DirichletCharacter.LFunction chi.primitiveCharacter z * P z := by
    rcases hguard with hchi | hrhoOne
    · exact Eventually.of_forall fun z => by
        simpa [P] using
          LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
            (.inl hchi)
    · filter_upwards [eventually_ne_nhds hrhoOne] with z hz
      simpa [P] using
        LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
          (.inr hz)
  have hprimitiveGuard : rho ≠ 1 ∨ chi.primitiveCharacter ≠ 1 := by
    rcases hguard with hchi | hrhoOne
    · exact .inr (primitiveCharacter_ne_one_of_ne_one chi hchi)
    · exact .inl hrhoOne
  have hprimitive : AnalyticAt ℂ
      (DirichletCharacter.LFunction chi.primitiveCharacter) rho := by
    rcases hprimitiveGuard with hrhoOne | hpsi
    · have hdiff : DifferentiableOn ℂ
          (DirichletCharacter.LFunction chi.primitiveCharacter) ({1}ᶜ : Set ℂ) := by
        intro z hz
        exact (DirichletCharacter.differentiableAt_LFunction
          chi.primitiveCharacter z (.inl (by simpa using hz))).differentiableWithinAt
      exact hdiff.analyticAt
        (isOpen_compl_singleton.mem_nhds (by simpa using hrhoOne))
    · exact (DirichletCharacter.differentiable_LFunction hpsi).analyticAt rho
  have hP : AnalyticAt ℂ P rho := by
    simpa [P] using (differentiable_inducingEulerProduct chi).analyticAt rho
  have hPne : P rho ≠ 0 := by
    simpa [P] using inducingEulerProduct_ne_zero_of_re_pos chi hrho
  have horder :
      analyticOrderAt (DirichletCharacter.LFunction chi) rho =
        analyticOrderAt
          (DirichletCharacter.LFunction chi.primitiveCharacter) rho := by
    calc
      analyticOrderAt (DirichletCharacter.LFunction chi) rho =
          analyticOrderAt
            (fun z =>
              DirichletCharacter.LFunction chi.primitiveCharacter z * P z)
              rho :=
        analyticOrderAt_congr heq
      _ = analyticOrderAt
            (DirichletCharacter.LFunction chi.primitiveCharacter) rho +
          analyticOrderAt P rho :=
        analyticOrderAt_mul hprimitive hP
      _ = analyticOrderAt
            (DirichletCharacter.LFunction chi.primitiveCharacter) rho := by
        rw [hP.analyticOrderAt_eq_zero.mpr hPne, add_zero]
  exact congrArg ENat.toNat horder

/-- The distinct nontrivial zeros up to an absolute height. -/
noncomputable def dirichletNontrivialLFunctionZerosFinset
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T : ℝ) : Finset ℂ := by
  classical
  exact (dirichletExplicitFormulaCandidateSingularitiesFinset chi
    ((0 : ℂ) - |T| * I) ((1 : ℂ) + |T| * I)).filter
      (IsDirichletNontrivialLFunctionZero chi)

@[simp]
theorem mem_dirichletNontrivialLFunctionZerosFinset_iff
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {T : ℝ} {rho : ℂ} :
    rho ∈ dirichletNontrivialLFunctionZerosFinset chi T ↔
      IsDirichletNontrivialLFunctionZero chi rho ∧
        |rho.im| ≤ |T| := by
  classical
  rw [dirichletNontrivialLFunctionZerosFinset, Finset.mem_filter,
    mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff,
    mem_dirichletExplicitFormulaCandidateSingularities_iff]
  constructor
  · rintro ⟨⟨hrect, _⟩, hzero⟩
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hrect
    norm_num at hrect
    exact ⟨hzero, (abs_le.mpr hrect.2)⟩
  · rintro ⟨hzero, hheight⟩
    have hrhoOne : rho ≠ 1 := by
      intro hrho
      have hre := congrArg Complex.re hrho
      simp only [one_re] at hre
      exact (lt_irrefl 1) (hre ▸ hzero.2.2)
    refine ⟨⟨?_, Or.inr ⟨Or.inl hrhoOne, hzero.1⟩⟩, hzero⟩
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    norm_num
    exact ⟨⟨hzero.2.1.le, hzero.2.2.le⟩, abs_le.mp hheight⟩

/-- The finite distinct-location index is unchanged by passage to the
primitive inducer. -/
theorem dirichletNontrivialLFunctionZerosFinset_eq_inducingPrimitive
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T : ℝ) :
    dirichletNontrivialLFunctionZerosFinset chi T =
      dirichletNontrivialLFunctionZerosFinset chi.primitiveCharacter T := by
  classical
  ext rho
  rw [mem_dirichletNontrivialLFunctionZerosFinset_iff,
    mem_dirichletNontrivialLFunctionZerosFinset_iff,
    isDirichletNontrivialLFunctionZero_iff_inducingPrimitive]

/-- The grouped modified-kernel sum over nontrivial zeros. Analytic order is
the source's repetition count. -/
noncomputable def dirichletNontrivialZeroKernelSum
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x T : ℝ) : ℂ :=
  ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T,
    (analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho : ℂ) *
        dirichletExplicitFormulaKernel x rho

/-- The exact grouped consequence of the sentence following equation (11.7):
the arbitrary character and its primitive inducer have the same truncated
nontrivial-zero kernel sum. -/
theorem dirichletNontrivialZeroKernelSum_eq_inducingPrimitive
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x T : ℝ) :
    dirichletNontrivialZeroKernelSum chi x T =
      dirichletNontrivialZeroKernelSum chi.primitiveCharacter x T := by
  classical
  rw [dirichletNontrivialZeroKernelSum,
    dirichletNontrivialZeroKernelSum,
    dirichletNontrivialLFunctionZerosFinset_eq_inducingPrimitive chi T]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hzero :=
    (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho).1
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    simp only [one_re] at hre
    exact (lt_irrefl 1) (hre ▸ hzero.2.2)
  rw [analyticOrderNatAt_LFunction_eq_inducingPrimitive_of_re_pos_of_guard
    chi (.inr hrhoOne) hzero.2.1]

end BoundedGaps.Maynard
