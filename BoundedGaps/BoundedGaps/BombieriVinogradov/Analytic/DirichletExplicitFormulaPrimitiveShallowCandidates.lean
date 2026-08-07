import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaVerticalEdges
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNontrivialZeroTransport
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPrimitiveShallowZeros

/-!
# Primitive shallow explicit-formula candidates

After the primitive reduction in equation (11.7),
`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115, moves the
modified-kernel contour across the principal pole, nontrivial zeros, and
parity-dependent trivial zeros. This file makes the project-selected
`Re(s) = -1/2` candidate inventory exact.

The only exceptional zero inside this shallow rectangle is the simple origin
zero of an even nonprincipal primitive character. Edge estimates and the
contour shift remain separate. Semantic review: `SEM-525`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Set
open scoped BigOperators

noncomputable local instance primitiveShallowCandidateDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The distinct candidates in the project-selected shallow rectangle. This
definition is total in `x` and `T`; its classification requires `1 < x`. -/
noncomputable def dirichletExplicitFormulaShallowCandidateSingularitiesFinset
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x T : ℝ) : Finset ℂ :=
  dirichletExplicitFormulaCandidateSingularitiesFinset chi
    ((-(1 / 2 : ℝ) : ℂ) - |T| * Complex.I)
    (((1 + 1 / Real.log x : ℝ) : ℂ) + |T| * Complex.I)

/-- A primitive shallow candidate is exactly the optional pole, a strict-strip
zero at the requested absolute height, or the optional even origin zero. -/
theorem
    mem_dirichletExplicitFormulaShallowCandidateSingularitiesFinset_iff_of_isPrimitive
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : chi.IsPrimitive) {x T : ℝ} (hx : 1 < x) {rho : ℂ} :
    rho ∈ dirichletExplicitFormulaShallowCandidateSingularitiesFinset
        chi x T ↔
      (chi = 1 ∧ rho = 1) ∨
        (IsDirichletNontrivialLFunctionZero chi rho ∧
          |rho.im| ≤ |T|) ∨
        (rho = 0 ∧ chi ≠ 1 ∧ chi.Even) := by
  classical
  rw [dirichletExplicitFormulaShallowCandidateSingularitiesFinset,
    mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff,
    mem_dirichletExplicitFormulaCandidateSingularities_iff]
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hright : 1 < 1 + 1 / Real.log x := by
    linarith [one_div_pos.mpr hlog]
  have hright' : 1 < 1 + (Real.log x)⁻¹ := by
    simpa [one_div] using hright
  have hedges : -(1 / 2 : ℝ) < 1 + 1 / Real.log x := by
    linarith
  have hedges' : -(1 / 2 : ℝ) ≤ 1 + (Real.log x)⁻¹ := by
    simpa [one_div] using hedges.le
  constructor
  · rintro ⟨hrect, hpole | hzero⟩
    · exact .inl hpole
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hrect
    norm_num at hrect
    rw [uIcc_of_le hedges'] at hrect
    have hheight : |rho.im| ≤ |T| := abs_le.mpr hrect.2
    by_cases hre : 0 < rho.re
    · have hreOne : rho.re < 1 := by
        by_contra hnot
        have hone : 1 ≤ rho.re := le_of_not_gt hnot
        have hguard : chi ≠ 1 ∨ rho ≠ 1 := hzero.1.symm
        exact (chi.LFunction_ne_zero_of_one_le_re hguard hone) hzero.2
      exact .inr (.inl ⟨⟨hzero.2, hre, hreOne⟩, hheight⟩)
    · have hreNonpos : rho.re ≤ 0 := le_of_not_gt hre
      have hleft : -(1 / 2 : ℝ) < rho.re := by
        rcases hrect.1.1.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso
          have hboundary :=
            (LFunction_ne_zero_on_dirichletExplicitFormulaVerticalEdges
              chi x hx 0 rho.im).1
          apply hboundary
          have hrhoEq :
              (((-((0 : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) +
                rho.im * I) = rho := by
            apply Complex.ext
            · simpa using heq
            · simp
          rw [hrhoEq]
          exact hzero.2
      exact .inr (.inr
        ((primitive_LFunction_eq_zero_iff_origin_of_neg_half_lt_re_of_re_nonpos
          chi hchi hleft hreNonpos).mp hzero.2))
  · intro hrhs
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    norm_num
    rw [uIcc_of_le hedges']
    rcases hrhs with hpole | hnontriv | horigin
    · rcases hpole with ⟨rfl, rfl⟩
      exact ⟨⟨⟨by norm_num, hright'.le⟩, by simp⟩, .inl ⟨rfl, rfl⟩⟩
    · rcases hnontriv with ⟨⟨hzero, hre0, hre1⟩, hheight⟩
      have hrhoOne : rho ≠ 1 := by
        intro hrho
        have hre := congrArg Complex.re hrho
        norm_num at hre
        linarith
      exact ⟨⟨⟨by linarith, by linarith⟩, abs_le.mp hheight⟩,
        .inr ⟨.inl hrhoOne, hzero⟩⟩
    · rcases horigin with ⟨rfl, hchiNe, heven⟩
      have hzero :=
        (primitive_LFunction_eq_zero_iff_origin_of_neg_half_lt_re_of_re_nonpos
          chi hchi (by norm_num) (by norm_num)).mpr
            ⟨rfl, hchiNe, heven⟩
      exact ⟨⟨⟨by norm_num, by
        simpa using (show (0 : ℝ) ≤ 1 by norm_num).trans hright'.le⟩, by simp⟩,
        .inr ⟨.inr hchiNe, hzero⟩⟩

/-- The shallow inventory is the disjoint-location union of its three
mathematical branches. -/
theorem
    dirichletExplicitFormulaShallowCandidateSingularitiesFinset_eq_of_isPrimitive
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (x T : ℝ) (hx : 1 < x) :
    dirichletExplicitFormulaShallowCandidateSingularitiesFinset chi x T =
      ((if chi = 1 then {1} else ∅) ∪
        dirichletNontrivialLFunctionZerosFinset chi T) ∪
      (if chi ≠ 1 ∧ chi.Even then {0} else ∅) := by
  classical
  ext rho
  rw [mem_dirichletExplicitFormulaShallowCandidateSingularitiesFinset_iff_of_isPrimitive
    hchi hx]
  simp only [Finset.mem_union,
    mem_dirichletNontrivialLFunctionZerosFinset_iff]
  by_cases hchiOne : chi = 1
  · subst chi
    simp
  · by_cases heven : chi.Even
    · simp [hchiOne, heven, and_comm]
    · simp [hchiOne, heven]

private theorem sum_nontrivial_candidateContribution_eq_neg_kernelSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (x T : ℝ) :
    (∑ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T,
      dirichletExplicitFormulaCandidateContribution chi x rho) =
        -dirichletNontrivialZeroKernelSum chi x T := by
  classical
  rw [dirichletNontrivialZeroKernelSum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hzero :=
    (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho).1
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    norm_num at hre
    linarith [hzero.2.2]
  simp [dirichletExplicitFormulaCandidateContribution, hrhoOne,
    dirichletExplicitFormulaZeroResidue]

/-- The exact shallow candidate sum: principal pole minus multiplicity-weighted
nontrivial kernels, with the even nonprincipal origin term retained. -/
theorem
    sum_dirichletExplicitFormulaShallowCandidateContribution_eq_of_isPrimitive
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (x T : ℝ) (hx : 1 < x) :
    (∑ rho ∈
        dirichletExplicitFormulaShallowCandidateSingularitiesFinset chi x T,
      dirichletExplicitFormulaCandidateContribution chi x rho) =
      (if chi = 1 then (x : ℂ) - 1 else 0) -
        dirichletNontrivialZeroKernelSum chi x T -
          (if chi ≠ 1 ∧ chi.Even then (Real.log x : ℂ) else 0) := by
  classical
  rw [dirichletExplicitFormulaShallowCandidateSingularitiesFinset_eq_of_isPrimitive
    chi hchi x T hx]
  by_cases hchiOne : chi = 1
  · subst chi
    have horigin : ¬((1 : DirichletCharacter ℂ q) ≠ 1 ∧
        (1 : DirichletCharacter ℂ q).Even) := fun h => h.1 rfl
    have hdisjoint : Disjoint ({1} : Finset ℂ)
        (dirichletNontrivialLFunctionZerosFinset
          (1 : DirichletCharacter ℂ q) T) := by
      rw [Finset.disjoint_left]
      intro rho hrhoOne hrho
      simp only [Finset.mem_singleton] at hrhoOne
      subst rho
      have hzero :=
        (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho).1
      norm_num [IsDirichletNontrivialLFunctionZero] at hzero
    simp only [if_true, if_neg horigin, Finset.union_empty]
    rw [Finset.sum_union hdisjoint,
      sum_nontrivial_candidateContribution_eq_neg_kernelSum]
    rw [Finset.sum_singleton,
      dirichletExplicitFormulaCandidateContribution,
      if_pos ⟨rfl, rfl⟩,
      dirichletExplicitFormulaPrincipalPoleResidue_eq_sub_one
        (x := x) (zero_lt_one.trans hx)]
    ring
  · by_cases heven : chi.Even
    · have hq : 1 < q := by
        have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
        have hqne : q ≠ 1 := fun hq => hchiOne (chi.level_one' hq)
        omega
      have hdisjoint : Disjoint
          (dirichletNontrivialLFunctionZerosFinset chi T)
          ({0} : Finset ℂ) := by
        rw [Finset.disjoint_left]
        intro rho hrho hrhoZero
        simp only [Finset.mem_singleton] at hrhoZero
        subst rho
        have hzero :=
          (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho).1
        norm_num [IsDirichletNontrivialLFunctionZero] at hzero
      have horigin : chi ≠ 1 ∧ chi.Even := ⟨hchiOne, heven⟩
      simp only [if_neg hchiOne, if_pos horigin, Finset.empty_union]
      rw [Finset.sum_union hdisjoint,
        sum_nontrivial_candidateContribution_eq_neg_kernelSum]
      rw [Finset.sum_singleton,
        dirichletExplicitFormulaCandidateContribution,
        if_neg (by simp [hchiOne]),
        dirichletExplicitFormulaZeroResidue_zero,
        analyticOrderNatAt_LFunction_zero_eq_one_of_isPrimitive_even
          hq chi hchi heven]
      norm_num
      ring
    · have horigin : ¬(chi ≠ 1 ∧ chi.Even) := fun h => heven h.2
      simp only [if_neg hchiOne, if_neg horigin, Finset.empty_union,
        Finset.union_empty]
      simpa using
        (sum_nontrivial_candidateContribution_eq_neg_kernelSum chi x T)

end BoundedGaps.Maynard
