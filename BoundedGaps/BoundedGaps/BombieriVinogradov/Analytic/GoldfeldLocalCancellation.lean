import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldSmoothedSum

/-!
# Goldfeld local cancellation and shifted-zeta residue

This file fills the canceled Mellin pole in Koukoulopoulos Theorem 12.9 with
Mathlib's divided slope. It then isolates the shifted zeta pole at
`s = 1 - beta` and proves its exact source residue. It does not move a contour
or assert that the residue is nonzero.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 55--56,
73--74, and 124--126. Semantic review: `SEM-555`.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace BoundedGaps.Maynard

/-- The shifted location where `zeta(s + beta)` has its source pole. -/
noncomputable def goldfeldShiftedZetaPole (beta : ℝ) : ℂ :=
  ((1 - beta : ℝ) : ℂ)

/-- The derivative-filled quotient of the shifted exceptional L-function by
`s`, centered at the canceled Mellin point. -/
noncomputable def goldfeldShiftedLFunctionDividedSlope
    {q1 : ℕ} [NeZero q1]
    (chi1 : DirichletCharacter ℂ q1) (beta : ℝ) (s : ℂ) : ℂ :=
  dslope
    (fun z : ℂ => DirichletCharacter.LFunction chi1 (z + (beta : ℂ))) 0 s

/-- The numerator left after filling the Mellin point and removing the shifted
zeta denominator. It is entire under the hypotheses proved below. -/
noncomputable def goldfeldContourNumerator
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  riemannZeta₁ (s + (beta : ℂ)) *
    goldfeldShiftedLFunctionDividedSlope chi1 beta s *
    DirichletCharacter.LFunction chi (s + (beta : ℂ)) *
    DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
      (s + (beta : ℂ)) *
    (-goldfeldDerivativeMellin s) * (x : ℂ) ^ s

/-- The contour integrand filled at zero, with the shifted zeta pole retained
as the explicit denominator `s - (1 - beta)`. -/
noncomputable def goldfeldRegularizedContourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  goldfeldContourNumerator chi1 chi beta x s /
    (s - goldfeldShiftedZetaPole beta)

/-- The exact positive-orientation residue coefficient displayed in the proof
of Koukoulopoulos Theorem 12.9. -/
noncomputable def goldfeldContourResidue
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) : ℂ :=
  (x : ℂ) ^ goldfeldShiftedZetaPole beta *
    DirichletCharacter.LFunction chi1 1 *
    DirichletCharacter.LFunction chi 1 *
    DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) 1 *
    goldfeldMellinContinuationData.Phi (goldfeldShiftedZetaPole beta)

private theorem goldfeldShiftedLFunctionDividedSlope_mul
    {q1 : ℕ} [NeZero q1]
    (chi1 : DirichletCharacter ℂ q1) (beta : ℝ)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (s : ℂ) :
    s * goldfeldShiftedLFunctionDividedSlope chi1 beta s =
      DirichletCharacter.LFunction chi1 (s + (beta : ℂ)) := by
  simpa [goldfeldShiftedLFunctionDividedSlope, smul_eq_mul] using
    (sub_smul_dslope_of_zero (f := fun z : ℂ =>
      DirichletCharacter.LFunction chi1 (z + (beta : ℂ)))
      (a := (0 : ℂ)) (by simpa using hzero) s)

/-- A shifted nonprincipal L-function has an entire derivative-filled divided
slope. -/
theorem differentiable_goldfeldShiftedLFunctionDividedSlope
    {q1 : ℕ} [NeZero q1]
    {chi1 : DirichletCharacter ℂ q1} (hchi1 : chi1 ≠ 1)
    (beta : ℝ) :
    Differentiable ℂ (goldfeldShiftedLFunctionDividedSlope chi1 beta) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2
    (((DirichletCharacter.differentiable_LFunction hchi1).comp
      (differentiable_id.add_const (beta : ℂ))).differentiableOn)

/-- Away from zero, the filled divided slope is the source quotient. No
simple-zero hypothesis is needed. -/
theorem goldfeldShiftedLFunctionDividedSlope_eq_div
    {q1 : ℕ} [NeZero q1]
    (chi1 : DirichletCharacter ℂ q1) {beta : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    {s : ℂ} (hs : s ≠ 0) :
    goldfeldShiftedLFunctionDividedSlope chi1 beta s =
      DirichletCharacter.LFunction chi1 (s + (beta : ℂ)) / s := by
  rw [eq_div_iff hs]
  simpa [mul_comm] using
    goldfeldShiftedLFunctionDividedSlope_mul chi1 beta hzero s

/-- Under the three nonprincipal hypotheses, every factor of the regularized
numerator is entire. -/
theorem differentiable_goldfeldContourNumerator
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (goldfeldContourNumerator chi1 chi beta x) := by
  have hshift : Differentiable ℂ (fun s : ℂ => s + (beta : ℂ)) :=
    differentiable_id.add_const _
  have hzeta : Differentiable ℂ (fun s : ℂ =>
      riemannZeta₁ (s + (beta : ℂ))) :=
    differentiable_riemannZeta₁.comp hshift
  have hLchi : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction chi (s + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi).comp hshift
  have hLcross : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hcross).comp hshift
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hxpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_id.const_cpow (.inl hx0)
  unfold goldfeldContourNumerator
  exact (((((hzeta.mul
    (differentiable_goldfeldShiftedLFunctionDividedSlope hchi1 beta)).mul
      hLchi).mul hLcross).mul
        differentiable_goldfeldDerivativeMellin.neg).mul hxpow)

/-- Off the canceled point and shifted zeta point, the regularized function is
exactly the original contour integrand. -/
theorem goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    {s : ℂ} (hs0 : s ≠ 0)
    (hspole : s ≠ goldfeldShiftedZetaPole beta) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x s =
      goldfeldContourIntegrand chi1 chi beta x s := by
  have hL := goldfeldShiftedLFunctionDividedSlope_mul chi1 beta hzero s
  have harg : s + (beta : ℂ) ≠ 1 := by
    intro h
    apply hspole
    rw [goldfeldShiftedZetaPole]
    norm_num at h ⊢
    linear_combination h
  have hshift : s + (beta : ℂ) - 1 =
      s - goldfeldShiftedZetaPole beta := by
    rw [goldfeldShiftedZetaPole]
    norm_num
    ring
  have hzeta := riemannZeta_eq_inv_sub_mul harg
  rw [hshift] at hzeta
  rw [goldfeldRegularizedContourIntegrand, goldfeldContourNumerator,
    goldfeldContourIntegrand, goldfeldFourFactorLFunction,
    hzeta, ← hL, goldfeldMellinContinuationData.equals_candidate,
    goldfeldMellinCandidate]
  field_simp [hs0, sub_ne_zero.mpr hspole]

/-- The filled contour integrand is analytic at the canceled Mellin point. -/
theorem goldfeldRegularizedContourIntegrand_analyticAt_zero
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta : beta < 1) (hx : 0 < x) :
    AnalyticAt ℂ
      (goldfeldRegularizedContourIntegrand chi1 chi beta x) 0 := by
  have hdelta0 : goldfeldShiftedZetaPole beta ≠ 0 := by
    rw [goldfeldShiftedZetaPole]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hbeta.ne')
  change AnalyticAt ℂ
    (fun s => goldfeldContourNumerator chi1 chi beta x s /
      (s - goldfeldShiftedZetaPole beta)) 0
  exact (differentiable_goldfeldContourNumerator
      hchi1 hchi hcross beta hx).analyticAt 0
    |>.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr hdelta0.symm)

/-- Evaluating the entire numerator at the shifted zeta point gives exactly
the source residue coefficient. -/
theorem goldfeldContourNumerator_apply_shiftedZetaPole
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : beta < 1)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldContourNumerator chi1 chi beta x
        (goldfeldShiftedZetaPole beta) =
      goldfeldContourResidue chi1 chi beta x := by
  have hdelta0 : goldfeldShiftedZetaPole beta ≠ 0 := by
    rw [goldfeldShiftedZetaPole]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hbeta.ne')
  have hshift : goldfeldShiftedZetaPole beta + (beta : ℂ) = 1 := by
    rw [goldfeldShiftedZetaPole]
    norm_num
  have hL := goldfeldShiftedLFunctionDividedSlope_mul chi1 beta hzero
    (goldfeldShiftedZetaPole beta)
  rw [hshift] at hL
  have hphi := goldfeldMellinContinuationData.equals_candidate
    (goldfeldShiftedZetaPole beta)
  rw [goldfeldMellinCandidate] at hphi
  have hphiMul : goldfeldShiftedZetaPole beta *
      goldfeldMellinContinuationData.Phi (goldfeldShiftedZetaPole beta) =
      -goldfeldDerivativeMellin (goldfeldShiftedZetaPole beta) := by
    rw [hphi]
    field_simp [hdelta0]
  rw [goldfeldContourNumerator, goldfeldContourResidue, hshift,
    riemannZeta₁_one, one_mul, ← hphiMul, ← hL]
  ring

/-- The regularized integrand has the exact shifted-zeta residue. -/
theorem goldfeldRegularizedContourIntegrand_residue
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta : beta < 1) (hx : 0 < x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    Tendsto
      (fun s => (s - goldfeldShiftedZetaPole beta) *
        goldfeldRegularizedContourIntegrand chi1 chi beta x s)
      (𝓝[≠] goldfeldShiftedZetaPole beta)
      (𝓝 (goldfeldContourResidue chi1 chi beta x)) := by
  have hnum : Tendsto (goldfeldContourNumerator chi1 chi beta x)
      (𝓝[≠] goldfeldShiftedZetaPole beta)
      (𝓝 (goldfeldContourNumerator chi1 chi beta x
        (goldfeldShiftedZetaPole beta))) :=
    (differentiable_goldfeldContourNumerator
      hchi1 hchi hcross beta hx).continuous
      |>.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [goldfeldContourNumerator_apply_shiftedZetaPole
    chi1 chi hbeta hzero] at hnum
  refine hnum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s - goldfeldShiftedZetaPole beta ≠ 0 :=
    sub_ne_zero.mpr (by simpa using hs)
  simp only [goldfeldRegularizedContourIntegrand]
  field_simp

/-- The original, totalized source integrand has the same exact punctured
residue at the shifted zeta point. -/
theorem goldfeldContourIntegrand_residue
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta : beta < 1) (hx : 0 < x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    Tendsto
      (fun s => (s - goldfeldShiftedZetaPole beta) *
        goldfeldContourIntegrand chi1 chi beta x s)
      (𝓝[≠] goldfeldShiftedZetaPole beta)
      (𝓝 (goldfeldContourResidue chi1 chi beta x)) := by
  have hdelta0 : goldfeldShiftedZetaPole beta ≠ 0 := by
    rw [goldfeldShiftedZetaPole]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hbeta.ne')
  have hreg := goldfeldRegularizedContourIntegrand_residue
    hchi1 hchi hcross hbeta hx hzero
  refine hreg.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_ne_nhdsWithin hdelta0] with s hspole hs0
  rw [goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    chi1 chi hzero hs0 (by simpa using hspole)]

end BoundedGaps.Maynard
