import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaRemovableRemainder
import BoundedGaps.BombieriVinogradov.Analytic.RectangleFinitePrincipalPartSum

/-!
# Dirichlet explicit-formula rectangle boundary

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 58--59,
equation (5.13), fixes the positive rectangle-boundary normalization. Printed
pp. 112--115 use that contour for the modified logarithmic derivative.

This file combines SEM-522's removable finite remainder with Mathlib's
rectangle Cauchy theorem and SEM-521's finite principal-part integral. It does
not classify zeros, estimate an edge, or replace the exact principal-pole
coefficient by the later main term. Semantic review: `SEM-523`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

private lemma continuous_horizontal_principal_part
    (c p : ℂ) (y : ℝ) (hy : y ≠ p.im) :
    Continuous (fun t : ℝ => c / ((t : ℂ) + y * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_ofReal.add (continuous_const.mul continuous_const)).sub
      continuous_const)
  intro t
  change ((t : ℂ) + (y : ℂ) * I - p) ≠ 0
  apply sub_ne_zero.mpr
  intro h
  have him := congrArg Complex.im h
  apply hy
  simpa using him

private lemma continuous_vertical_principal_part
    (c p : ℂ) (x : ℝ) (hx : x ≠ p.re) :
    Continuous (fun t : ℝ => c / ((x : ℂ) + t * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const)
  intro t
  change ((x : ℂ) + (t : ℂ) * I - p) ≠ 0
  apply sub_ne_zero.mpr
  intro h
  have hre := congrArg Complex.re h
  apply hx
  simpa using hre

private lemma intervalIntegrable_horizontal_of_continuousOn_rectangle
    {F : ℂ → ℂ} {z w : ℂ}
    (hF : ContinuousOn F (Complex.Rectangle z w))
    {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    IntervalIntegrable (fun t : ℝ => F ((t : ℂ) + y * I))
      volume z.re w.re := by
  apply ContinuousOn.intervalIntegrable
  apply hF.comp
  · fun_prop
  · intro t ht
    simpa [Complex.Rectangle, Complex.mem_reProdIm] using And.intro ht hy

private lemma intervalIntegrable_vertical_of_continuousOn_rectangle
    {F : ℂ → ℂ} {z w : ℂ}
    (hF : ContinuousOn F (Complex.Rectangle z w))
    {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    IntervalIntegrable (fun t : ℝ => F ((x : ℂ) + t * I))
      volume z.im w.im := by
  apply ContinuousOn.intervalIntegrable
  apply hF.comp
  · fun_prop
  · intro t ht
    simpa [Complex.Rectangle, Complex.mem_reProdIm] using And.intro hx ht

private lemma intervalIntegrable_horizontal_principalPartSum
    (P : Finset ℂ) (c : ℂ → ℂ) (y a b : ℝ)
    (hy : ∀ p ∈ P, y ≠ p.im) :
    IntervalIntegrable
      (fun t : ℝ => ∑ p ∈ P, c p / ((t : ℂ) + y * I - p))
      volume a b := by
  rw [← Finset.sum_fn]
  apply IntervalIntegrable.sum P
  intro p hp
  exact (continuous_horizontal_principal_part (c p) p y
    (hy p hp)).intervalIntegrable a b

private lemma intervalIntegrable_vertical_principalPartSum
    (P : Finset ℂ) (c : ℂ → ℂ) (x a b : ℝ)
    (hx : ∀ p ∈ P, x ≠ p.re) :
    IntervalIntegrable
      (fun t : ℝ => ∑ p ∈ P, c p / ((x : ℂ) + t * I - p))
      volume a b := by
  rw [← Finset.sum_fn]
  apply IntervalIntegrable.sum P
  intro p hp
  exact (continuous_vertical_principal_part (c p) p x
    (hx p hp)).intervalIntegrable a b

/-- The positive rectangle-boundary integral of the modified Dirichlet
explicit-formula integrand is `2 * pi * I` times the sum of its exact grouped
candidate contributions. -/
theorem
    wedgeIntegral_add_wedgeIntegral_dirichletExplicitFormulaIntegrand_eq_mul_sum_candidateContribution
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (z w : ℂ)
    (hP : ∀ rho ∈
      dirichletExplicitFormulaCandidateSingularitiesFinset chi z w,
        z.re < rho.re ∧ rho.re < w.re ∧
          z.im < rho.im ∧ rho.im < w.im) :
    Complex.wedgeIntegral z w
          (dirichletExplicitFormulaIntegrand chi x) +
        Complex.wedgeIntegral w z
          (dirichletExplicitFormulaIntegrand chi x) =
      (2 * Real.pi * Complex.I) *
        ∑ rho ∈
          dirichletExplicitFormulaCandidateSingularitiesFinset chi z w,
          dirichletExplicitFormulaCandidateContribution chi x rho := by
  classical
  let P := dirichletExplicitFormulaCandidateSingularitiesFinset chi z w
  let c : ℂ → ℂ := dirichletExplicitFormulaCandidateContribution chi x
  let f : ℂ → ℂ := dirichletExplicitFormulaIntegrand chi x
  let G : ℂ → ℂ := fun s => ∑ rho ∈ P, c rho / (s - rho)
  change ∀ rho ∈ P,
    z.re < rho.re ∧ rho.re < w.re ∧
      z.im < rho.im ∧ rho.im < w.im at hP
  change Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f =
    (2 * Real.pi * I) * ∑ rho ∈ P, c rho
  have hinside :
      dirichletExplicitFormulaCandidateSingularities chi z w ⊆
        interior (Complex.Rectangle z w) := by
    intro rho hrho
    have hrhoP : rho ∈ P := by
      change rho ∈
        dirichletExplicitFormulaCandidateSingularitiesFinset chi z w
      exact mem_dirichletExplicitFormulaCandidateSingularitiesFinset_iff.mpr hrho
    have hrhoPosition := hP rho hrhoP
    have hre : z.re ≤ w.re :=
      (hrhoPosition.1.trans hrhoPosition.2.1).le
    have him : z.im ≤ w.im :=
      (hrhoPosition.2.2.1.trans hrhoPosition.2.2.2).le
    rw [Complex.Rectangle, Complex.interior_reProdIm,
      uIcc_of_le hre, uIcc_of_le him, interior_Icc, interior_Icc,
      Complex.mem_reProdIm]
    exact ⟨⟨hrhoPosition.1, hrhoPosition.2.1⟩,
      ⟨hrhoPosition.2.2.1, hrhoPosition.2.2.2⟩⟩
  obtain ⟨F, hF, hEq⟩ :=
    exists_differentiableOn_dirichletExplicitFormulaIntegrand_sub_candidatePrincipalParts
      chi x z w hinside
  change Set.EqOn F (fun s => f s - G s) ((P : Set ℂ)ᶜ) at hEq
  have hFbottom :
      IntervalIntegrable (fun t : ℝ => F ((t : ℂ) + z.im * I))
        volume z.re w.re :=
    intervalIntegrable_horizontal_of_continuousOn_rectangle
      (y := z.im) hF.continuousOn left_mem_uIcc
  have hFtop :
      IntervalIntegrable (fun t : ℝ => F ((t : ℂ) + w.im * I))
        volume w.re z.re :=
    (intervalIntegrable_horizontal_of_continuousOn_rectangle
      (y := w.im) hF.continuousOn right_mem_uIcc).symm
  have hFright :
      IntervalIntegrable (fun t : ℝ => F ((w.re : ℂ) + t * I))
        volume z.im w.im :=
    intervalIntegrable_vertical_of_continuousOn_rectangle
      (x := w.re) hF.continuousOn right_mem_uIcc
  have hFleft :
      IntervalIntegrable (fun t : ℝ => F ((z.re : ℂ) + t * I))
        volume w.im z.im :=
    (intervalIntegrable_vertical_of_continuousOn_rectangle
      (x := z.re) hF.continuousOn left_mem_uIcc).symm
  have hGbottom :
      IntervalIntegrable (fun t : ℝ => G ((t : ℂ) + z.im * I))
        volume z.re w.re := by
    apply intervalIntegrable_horizontal_principalPartSum P c
    intro rho hrho
    exact ne_of_lt (hP rho hrho).2.2.1
  have hGtop :
      IntervalIntegrable (fun t : ℝ => G ((t : ℂ) + w.im * I))
        volume w.re z.re := by
    apply intervalIntegrable_horizontal_principalPartSum P c
    intro rho hrho
    exact ne_of_gt (hP rho hrho).2.2.2
  have hGright :
      IntervalIntegrable (fun t : ℝ => G ((w.re : ℂ) + t * I))
        volume z.im w.im := by
    apply intervalIntegrable_vertical_principalPartSum P c
    intro rho hrho
    exact ne_of_gt (hP rho hrho).2.1
  have hGleft :
      IntervalIntegrable (fun t : ℝ => G ((z.re : ℂ) + t * I))
        volume w.im z.im := by
    apply intervalIntegrable_vertical_principalPartSum P c
    intro rho hrho
    exact ne_of_lt (hP rho hrho).1
  have hnotBottom (t : ℝ) : ((t : ℂ) + z.im * I) ∉ P := by
    intro ht
    simpa using (hP _ ht).2.2.1
  have hnotTop (t : ℝ) : ((t : ℂ) + w.im * I) ∉ P := by
    intro ht
    simpa using (hP _ ht).2.2.2
  have hnotRight (t : ℝ) : ((w.re : ℂ) + t * I) ∉ P := by
    intro ht
    simpa using (hP _ ht).2.1
  have hnotLeft (t : ℝ) : ((z.re : ℂ) + t * I) ∉ P := by
    intro ht
    simpa using (hP _ ht).1
  have hdecomp {s : ℂ} (hs : s ∉ P) : f s = F s + G s := by
    have hs' : s ∈ ((P : Set ℂ)ᶜ) := hs
    exact eq_add_of_sub_eq (hEq hs').symm
  have hbottom :
      (∫ t : ℝ in z.re..w.re, f ((t : ℂ) + z.im * I)) =
        ∫ t : ℝ in z.re..w.re,
          F ((t : ℂ) + z.im * I) + G ((t : ℂ) + z.im * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp (hnotBottom t)
  have htop :
      (∫ t : ℝ in w.re..z.re, f ((t : ℂ) + w.im * I)) =
        ∫ t : ℝ in w.re..z.re,
          F ((t : ℂ) + w.im * I) + G ((t : ℂ) + w.im * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp (hnotTop t)
  have hright :
      (∫ t : ℝ in z.im..w.im, f ((w.re : ℂ) + t * I)) =
        ∫ t : ℝ in z.im..w.im,
          F ((w.re : ℂ) + t * I) + G ((w.re : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp (hnotRight t)
  have hleft :
      (∫ t : ℝ in w.im..z.im, f ((z.re : ℂ) + t * I)) =
        ∫ t : ℝ in w.im..z.im,
          F ((z.re : ℂ) + t * I) + G ((z.re : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp (hnotLeft t)
  have hzw : Complex.wedgeIntegral z w f =
      Complex.wedgeIntegral z w F + Complex.wedgeIntegral z w G := by
    simp only [Complex.wedgeIntegral]
    rw [hbottom, hright,
      intervalIntegral.integral_add hFbottom hGbottom,
      intervalIntegral.integral_add hFright hGright]
    simp only [smul_add]
    abel
  have hwz : Complex.wedgeIntegral w z f =
      Complex.wedgeIntegral w z F + Complex.wedgeIntegral w z G := by
    simp only [Complex.wedgeIntegral]
    rw [htop, hleft,
      intervalIntegral.integral_add hFtop hGtop,
      intervalIntegral.integral_add hFleft hGleft]
    simp only [smul_add]
    abel
  have hFzero :
      Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F = 0 := by
    have hconservative := hF.isConservativeOn z w (fun _ hs => hs)
    rw [hconservative]
    simp
  have hGsum :
      Complex.wedgeIntegral z w G + Complex.wedgeIntegral w z G =
        (2 * Real.pi * I) * ∑ rho ∈ P, c rho := by
    simpa [G] using
      wedgeIntegral_add_wedgeIntegral_finset_sum_div_sub_eq_two_pi_I_mul_sum
        z w P c hP
  calc
    Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f =
        (Complex.wedgeIntegral z w F + Complex.wedgeIntegral z w G) +
          (Complex.wedgeIntegral w z F + Complex.wedgeIntegral w z G) := by
      rw [hzw, hwz]
    _ = (Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F) +
        (Complex.wedgeIntegral z w G + Complex.wedgeIntegral w z G) := by
      abel
    _ = (2 * Real.pi * I) * ∑ rho ∈ P, c rho := by
      rw [hFzero, hGsum, zero_add]

end

end BoundedGaps.Maynard
