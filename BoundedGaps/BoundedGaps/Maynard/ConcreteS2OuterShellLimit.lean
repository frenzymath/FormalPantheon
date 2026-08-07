import BoundedGaps.Maynard.ConcreteS2OuterMeanLimit
import BoundedGaps.Maynard.MaynardS2OuterFaceBox
import BoundedGaps.Maynard.ConcreteScalarEndpointZero
import BoundedGaps.Maynard.ConcreteFractionalRectangle

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

theorem maynardS2OuterSquarefreeCoordinateShell_sum_eq_sub_mean
    {W Qlo Qhi : ℕ} (hQ : Qlo ≤ Qhi) :
    (∑ n ∈ squarefreeCoprimeCoordinateShell W Qlo Qhi,
      maynardS2OuterSquarefreeAF W n) =
      maynardS2OuterSquarefreeMean W Qhi -
        maynardS2OuterSquarefreeMean W Qlo := by
  unfold squarefreeCoprimeCoordinateShell
  rw [← maynardS2OuterSquarefreeCoordinateSupport_sum_eq_mean W Qhi,
    ← maynardS2OuterSquarefreeCoordinateSupport_sum_eq_mean W Qlo]
  rw [Finset.sum_sdiff_eq_sub]
  exact squarefreeCoprimeCoordinateSupport_subset hQ

theorem tendsto_engelsmaS2OuterSquarefreeMean_fractionalRadius_nonneg
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 ≤ beta) :
    Tendsto (fun N : ℕ =>
      maynardS2OuterSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds beta) := by
  by_cases hzero : beta = 0
  · subst beta
    have hInv := tendsto_inv_engelsmaSingularSeries_mul_logRadius_zero halpha
    apply hInv.congr'
    filter_upwards [] with N
    have hR : engelsmaMaynardRadius (0 : ℝ) N = 1 := by
      unfold engelsmaMaynardRadius maynardDivisorCutoff
      simp
    simp [mul_zero, hR, maynardS2OuterSquarefreeMean_one]
  · have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
    have hgamma : 0 < alpha * beta := mul_pos halpha hbetaPos
    have hmean :=
      tendsto_engelsmaS2OuterSquarefreeMean_div_preSieveLeadingTerm_one
        hgamma
    have hratio := tendsto_log_engelsmaMaynardRadius_ratio hgamma halpha
    have hproduct : Tendsto (fun N : ℕ =>
        (maynardS2OuterSquarefreeMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * beta) N) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius (alpha * beta) N))) *
        (Real.log (engelsmaMaynardRadius (alpha * beta) N) /
          Real.log (engelsmaMaynardRadius alpha N)))
        atTop (nhds beta) := by
      simpa [ne_of_gt halpha] using hmean.mul hratio
    apply hproduct.congr'
    filter_upwards [
      (tendsto_log_engelsmaMaynardRadius_atTop hgamma).eventually
        (eventually_ne_atTop 0),
      (tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually
        (eventually_ne_atTop 0)] with N hGamma hAlpha
    have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
    field_simp [hS.ne', hGamma, hAlpha]

def maynardS2OuterSquarefreeTupleShell
    (H : Finset ℕ) (W : ℕ) (Qlo Qhi : H → ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset fun h =>
    squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h)

def maynardS2OuterSquarefreeTupleShellMass
    (H : Finset ℕ) (W : ℕ) (Qlo Qhi : H → ℕ) : ℝ :=
  ∑ u ∈ maynardS2OuterSquarefreeTupleShell H W Qlo Qhi,
    ∏ h : H, maynardS2OuterSquarefreeAF W (u h)

theorem maynardS2OuterSquarefreeTupleShellMass_eq_prod_sub_mean
    {H : Finset ℕ} {W : ℕ} {Qlo Qhi : H → ℕ}
    (hQ : ∀ h : H, Qlo h ≤ Qhi h) :
    maynardS2OuterSquarefreeTupleShellMass H W Qlo Qhi =
      ∏ h : H,
        (maynardS2OuterSquarefreeMean W (Qhi h) -
          maynardS2OuterSquarefreeMean W (Qlo h)) := by
  unfold maynardS2OuterSquarefreeTupleShellMass
    maynardS2OuterSquarefreeTupleShell
  calc
    (∑ u ∈ Fintype.piFinset
        (fun h : H => squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h)),
        ∏ h : H, maynardS2OuterSquarefreeAF W (u h)) =
        ∏ h : H, ∑ n ∈ squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h),
          maynardS2OuterSquarefreeAF W n := by
      exact (Finset.prod_univ_sum
        (fun h : H => squarefreeCoprimeCoordinateShell W (Qlo h) (Qhi h))
        (fun h : H => fun n => maynardS2OuterSquarefreeAF W n)).symm
    _ = ∏ h : H,
        (maynardS2OuterSquarefreeMean W (Qhi h) -
          maynardS2OuterSquarefreeMean W (Qlo h)) := by
      apply Finset.prod_congr rfl
      intro h hh
      exact maynardS2OuterSquarefreeCoordinateShell_sum_eq_sub_mean (hQ h)

def normalizedMaynardS2OuterSquarefreeTupleShellMass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ)
    (Qlo Qhi : H → ℕ) : ℝ :=
  maynardS2OuterSquarefreeTupleShellMass H
      (engelsmaMaynardModulus N) Qlo Qhi /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

set_option maxRecDepth 6000 in
theorem tendsto_normalizedMaynardS2OuterSquarefreeTupleShellMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta gamma : H → ℝ)
    (hbeta : ∀ h, beta h ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : ∀ h, gamma h ∈ Set.Icc (0 : ℝ) 1)
    (horder : ∀ h, beta h ≤ gamma h) :
    Tendsto (fun N : ℕ =>
      normalizedMaynardS2OuterSquarefreeTupleShellMass H alpha N
        (fun h => engelsmaMaynardRadius (alpha * beta h) N)
        (fun h => engelsmaMaynardRadius (alpha * gamma h) N))
      atTop (nhds (∏ h : H, (gamma h - beta h))) := by
  have hcoord : ∀ h : H, Tendsto (fun N : ℕ =>
      (maynardS2OuterSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * gamma h) N) -
        maynardS2OuterSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N)) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (gamma h - beta h)) := by
    intro h
    have hgammaT := tendsto_engelsmaS2OuterSquarefreeMean_fractionalRadius_nonneg
      halpha (hgamma h).1
    have hbetaT := tendsto_engelsmaS2OuterSquarefreeMean_fractionalRadius_nonneg
      halpha (hbeta h).1
    have hdiff := hgammaT.sub hbetaT
    apply hdiff.congr'
    have hmul : alpha * beta h ≤ alpha * gamma h :=
      mul_le_mul_of_nonneg_left (horder h) halpha.le
    filter_upwards [eventually_engelsmaMaynardRadius_mono_exponent hmul] with
      N hQ
    rw [sub_div]

  have hprod : Tendsto (fun N : ℕ =>
      ∏ h : H,
        (maynardS2OuterSquarefreeMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * gamma h) N) -
          maynardS2OuterSquarefreeMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * beta h) N)) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (∏ h : H, (gamma h - beta h))) := by
    apply tendsto_finsetProd Finset.univ
    intro h hh
    exact hcoord h
  apply hprod.congr'
  have horderEvent : ∀ᶠ N : ℕ in atTop, ∀ h : H,
      engelsmaMaynardRadius (alpha * beta h) N ≤
        engelsmaMaynardRadius (alpha * gamma h) N := by
    have hev : ∀ᶠ N : ℕ in atTop, ∀ h ∈ (Finset.univ : Finset H),
        engelsmaMaynardRadius (alpha * beta h) N ≤
          engelsmaMaynardRadius (alpha * gamma h) N := by
      apply (Finset.univ : Finset H).eventually_all.mpr
      intro h hh
      exact eventually_engelsmaMaynardRadius_mono_exponent
        (mul_le_mul_of_nonneg_left (horder h) halpha.le)
    filter_upwards [hev] with N hN h
    exact hN h (Finset.mem_univ h)
  filter_upwards [horderEvent] with N hN
  unfold normalizedMaynardS2OuterSquarefreeTupleShellMass
  rw [Finset.prod_div_distrib]
  rw [maynardS2OuterSquarefreeTupleShellMass_eq_prod_sub_mean]
  · simp only [Finset.prod_const, Fintype.card_coe]
    rw [Finset.card_univ]
    simp only [Fintype.card_coe]
  · intro h
    exact hN h

theorem tendsto_finite_linear_combination_normalizedMaynardS2OuterSquarefreeTupleShellMass
    {ι : Type*} {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (I : Finset ι) (coeff : ι → ℝ)
    (beta gamma : ι → H → ℝ)
    (hbeta : ∀ i ∈ I, ∀ h, beta i h ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : ∀ i ∈ I, ∀ h, gamma i h ∈ Set.Icc (0 : ℝ) 1)
    (horder : ∀ i ∈ I, ∀ h, beta i h ≤ gamma i h) :
    Tendsto (fun N : ℕ =>
      ∑ i ∈ I, coeff i *
        normalizedMaynardS2OuterSquarefreeTupleShellMass H alpha N
          (fun h => engelsmaMaynardRadius (alpha * beta i h) N)
          (fun h => engelsmaMaynardRadius (alpha * gamma i h) N))
      atTop (nhds (∑ i ∈ I, coeff i *
        ∏ h : H, (gamma i h - beta i h))) := by
  apply tendsto_finsetSum I
  intro i hi
  have hlim := tendsto_normalizedMaynardS2OuterSquarefreeTupleShellMass
    halpha (beta i) (gamma i)
    (hbeta i hi) (hgamma i hi) (horder i hi)
  exact hlim.const_mul (coeff i)

end BoundedGaps.Maynard
