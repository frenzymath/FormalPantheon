import BoundedGaps.Maynard.ConcreteS2OffFaceBoundary
import BoundedGaps.Maynard.MaynardS2OuterTupleBoxFactorization

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def engelsmaS2OuterFractionalTupleBoxMass
    (H : Finset ℕ) (alpha : ℝ) (beta : H → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaFractionalTupleBox H alpha beta N,
    ∏ h : H, maynardS2OuterSquarefreeAF
      (engelsmaMaynardModulus N) (u h)

def normalizedEngelsmaS2OuterFractionalTupleBoxMass
    (H : Finset ℕ) (alpha : ℝ) (beta : H → ℝ) (N : ℕ) : ℝ :=
  engelsmaS2OuterFractionalTupleBoxMass H alpha beta N /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
theorem tendsto_normalizedEngelsmaS2OuterFractionalTupleBoxMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta : H → ℝ) (hbeta : ∀ h, beta h ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2OuterFractionalTupleBoxMass H alpha beta N)
      atTop (nhds (∏ h : H, beta h)) := by
  have hcoord : ∀ h : H, Tendsto (fun N : ℕ =>
      maynardS2OuterSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (beta h)) := by
    intro h
    exact tendsto_engelsmaS2OuterSquarefreeMean_fractionalRadius_nonneg
      halpha (hbeta h).1
  have hprod : Tendsto (fun N : ℕ =>
      ∏ h : H,
        maynardS2OuterSquarefreeMean
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * beta h) N) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (∏ h : H, beta h)) := by
    apply tendsto_finsetProd Finset.univ
    intro h hh
    exact hcoord h
  apply hprod.congr'
  filter_upwards [] with N
  unfold normalizedEngelsmaS2OuterFractionalTupleBoxMass
    engelsmaS2OuterFractionalTupleBoxMass engelsmaFractionalTupleBox
  rw [maynardS2OuterSquarefreeTupleBox_sum_eq_prod_mean]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Fintype.card_coe]
  rw [Finset.card_univ]
  simp only [Fintype.card_coe]

def normalizedEngelsmaS2OuterUnitBoundaryBoxMassSum
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ h : H, normalizedEngelsmaS2OuterFractionalTupleBoxMass
    H alpha (unitBoundaryBeta h) N

def engelsmaS2OuterUnitBoundaryBoxUnionMass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaUnitBoundaryBoxUnion H alpha N,
    ∏ h : H, maynardS2OuterSquarefreeAF
      (engelsmaMaynardModulus N) (u h)

def normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  engelsmaS2OuterUnitBoundaryBoxUnionMass H alpha N /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

theorem tendsto_normalizedEngelsmaS2OuterUnitBoundaryBoxMassSum_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2OuterUnitBoundaryBoxMassSum H alpha N)
      atTop (nhds 0) := by
  have hsum : Tendsto (fun N : ℕ =>
      ∑ h : H, normalizedEngelsmaS2OuterFractionalTupleBoxMass
        H alpha (unitBoundaryBeta h) N)
      atTop (nhds (∑ _h : H, (0 : ℝ))) := by
    apply tendsto_finsetSum Finset.univ
    intro h hh
    have hlim := tendsto_normalizedEngelsmaS2OuterFractionalTupleBoxMass
      halpha (unitBoundaryBeta h)
        (fun i => by
          by_cases hi : i = h <;> simp [unitBoundaryBeta, hi])
    have hzero : ∏ i : H, unitBoundaryBeta h i = 0 := by
      classical
      apply Finset.prod_eq_zero (Finset.mem_univ h)
      simp [unitBoundaryBeta]
    rw [hzero] at hlim
    simpa using hlim
  simpa [normalizedEngelsmaS2OuterUnitBoundaryBoxMassSum] using hsum

theorem engelsmaS2OuterUnitBoundaryBoxUnionMass_le_sum
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) :
    engelsmaS2OuterUnitBoundaryBoxUnionMass H alpha N ≤
      ∑ h : H, engelsmaS2OuterFractionalTupleBoxMass
        H alpha (unitBoundaryBeta h) N := by
  unfold engelsmaS2OuterUnitBoundaryBoxUnionMass
    engelsmaUnitBoundaryBoxUnion engelsmaS2OuterFractionalTupleBoxMass
  apply sum_biUnion_le_sum_sum_of_nonneg
  intro u
  exact Finset.prod_nonneg (fun h hh =>
    maynardS2OuterSquarefreeAF_nonneg (engelsmaMaynardModulus N) (u h))

set_option maxRecDepth 8000 in
theorem tendsto_normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass H alpha N)
      atTop (nhds 0) := by
  have henvelope :=
    tendsto_normalizedEngelsmaS2OuterUnitBoundaryBoxMassSum_zero
      (H := H) halpha
  have hlog := tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass H alpha N := by
    filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with N hlogN
    unfold normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass
      engelsmaS2OuterUnitBoundaryBoxUnionMass
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro u hu
      exact Finset.prod_nonneg (fun h hh =>
        maynardS2OuterSquarefreeAF_nonneg (engelsmaMaynardModulus N) (u h))
    · have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
      positivity
  apply squeeze_zero' hnonneg ?_ henvelope
  filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with N hlogN
  unfold normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass
    normalizedEngelsmaS2OuterUnitBoundaryBoxMassSum
    normalizedEngelsmaS2OuterFractionalTupleBoxMass
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right
    (engelsmaS2OuterUnitBoundaryBoxUnionMass_le_sum H alpha N)
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  positivity

end BoundedGaps.Maynard
