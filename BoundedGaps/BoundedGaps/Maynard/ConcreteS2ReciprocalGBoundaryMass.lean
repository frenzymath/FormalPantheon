import BoundedGaps.Maynard.ConcreteS2ReciprocalGShellLimit
import BoundedGaps.Maynard.ConcreteS2OffFaceBoundary
import BoundedGaps.Maynard.ConcreteS2OffFaceGoodMomentCore

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def normalizedEngelsmaS2ReciprocalGBoundaryGridStepMass
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexBoundaryGridIndex
      (engelsmaOffFaceFinset m) mesh,
    normalizedMaynardS2ReciprocalGTupleShellMass
      (engelsmaOffFaceFinset m) alpha N
      (fun h => engelsmaMaynardRadius
        (alpha * fractionalGridLower mesh j h) N)
      (fun h => engelsmaMaynardRadius
        (alpha * fractionalGridUpper mesh j h) N)

set_option maxRecDepth 7000 in
set_option maxHeartbeats 800000 in
theorem tendsto_normalizedEngelsmaS2ReciprocalGBoundaryGridStepMass
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple)
    {mesh : ℕ} (hmesh : 0 < mesh) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2ReciprocalGBoundaryGridStepMass alpha m mesh N)
      atTop (nhds (simplexBoundaryGridVolume
        (engelsmaOffFaceFinset m) mesh)) := by
  let H := engelsmaOffFaceFinset m
  let I := fractionalSimplexBoundaryGridIndex H mesh
  have hlim :=
    tendsto_finite_linear_combination_normalizedMaynardS2ReciprocalGTupleShellMass
      halpha I (fun _ => (1 : ℝ))
      (fun j => fractionalGridLower mesh j)
      (fun j => fractionalGridUpper mesh j)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hmesh
        (Finset.mem_filter.mp hj).1 h).1)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hmesh
        (Finset.mem_filter.mp hj).1 h).2.1)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hmesh
        (Finset.mem_filter.mp hj).1 h).2.2)
  simpa [normalizedEngelsmaS2ReciprocalGBoundaryGridStepMass, I, H,
    simplexBoundaryGridVolume] using hlim

def engelsmaS2ReciprocalGBoundaryGridSupportMass
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaSimplexBoundaryGridShellUnion
      (engelsmaOffFaceFinset m) alpha mesh N,
    ∏ h : engelsmaOffFaceFinset m,
      maynardS2ReciprocalGSquarefreeAF
        (engelsmaMaynardModulus N) (u h)

def normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N : ℕ) : ℝ :=
  engelsmaS2ReciprocalGBoundaryGridSupportMass alpha m mesh N /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^
        Fintype.card (engelsmaOffFaceFinset m)

set_option maxRecDepth 7000 in
theorem eventually_normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass_eq_stepMass
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple)
    {mesh : ℕ} (hmesh : 0 < mesh) :
    ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
          alpha m mesh N =
        normalizedEngelsmaS2ReciprocalGBoundaryGridStepMass
          alpha m mesh N := by
  have hdis := eventually_engelsmaFractionalGridShells_pairwise_disjoint
    (H := engelsmaOffFaceFinset m) halpha hmesh
  filter_upwards [hdis] with N hdisN
  unfold normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
    engelsmaS2ReciprocalGBoundaryGridSupportMass
    normalizedEngelsmaS2ReciprocalGBoundaryGridStepMass
    normalizedMaynardS2ReciprocalGTupleShellMass
    engelsmaSimplexBoundaryGridShellUnion
  rw [Finset.sum_biUnion]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    unfold maynardS2ReciprocalGTupleShellMass
      maynardS2ReciprocalGTupleShell
    rfl
  · intro j hj k hk hne
    exact hdisN j k hne

theorem tendsto_normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) {mesh : ℕ} (hmesh : 0 < mesh) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass alpha m mesh N)
      atTop (nhds (simplexBoundaryGridVolume
        (engelsmaOffFaceFinset m) mesh)) := by
  have hstep := tendsto_normalizedEngelsmaS2ReciprocalGBoundaryGridStepMass
    halpha m hmesh
  apply hstep.congr'
  filter_upwards [eventually_normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass_eq_stepMass
    halpha m hmesh] with N hN
  exact hN.symm

def engelsmaS2ReciprocalGFractionalTupleBoxMass
    (H : Finset ℕ) (alpha : ℝ) (beta : H → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaFractionalTupleBox H alpha beta N,
    ∏ h : H, maynardS2ReciprocalGSquarefreeAF
      (engelsmaMaynardModulus N) (u h)

theorem engelsmaS2ReciprocalGFractionalTupleBoxMass_eq_prod_mean
    {H : Finset ℕ} {alpha : ℝ} {beta : H → ℝ} (N : ℕ) :
    engelsmaS2ReciprocalGFractionalTupleBoxMass H alpha beta N =
      ∏ h : H,
        maynardS2ReciprocalGSquarefreeMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N) := by
  unfold engelsmaS2ReciprocalGFractionalTupleBoxMass engelsmaFractionalTupleBox
    squarefreeCoprimeTupleBox
  calc
    (∑ u ∈ Fintype.piFinset
        (fun h : H => squarefreeCoprimeCoordinateSupport
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N)),
        ∏ h : H, maynardS2ReciprocalGSquarefreeAF
          (engelsmaMaynardModulus N) (u h)) =
        ∏ h : H, ∑ n ∈ squarefreeCoprimeCoordinateSupport
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N),
          maynardS2ReciprocalGSquarefreeAF
            (engelsmaMaynardModulus N) n := by
      exact (Finset.prod_univ_sum _ _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro h hh
      exact maynardS2ReciprocalGSquarefreeCoordinateSupport_sum_eq_mean _ _

def normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass
    (H : Finset ℕ) (alpha : ℝ) (beta : H → ℝ) (N : ℕ) : ℝ :=
  engelsmaS2ReciprocalGFractionalTupleBoxMass H alpha beta N /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

set_option maxRecDepth 8000 in
theorem tendsto_normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta : H → ℝ) (hbeta : ∀ h, beta h ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass H alpha beta N)
      atTop (nhds (∏ h : H, beta h)) := by
  have hcoord : ∀ h : H, Tendsto (fun N : ℕ =>
      maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta h) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds (beta h)) := by
    intro h
    exact tendsto_engelsmaS2ReciprocalGSquarefreeMean_fractionalRadius_nonneg
      halpha (hbeta h).1
  have hprod : Tendsto (fun N : ℕ =>
      ∏ h : H,
        maynardS2ReciprocalGSquarefreeMean
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
  unfold normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass
  rw [engelsmaS2ReciprocalGFractionalTupleBoxMass_eq_prod_mean]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Fintype.card_coe]
  rw [Finset.card_univ]
  simp only [Fintype.card_coe]

def normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxMassSum
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ h : H, normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass
    H alpha (unitBoundaryBeta h) N

def engelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaUnitBoundaryBoxUnion H alpha N,
    ∏ h : H, maynardS2ReciprocalGSquarefreeAF
      (engelsmaMaynardModulus N) (u h)

def normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  engelsmaS2ReciprocalGUnitBoundaryBoxUnionMass H alpha N /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

theorem engelsmaS2ReciprocalGUnitBoundaryBoxUnionMass_le_sum
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) :
    engelsmaS2ReciprocalGUnitBoundaryBoxUnionMass H alpha N ≤
      ∑ h : H, engelsmaS2ReciprocalGFractionalTupleBoxMass
        H alpha (unitBoundaryBeta h) N := by
  unfold engelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
    engelsmaUnitBoundaryBoxUnion
    engelsmaS2ReciprocalGFractionalTupleBoxMass
  apply sum_biUnion_le_sum_sum_of_nonneg
  intro u
  exact Finset.prod_nonneg (fun h hh =>
    maynardS2ReciprocalGSquarefreeAF_nonneg _ _)

set_option maxRecDepth 8000 in
theorem tendsto_normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass H alpha N)
      atTop (nhds 0) := by
  have hsum : Tendsto (fun N : ℕ =>
      ∑ h : H, normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass
        H alpha (unitBoundaryBeta h) N)
      atTop (nhds (∑ _h : H, (0 : ℝ))) := by
    apply tendsto_finsetSum Finset.univ
    intro h hh
    have hlim := tendsto_normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass
      halpha (unitBoundaryBeta h)
        (fun i => by
          by_cases hi : i = h <;> simp [unitBoundaryBeta, hi])
    have hzero : ∏ i : H, unitBoundaryBeta h i = 0 := by
      classical
      apply Finset.prod_eq_zero (Finset.mem_univ h)
      simp [unitBoundaryBeta]
    rw [hzero] at hlim
    simpa using hlim
  have hnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass H alpha N := by
    filter_upwards [
      (tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually
        (eventually_gt_atTop 0)] with N hlogN
    unfold normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
      engelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro u hu
      exact Finset.prod_nonneg (fun h hh =>
        maynardS2ReciprocalGSquarefreeAF_nonneg _ _)
    · have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
      positivity
  have hsum0 : Tendsto (fun N : ℕ =>
      ∑ h : H, normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass
        H alpha (unitBoundaryBeta h) N) atTop (nhds 0) := by
    simpa using hsum
  apply squeeze_zero' hnonneg ?_ hsum0
  filter_upwards [
    (tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually
      (eventually_gt_atTop 0)] with N hlogN
  unfold normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
    normalizedEngelsmaS2ReciprocalGFractionalTupleBoxMass
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right
    (engelsmaS2ReciprocalGUnitBoundaryBoxUnionMass_le_sum H alpha N)
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  positivity

end BoundedGaps.Maynard
