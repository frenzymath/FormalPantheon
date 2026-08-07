import BoundedGaps.Maynard.ConcreteS2OffFaceGoodEndpointShell
import BoundedGaps.Maynard.ConcreteS2ComplementFaceExpansion

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

theorem engelsmaS2OffFaceQuadraticIntegrand_normalized_eq
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple)
    (b c : ℕ) (u : engelsmaOffFaceFinset m → ℕ) :
    engelsmaS2OffFaceQuadraticIntegrand m b c
        (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) =
      faceQuadraticIntegrand (engelsmaIndexEquiv m) b c
        (engelsmaS2OffCoordinateLogFacePoint
          (engelsmaMaynardRadius alpha N) m
          (engelsmaOffFaceExtension m u)) := by
  unfold engelsmaS2OffFaceQuadraticIntegrand
    engelsmaS2OffFaceNormalizedLogPoint
  congr 1
  funext j
  obtain ⟨h, rfl⟩ := (engelsmaOffFaceIndexEquiv m).surjective j
  rw [engelsmaS2OffCoordinateLogFacePoint_reindex]
  rw [(engelsmaOffFaceIndexEquiv m).symm_apply_apply]
  simp [normalizedDivisorLogTuple]

def engelsmaS2OffFaceNaturalScale
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
    Real.log (engelsmaMaynardRadius alpha N)) ^
      Fintype.card (engelsmaOffFaceFinset m)

def engelsmaS2OffFaceGoodQuadraticMoment
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple)
    (b c : ℕ) : ℝ :=
  ∑ u ∈ engelsmaS2OffFaceGoodSupport
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m,
    engelsmaS2OffFaceQuadraticIntegrand m b c
        (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) *
      outerTupleWeight (engelsmaOffFaceFinset m)
        (engelsmaMaynardModulus N) u

def normalizedEngelsmaS2OffFaceGoodQuadraticMoment
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple)
    (b c : ℕ) : ℝ :=
  engelsmaS2OffFaceGoodQuadraticMoment alpha N m b c /
    engelsmaS2OffFaceNaturalScale alpha N m

def engelsmaS2OffFaceInnerGridQuadraticCellSum
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N b c : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex
      (engelsmaOffFaceFinset m) mesh,
    ∑ u ∈ engelsmaFractionalTupleShell
        (engelsmaOffFaceFinset m) alpha
          (fractionalGridLower mesh j)
          (fractionalGridUpper mesh j) N,
      engelsmaS2OffFaceQuadraticIntegrand m b c
          (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) *
        outerTupleWeight (engelsmaOffFaceFinset m)
          (engelsmaMaynardModulus N) u

def normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N b c : ℕ) : ℝ :=
  engelsmaS2OffFaceInnerGridQuadraticCellSum alpha m mesh N b c /
    engelsmaS2OffFaceNaturalScale alpha N m

def engelsmaS2OffFaceInnerGridQuadraticStepSum
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N b c : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex
      (engelsmaOffFaceFinset m) mesh,
    engelsmaS2OffFaceQuadraticIntegrand m b c
        (fractionalGridLower mesh j) *
      maynardS2OuterSquarefreeTupleShellMass
        (engelsmaOffFaceFinset m) (engelsmaMaynardModulus N)
        (fun h => engelsmaMaynardRadius
          (alpha * fractionalGridLower mesh j h) N)
        (fun h => engelsmaMaynardRadius
          (alpha * fractionalGridUpper mesh j h) N)

def engelsmaS2OffFaceBoundaryGridSupportMass
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaSimplexBoundaryGridShellUnion
      (engelsmaOffFaceFinset m) alpha mesh N,
    outerTupleWeight (engelsmaOffFaceFinset m)
      (engelsmaMaynardModulus N) u

def normalizedEngelsmaS2OffFaceBoundaryGridSupportMass
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N : ℕ) : ℝ :=
  engelsmaS2OffFaceBoundaryGridSupportMass alpha m mesh N /
    engelsmaS2OffFaceNaturalScale alpha N m

theorem engelsmaS2OffFaceQuadraticIntegrand_nonneg
    {m : BoundedGaps.engelsmaTuple} {b c : ℕ}
    {t : engelsmaOffFaceFinset m → ℝ}
    (ht : t ∈ finiteSimplexOf (engelsmaOffFaceFinset m)) :
    0 ≤ engelsmaS2OffFaceQuadraticIntegrand m b c t := by
  rw [engelsmaS2OffFaceQuadraticIntegrand_eq]
  apply mul_nonneg
  · exact pow_nonneg (sub_nonneg.mpr ht.2) b
  · exact pow_nonneg (Finset.sum_nonneg
      (fun h hh => sq_nonneg (t h))) c

set_option maxRecDepth 7000 in
theorem engelsmaS2OffFaceNormalizedLogPoint_mem_finiteSimplex
    {alpha : ℝ} {N : ℕ} {m : BoundedGaps.engelsmaTuple}
    {u : engelsmaOffFaceFinset m → ℕ}
    (hR : 1 < engelsmaMaynardRadius alpha N)
    (hu : u ∈ preSievedSimplexTupleSupport
      (engelsmaOffFaceFinset m) (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N)) :
    engelsmaS2OffFaceNormalizedLogPoint alpha N m u ∈
      finiteSimplexOf (engelsmaOffFaceFinset m) := by
  let H := engelsmaOffFaceFinset m
  have huBox : u ∈ maynardDivisorTupleBox H
      (engelsmaMaynardRadius alpha N) := by
    rw [mem_maynardDivisorTupleBox_iff]
    intro h
    have huh := Fintype.mem_piFinset.mp
      (mem_preSievedSimplexTupleSupport_iff.mp hu).1 h
    have huhData := Finset.mem_filter.mp huh
    exact ⟨huhData.2.1, Finset.mem_range.mp huhData.1⟩
  have hcoord : ∀ h : H,
      engelsmaS2OffFaceNormalizedLogPoint alpha N m u h ∈
        Set.Icc (0 : ℝ) 1 := by
    intro h
    exact normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hR huBox h
  have huPos : ∀ h : H, 0 < u h := fun h =>
    (preSievedSimplexTupleSupport_coordinate hu h).1
  have hsum :=
    (divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
      hR huPos).mp (mem_preSievedSimplexTupleSupport_iff.mp hu).2
  constructor
  · rw [maynardCubeOf, Set.mem_pi]
    exact fun h hh => hcoord h
  · simpa [engelsmaS2OffFaceNormalizedLogPoint, H] using hsum.le

theorem eventually_engelsmaS2OffFaceNaturalScale_pos
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    ∀ᶠ N : ℕ in atTop,
      0 < engelsmaS2OffFaceNaturalScale alpha N m := by
  filter_upwards [eventually_one_lt_engelsmaMaynardRadius halpha] with N hR
  unfold engelsmaS2OffFaceNaturalScale
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  have hL : 0 < Real.log (engelsmaMaynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hR)
  positivity

set_option maxRecDepth 7000 in
theorem engelsmaS2OffFaceGridQuadraticStep_eq_div
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N b c : ℕ) :
    engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c =
      engelsmaS2OffFaceInnerGridQuadraticStepSum alpha m mesh N b c /
        engelsmaS2OffFaceNaturalScale alpha N m := by
  unfold engelsmaS2OffFaceGridQuadraticStep
    engelsmaS2OffFaceInnerGridQuadraticStepSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  unfold normalizedMaynardS2OuterSquarefreeTupleShellMass
    engelsmaS2OffFaceNaturalScale
  ring

set_option maxRecDepth 7000 in
theorem engelsmaS2OffFaceInnerGridQuadraticStepSum_eq_cellSum
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N b c : ℕ) :
    engelsmaS2OffFaceInnerGridQuadraticStepSum alpha m mesh N b c =
      ∑ j ∈ fractionalSimplexInnerGridIndex
          (engelsmaOffFaceFinset m) mesh,
        ∑ u ∈ engelsmaFractionalTupleShell
            (engelsmaOffFaceFinset m) alpha
              (fractionalGridLower mesh j)
              (fractionalGridUpper mesh j) N,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j) *
            outerTupleWeight (engelsmaOffFaceFinset m)
              (engelsmaMaynardModulus N) u := by
  unfold engelsmaS2OffFaceInnerGridQuadraticStepSum
    maynardS2OuterSquarefreeTupleShellMass
    maynardS2OuterSquarefreeTupleShell outerTupleWeight
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  rfl

set_option maxRecDepth 8000 in
theorem engelsmaS2OffFaceInnerGridCell_sub_step_le
    {alpha : ℝ} {m : BoundedGaps.engelsmaTuple}
    {mesh N b c : ℕ} {epsilon : ℝ}
    (_hepsilon : 0 ≤ epsilon)
    (hosc : ∀ j ∈ fractionalSimplexInnerGridIndex
        (engelsmaOffFaceFinset m) mesh,
      ∀ u ∈ engelsmaFractionalTupleShell
          (engelsmaOffFaceFinset m) alpha
            (fractionalGridLower mesh j)
            (fractionalGridUpper mesh j) N,
        |engelsmaS2OffFaceQuadraticIntegrand m b c
            (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) -
          engelsmaS2OffFaceQuadraticIntegrand m b c
            (fractionalGridLower mesh j)| ≤ epsilon) :
    |engelsmaS2OffFaceInnerGridQuadraticCellSum
          alpha m mesh N b c -
        engelsmaS2OffFaceInnerGridQuadraticStepSum
          alpha m mesh N b c| ≤
      epsilon * ∑ j ∈ fractionalSimplexInnerGridIndex
          (engelsmaOffFaceFinset m) mesh,
        maynardS2OuterSquarefreeTupleShellMass
          (engelsmaOffFaceFinset m) (engelsmaMaynardModulus N)
          (fun h => engelsmaMaynardRadius
            (alpha * fractionalGridLower mesh j h) N)
          (fun h => engelsmaMaynardRadius
            (alpha * fractionalGridUpper mesh j h) N) := by
  rw [engelsmaS2OffFaceInnerGridQuadraticStepSum_eq_cellSum]
  unfold engelsmaS2OffFaceInnerGridQuadraticCellSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ fractionalSimplexInnerGridIndex
        (engelsmaOffFaceFinset m) mesh,
      |(∑ u ∈ engelsmaFractionalTupleShell
          (engelsmaOffFaceFinset m) alpha
            (fractionalGridLower mesh j)
            (fractionalGridUpper mesh j) N,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) *
            outerTupleWeight (engelsmaOffFaceFinset m)
              (engelsmaMaynardModulus N) u) -
        ∑ u ∈ engelsmaFractionalTupleShell
          (engelsmaOffFaceFinset m) alpha
            (fractionalGridLower mesh j)
            (fractionalGridUpper mesh j) N,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j) *
            outerTupleWeight (engelsmaOffFaceFinset m)
              (engelsmaMaynardModulus N) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ fractionalSimplexInnerGridIndex
        (engelsmaOffFaceFinset m) mesh,
      epsilon * maynardS2OuterSquarefreeTupleShellMass
        (engelsmaOffFaceFinset m) (engelsmaMaynardModulus N)
        (fun h => engelsmaMaynardRadius
          (alpha * fractionalGridLower mesh j h) N)
        (fun h => engelsmaMaynardRadius
          (alpha * fractionalGridUpper mesh j h) N) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ u ∈ engelsmaFractionalTupleShell
            (engelsmaOffFaceFinset m) alpha
              (fractionalGridLower mesh j)
              (fractionalGridUpper mesh j) N,
          |engelsmaS2OffFaceQuadraticIntegrand m b c
                (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) *
              outerTupleWeight (engelsmaOffFaceFinset m)
                (engelsmaMaynardModulus N) u -
            engelsmaS2OffFaceQuadraticIntegrand m b c
                (fractionalGridLower mesh j) *
              outerTupleWeight (engelsmaOffFaceFinset m)
                (engelsmaMaynardModulus N) u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ u ∈ engelsmaFractionalTupleShell
            (engelsmaOffFaceFinset m) alpha
              (fractionalGridLower mesh j)
              (fractionalGridUpper mesh j) N,
          epsilon * outerTupleWeight (engelsmaOffFaceFinset m)
            (engelsmaMaynardModulus N) u := by
          apply Finset.sum_le_sum
          intro u hu
          have hw : 0 ≤ outerTupleWeight (engelsmaOffFaceFinset m)
              (engelsmaMaynardModulus N) u := by
            unfold outerTupleWeight
            exact Finset.prod_nonneg (fun h hh =>
              maynardS2OuterSquarefreeAF_nonneg
                (engelsmaMaynardModulus N) (u h))
          rw [← sub_mul, abs_mul, abs_of_nonneg hw]
          exact mul_le_mul_of_nonneg_right (hosc j hj u hu) hw
        _ = _ := by
          unfold maynardS2OuterSquarefreeTupleShellMass
            maynardS2OuterSquarefreeTupleShell outerTupleWeight
          rw [Finset.mul_sum]
          rfl
    _ = _ := by rw [Finset.mul_sum]

set_option maxRecDepth 7000 in
theorem eventually_normalizedEngelsmaS2OffFaceBoundaryGridSupportMass_eq_stepMass
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple)
    {mesh : ℕ} (hmesh : 0 < mesh) :
    ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaS2OffFaceBoundaryGridSupportMass
          alpha m mesh N =
        normalizedEngelsmaS2OffFaceBoundaryGridStepMass
          alpha m mesh N := by
  have hdis := eventually_engelsmaFractionalGridShells_pairwise_disjoint
    (H := engelsmaOffFaceFinset m) halpha hmesh
  filter_upwards [hdis] with N hdisN
  unfold normalizedEngelsmaS2OffFaceBoundaryGridSupportMass
    engelsmaS2OffFaceBoundaryGridSupportMass
    normalizedEngelsmaS2OffFaceBoundaryGridStepMass
    normalizedMaynardS2OuterSquarefreeTupleShellMass
    engelsmaSimplexBoundaryGridShellUnion
  rw [Finset.sum_biUnion]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    unfold maynardS2OuterSquarefreeTupleShellMass
      maynardS2OuterSquarefreeTupleShell outerTupleWeight
    rfl
  · intro j hj k hk hne
    exact hdisN j k hne


end BoundedGaps.Maynard
