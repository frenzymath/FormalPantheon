import BoundedGaps.Maynard.ConcreteS2OffFaceComplementMoment
import BoundedGaps.Maynard.ConcreteFractionalTupleBoxSimplex
import BoundedGaps.Maynard.ConcreteSimplexBoundaryMesh
import BoundedGaps.Maynard.ConcreteS2OuterShellLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def engelsmaS2OffFaceQuadraticIntegrand
    (m : BoundedGaps.engelsmaTuple) (b c : ℕ)
    (t : engelsmaOffFaceFinset m → ℝ) : ℝ :=
  faceQuadraticIntegrand (engelsmaIndexEquiv m) b c
    (fun j => t ((engelsmaOffFaceIndexEquiv m).symm j))

def engelsmaS2OffFaceGridQuadraticStep
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple)
    (mesh N b c : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex
      (engelsmaOffFaceFinset m) mesh,
      engelsmaS2OffFaceQuadraticIntegrand m b c
        (fractionalGridLower mesh j) *
      normalizedMaynardS2OuterSquarefreeTupleShellMass
        (engelsmaOffFaceFinset m) alpha N
        (fun h => engelsmaMaynardRadius
          (alpha * fractionalGridLower mesh j h) N)
        (fun h => engelsmaMaynardRadius
          (alpha * fractionalGridUpper mesh j h) N)

set_option maxRecDepth 7000 in
set_option maxHeartbeats 800000 in
theorem tendsto_engelsmaS2OffFaceGridQuadraticStep
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple)
    {mesh : ℕ} (hmesh : 0 < mesh) (b c : ℕ) :
    Tendsto (fun N : ℕ =>
      engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c)
      atTop (nhds (
        ∑ j ∈ fractionalSimplexInnerGridIndex
            (engelsmaOffFaceFinset m) mesh,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j) *
            ∏ h : engelsmaOffFaceFinset m,
              (fractionalGridUpper mesh j h -
                fractionalGridLower mesh j h))) := by
  let H := engelsmaOffFaceFinset m
  let I := fractionalSimplexInnerGridIndex H mesh
  have hlim :=
    tendsto_finite_linear_combination_normalizedMaynardS2OuterSquarefreeTupleShellMass
      halpha I
      (fun j => engelsmaS2OffFaceQuadraticIntegrand m b c
        (fractionalGridLower mesh j))
      (fun j => fractionalGridLower mesh j)
      (fun j => fractionalGridUpper mesh j)
      (fun j hj h =>
        (fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.1)
      (fun j hj h =>
        (fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.2.1)
      (fun j hj h =>
        (fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.2.2)
  simpa [engelsmaS2OffFaceGridQuadraticStep, I, H] using hlim

end BoundedGaps.Maynard
