import BoundedGaps.Maynard.ConcreteS2ComplementFaceIdentification
import BoundedGaps.Maynard.SmallKFaceMoments

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory
open scoped BigOperators

set_option maxRecDepth 5000 in
theorem engelsmaS2CoordinateFiberFaceIntegral_sq_eq_pairSum
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) :
    engelsmaS2CoordinateFiberFaceIntegral R m r ^ 2 =
      ∑ i : Fin 42, ∑ j : Fin 42,
        smallKRealFacePairTerm (engelsmaIndexEquiv m) i j
          (engelsmaS2OffCoordinateLogFacePoint R m r) := by
  let mi := engelsmaIndexEquiv m
  let t := engelsmaS2OffCoordinateLogFacePoint R m r
  have hexp : engelsmaS2CoordinateFiberFaceIntegral R m r =
      ∑ i : Fin 42, smallKRealFaceInnerTerm mi i t := by
    unfold engelsmaS2CoordinateFiberFaceIntegral
    exact smallKRealFaceInner_expansion mi t
  rw [hexp]
  simp only [pow_two, Finset.sum_mul_sum]
  rfl

set_option maxRecDepth 7000 in
theorem engelsmaS2CoordinateFiberFaceIntegral_sq_eq_faceQuadraticSum
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R) (hrm : r m = 1) :
    engelsmaS2CoordinateFiberFaceIntegral R m r ^ 2 =
      ∑ i : Fin 42, ∑ j : Fin 42,
        ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            ((smallKCoefficient i * smallKCoefficient j *
              smallKFaceInnerCoefficient i cp *
              smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
              faceQuadraticIntegrand (engelsmaIndexEquiv m)
                (smallKFaceInnerExponent i cp +
                  smallKFaceInnerExponent j dp) (cp + dp)
                (engelsmaS2OffCoordinateLogFacePoint R m r) := by
  rw [engelsmaS2CoordinateFiberFaceIntegral_sq_eq_pairSum R m r]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact smallKRealFacePairTerm_formula (engelsmaIndexEquiv m) i j _
    (engelsmaS2OffCoordinateLogFacePoint_mem_faceSimplex m hr hR hrm)

end BoundedGaps.Maynard
