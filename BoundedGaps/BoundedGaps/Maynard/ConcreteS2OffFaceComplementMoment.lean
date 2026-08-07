import BoundedGaps.Maynard.ConcreteS2GoodSupportSumReindex
import BoundedGaps.Maynard.ConcreteS2GoodComplementOuterMoment
import BoundedGaps.Maynard.ConcreteS2ComplementFaceIdentification

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory
open scoped BigOperators

noncomputable def engelsmaS2OffFaceGoodComplementOuterMoment
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ u ∈ engelsmaS2OffFaceGoodSupport R D m,
    (∏ h : engelsmaOffFaceFinset m,
      maynardS2OuterSquarefreeAF (primorial D) (u h)) *
      (Real.log R *
        engelsmaS2CoordinateFiberFaceIntegral R m
          (engelsmaOffFaceExtension m u)) ^ 2

set_option maxRecDepth 7000 in
theorem engelsmaS2CoordinateFiberGoodComplementOuterMoment_eq_offFace
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple) (hR : 1 < R) :
    engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m =
      engelsmaS2OffFaceGoodComplementOuterMoment R D m := by
  unfold engelsmaS2CoordinateFiberGoodComplementOuterMoment
    engelsmaS2OffFaceGoodComplementOuterMoment
  rw [sum_engelsmaS2CoordinateFiberGoodSupport_eq_offFace]
  apply Finset.sum_congr rfl
  intro u hu
  let r := engelsmaOffFaceExtension m u
  have hrGood : r ∈ engelsmaS2CoordinateFiberGoodSupport R D m := by
    apply (engelsmaOffFaceExtension_mem_goodSupport_iff R D m u).mpr
    exact mem_engelsmaS2OffFaceGoodSupport_iff.mp hu
  have hrMem := (Finset.mem_filter.mp hrGood).1
  have hr := isMaynardDivisorTuple_of_mem_support hrMem
  have hweight :=
    maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_offFaceProduct m r hr
  have hrestrict : engelsmaOffFaceRestriction m r = u :=
    engelsmaOffFaceRestriction_extension m u
  rw [hweight, hrestrict]
  have hface :=
    engelsmaS2CoordinateFiber_complementIntegral_eq_faceIntegral
      m hr hR (engelsmaOffFaceExtension_at m u)
  rw [hface]

end BoundedGaps.Maynard
