import BoundedGaps.Maynard.ConcreteS2CoordinateOneTupleEquiv

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

set_option maxRecDepth 5000 in
theorem divisorTupleProduct_engelsmaOffFaceExtension_eq
    (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    divisorTupleProduct BoundedGaps.engelsmaTuple
        (engelsmaOffFaceExtension m u) =
      divisorTupleProduct (engelsmaOffFaceFinset m) u := by
  rw [divisorTupleProduct_eq_offCoordinateProduct m
    (engelsmaOffFaceExtension_at m u)]
  rw [maynardS2OffCoordinateProduct_eq_offFaceProduct]
  rw [engelsmaOffFaceRestriction_extension]
  rfl

set_option maxRecDepth 5000 in
theorem maynardS2OffCoordinateProduct_engelsmaOffFaceExtension_eq
    (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m
        (engelsmaOffFaceExtension m u) =
      divisorTupleProduct (engelsmaOffFaceFinset m) u := by
  rw [maynardS2OffCoordinateProduct_eq_offFaceProduct]
  rw [engelsmaOffFaceRestriction_extension]
  rfl

theorem isMaynardDivisorTuple_engelsmaOffFaceExtension_iff
    (R W : ℕ) (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R W
        (engelsmaOffFaceExtension m u) ↔
      IsMaynardDivisorTuple (engelsmaOffFaceFinset m) R W u := by
  unfold IsMaynardDivisorTuple
  rw [divisorTupleProduct_engelsmaOffFaceExtension_eq]

set_option maxRecDepth 5000 in
theorem engelsmaOffFaceExtension_mem_maynardDivisorTupleSupport_iff
    (R W : ℕ) (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    engelsmaOffFaceExtension m u ∈
        maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R W ↔
      u ∈ maynardDivisorTupleSupport (engelsmaOffFaceFinset m) R W := by
  rw [mem_maynardDivisorTupleSupport_iff,
    mem_maynardDivisorTupleSupport_iff]
  constructor
  · intro h
    have hu := (isMaynardDivisorTuple_engelsmaOffFaceExtension_iff
      R W m u).mp h.2
    exact ⟨hu.mem_maynardDivisorTupleBox, hu⟩
  · intro h
    have hfull := (isMaynardDivisorTuple_engelsmaOffFaceExtension_iff
      R W m u).mpr h.2
    exact ⟨hfull.mem_maynardDivisorTupleBox, hfull⟩

set_option maxRecDepth 5000 in
theorem engelsmaOffFaceExtension_mem_goodSupport_iff
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    engelsmaOffFaceExtension m u ∈
        engelsmaS2CoordinateFiberGoodSupport R D m ↔
      u ∈ maynardDivisorTupleSupport
          (engelsmaOffFaceFinset m) R (primorial D) ∧
        1 < maynardS2CoordinateFiberEndpoint R
          (divisorTupleProduct (engelsmaOffFaceFinset m) u) := by
  rw [engelsmaS2CoordinateFiberGoodSupport, Finset.mem_filter]
  rw [engelsmaOffFaceExtension_mem_maynardDivisorTupleSupport_iff]
  rw [maynardS2OffCoordinateProduct_engelsmaOffFaceExtension_eq]
  simp only [engelsmaOffFaceExtension_at, true_and]

end BoundedGaps.Maynard
