import BoundedGaps.Maynard.ConcreteS2CoordinateOneSupportReindex

noncomputable section

namespace BoundedGaps.Maynard

def engelsmaS2OffFaceGoodSupport
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    Finset (engelsmaOffFaceFinset m → ℕ) :=
  (maynardDivisorTupleSupport
      (engelsmaOffFaceFinset m) R (primorial D)).filter fun u =>
    1 < maynardS2CoordinateFiberEndpoint R
      (divisorTupleProduct (engelsmaOffFaceFinset m) u)

theorem mem_engelsmaS2OffFaceGoodSupport_iff
    {R D : ℕ} {m : BoundedGaps.engelsmaTuple}
    {u : engelsmaOffFaceFinset m → ℕ} :
    u ∈ engelsmaS2OffFaceGoodSupport R D m ↔
      u ∈ maynardDivisorTupleSupport
          (engelsmaOffFaceFinset m) R (primorial D) ∧
        1 < maynardS2CoordinateFiberEndpoint R
          (divisorTupleProduct (engelsmaOffFaceFinset m) u) := by
  exact Finset.mem_filter

set_option maxRecDepth 6000 in
theorem sum_engelsmaS2CoordinateFiberGoodSupport_eq_offFace
    {M : Type*} [AddCommMonoid M]
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple)
    (F : (BoundedGaps.engelsmaTuple → ℕ) → M) :
    (∑ r ∈ engelsmaS2CoordinateFiberGoodSupport R D m, F r) =
      ∑ u ∈ engelsmaS2OffFaceGoodSupport R D m,
        F (engelsmaOffFaceExtension m u) := by
  apply Finset.sum_bij (fun r _ => engelsmaOffFaceRestriction m r)
  · intro r hr
    have hrData := Finset.mem_filter.mp hr
    have hrm : r m = 1 := hrData.2.1
    apply mem_engelsmaS2OffFaceGoodSupport_iff.mpr
    have hext := engelsmaOffFaceExtension_restriction m r hrm
    exact (engelsmaOffFaceExtension_mem_goodSupport_iff R D m
      (engelsmaOffFaceRestriction m r)).mp (by simpa [hext] using hr)
  · intro r hr s hs hEq
    have hrm := (Finset.mem_filter.mp hr).2.1
    have hsm := (Finset.mem_filter.mp hs).2.1
    calc
      r = engelsmaOffFaceExtension m (engelsmaOffFaceRestriction m r) :=
        (engelsmaOffFaceExtension_restriction m r hrm).symm
      _ = engelsmaOffFaceExtension m (engelsmaOffFaceRestriction m s) := by
        rw [hEq]
      _ = s := engelsmaOffFaceExtension_restriction m s hsm
  · intro u hu
    let r := engelsmaOffFaceExtension m u
    have hr : r ∈ engelsmaS2CoordinateFiberGoodSupport R D m := by
      apply (engelsmaOffFaceExtension_mem_goodSupport_iff R D m u).mpr
      exact mem_engelsmaS2OffFaceGoodSupport_iff.mp hu
    refine ⟨r, hr, ?_⟩
    exact engelsmaOffFaceRestriction_extension m u
  · intro r hr
    have hrm := (Finset.mem_filter.mp hr).2.1
    rw [engelsmaOffFaceExtension_restriction m r hrm]

end BoundedGaps.Maynard
