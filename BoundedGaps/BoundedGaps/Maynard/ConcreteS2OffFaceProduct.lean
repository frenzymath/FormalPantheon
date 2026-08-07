import BoundedGaps.Maynard.ConcreteS2OffFaceIndexEquiv
import BoundedGaps.Maynard.MaynardS2OuterFaceBox

noncomputable section

namespace BoundedGaps.Maynard

set_option maxRecDepth 4000 in
noncomputable def engelsmaEraseToOffFace
    (m : BoundedGaps.engelsmaTuple)
    (h : (Finset.univ.erase m : Finset BoundedGaps.engelsmaTuple)) :
    engelsmaOffFaceFinset m :=
  ⟨h.1.1, Finset.mem_erase.mpr ⟨by
    intro hval
    exact (Finset.mem_erase.mp h.2).1 (Subtype.ext hval), h.1.2⟩⟩

set_option maxRecDepth 4000 in
noncomputable def engelsmaEraseToOffFaceEquiv
    (m : BoundedGaps.engelsmaTuple) :
    (Finset.univ.erase m : Finset BoundedGaps.engelsmaTuple) ≃
      engelsmaOffFaceFinset m :=
  Equiv.ofBijective
    (engelsmaEraseToOffFace m)
    (by
      constructor
      · intro h k hEq
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : engelsmaOffFaceFinset m => z.1) hEq
      · intro h
        let full : BoundedGaps.engelsmaTuple :=
          ⟨h.1, (Finset.mem_erase.mp h.2).2⟩
        have hne : full ≠ m := by
          intro hEq
          exact (Finset.mem_erase.mp h.2).1 (congrArg Subtype.val hEq)
        let k : (Finset.univ.erase m : Finset BoundedGaps.engelsmaTuple) :=
          ⟨full, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ full⟩⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext
        rfl)

noncomputable def engelsmaOffFaceRestriction
    (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) :
    engelsmaOffFaceFinset m → ℕ :=
  fun h => r ⟨h.1, (Finset.mem_erase.mp h.2).2⟩

set_option maxRecDepth 5000 in
theorem prod_engelsmaTuple_erase_eq_offFaceProduct
    {M : Type*} [CommMonoid M]
    (m : BoundedGaps.engelsmaTuple)
    (f : BoundedGaps.engelsmaTuple → M) :
    (∏ h ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m, f h) =
      ∏ h : engelsmaOffFaceFinset m,
        f ⟨h.1, (Finset.mem_erase.mp h.2).2⟩ := by
  rw [← Finset.prod_coe_sort]
  apply Fintype.prod_equiv (engelsmaEraseToOffFaceEquiv m)
  intro h
  rfl

set_option maxRecDepth 5000 in
theorem maynardS2OffCoordinateProduct_eq_offFaceProduct
    (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) :
    maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r =
      ∏ h : engelsmaOffFaceFinset m,
        engelsmaOffFaceRestriction m r h := by
  unfold maynardS2OffCoordinateProduct
  exact prod_engelsmaTuple_erase_eq_offFaceProduct m r

theorem engelsmaS2OffCoordinateLogFacePoint_reindex
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ)
    (h : engelsmaOffFaceFinset m) :
    engelsmaS2OffCoordinateLogFacePoint R m r
        (engelsmaOffFaceIndexEquiv m h) =
      Real.log (engelsmaOffFaceRestriction m r h) / Real.log R := by
  rw [engelsmaOffFaceIndexEquiv_apply]
  unfold engelsmaS2OffCoordinateLogFacePoint
    engelsmaOffFaceToFaceIndex engelsmaOffFaceRestriction
  rw [engelsmaIndexEquiv.symm_apply_apply]

set_option maxRecDepth 5000 in
theorem maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_offFaceProduct
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ)
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) :
    maynardS2OuterSquarefreeAF (primorial D)
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) =
      ∏ h : engelsmaOffFaceFinset m,
        maynardS2OuterSquarefreeAF (primorial D)
          (engelsmaOffFaceRestriction m r h) := by
  rw [maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_prod m r hr]
  exact prod_engelsmaTuple_erase_eq_offFaceProduct m
    (fun h => maynardS2OuterSquarefreeAF (primorial D) (r h))

end BoundedGaps.Maynard
