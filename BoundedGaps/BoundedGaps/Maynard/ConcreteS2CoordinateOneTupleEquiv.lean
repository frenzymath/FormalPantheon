import BoundedGaps.Maynard.ConcreteS2OffFaceProduct

noncomputable section

namespace BoundedGaps.Maynard

noncomputable def engelsmaOffFaceExtension
    (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    BoundedGaps.engelsmaTuple → ℕ :=
  fun h => if hh : h = m then 1 else
    u ⟨h.1, Finset.mem_erase.mpr ⟨by
      intro hval
      exact hh (Subtype.ext hval), h.2⟩⟩

@[simp] theorem engelsmaOffFaceExtension_at
    (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    engelsmaOffFaceExtension m u m = 1 := by
  simp [engelsmaOffFaceExtension]

theorem engelsmaOffFaceExtension_off
    (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ)
    (h : BoundedGaps.engelsmaTuple) (hh : h ≠ m) :
    engelsmaOffFaceExtension m u h =
      u ⟨h.1, Finset.mem_erase.mpr ⟨by
        intro hval
        exact hh (Subtype.ext hval), h.2⟩⟩ := by
  unfold engelsmaOffFaceExtension
  rw [dif_neg hh]

set_option maxRecDepth 4000 in
@[simp] theorem engelsmaOffFaceRestriction_extension
    (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    engelsmaOffFaceRestriction m (engelsmaOffFaceExtension m u) = u := by
  funext h
  unfold engelsmaOffFaceRestriction
  have hh :
      (⟨h.1, (Finset.mem_erase.mp h.2).2⟩ : BoundedGaps.engelsmaTuple) ≠ m := by
    intro hEq
    exact (Finset.mem_erase.mp h.2).1
      (congrArg (fun z : BoundedGaps.engelsmaTuple => z.1) hEq)
  rw [engelsmaOffFaceExtension_off _ _ _ hh]

set_option maxRecDepth 4000 in
theorem engelsmaOffFaceExtension_restriction
    (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) (hrm : r m = 1) :
    engelsmaOffFaceExtension m (engelsmaOffFaceRestriction m r) = r := by
  funext h
  by_cases hh : h = m
  · subst h
    simp [hrm]
  · rw [engelsmaOffFaceExtension_off m _ h hh]
    rfl

noncomputable def engelsmaCoordinateOneTupleEquiv
    (m : BoundedGaps.engelsmaTuple) :
    (engelsmaOffFaceFinset m → ℕ) ≃
      {r : BoundedGaps.engelsmaTuple → ℕ // r m = 1} where
  toFun u := ⟨engelsmaOffFaceExtension m u,
    engelsmaOffFaceExtension_at m u⟩
  invFun r := engelsmaOffFaceRestriction m r.1
  left_inv u := engelsmaOffFaceRestriction_extension m u
  right_inv r := by
    apply Subtype.ext
    exact engelsmaOffFaceExtension_restriction m r.1 r.2

@[simp] theorem engelsmaCoordinateOneTupleEquiv_apply_val
    (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    (engelsmaCoordinateOneTupleEquiv m u).1 =
      engelsmaOffFaceExtension m u := rfl

end BoundedGaps.Maynard
