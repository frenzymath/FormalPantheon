import BoundedGaps.Maynard.ConcreteS2ComplementFaceIdentification

noncomputable section

namespace BoundedGaps.Maynard

def engelsmaOffFaceFinset (m : BoundedGaps.engelsmaTuple) : Finset ℕ :=
  BoundedGaps.engelsmaTuple.erase m.1

set_option maxRecDepth 4000 in
noncomputable def engelsmaOffFaceToFaceIndex
    (m : BoundedGaps.engelsmaTuple) (h : engelsmaOffFaceFinset m) :
    maynardFaceIndex 105 (engelsmaIndexEquiv m) :=
  ⟨engelsmaIndexEquiv
      (⟨h.1, (Finset.mem_erase.mp h.2).2⟩ : BoundedGaps.engelsmaTuple), by
    intro heq
    apply (Finset.mem_erase.mp h.2).1
    have hfull :
        (⟨h.1, (Finset.mem_erase.mp h.2).2⟩ : BoundedGaps.engelsmaTuple) = m :=
      engelsmaIndexEquiv.injective heq
    exact congrArg Subtype.val hfull⟩

set_option maxRecDepth 4000 in
theorem engelsmaOffFaceToFaceIndex_injective
    (m : BoundedGaps.engelsmaTuple) :
    Function.Injective (engelsmaOffFaceToFaceIndex m) := by
  intro h k hEq
  apply Subtype.ext
  have hval := congrArg Subtype.val hEq
  have hfull := engelsmaIndexEquiv.injective hval
  exact congrArg (fun z : BoundedGaps.engelsmaTuple => z.1) hfull

set_option maxRecDepth 4000 in
theorem engelsmaOffFaceToFaceIndex_surjective
    (m : BoundedGaps.engelsmaTuple) :
    Function.Surjective (engelsmaOffFaceToFaceIndex m) := by
  intro j
  let hfull : BoundedGaps.engelsmaTuple :=
    engelsmaIndexEquiv.symm j.1
  have hne : hfull.1 ≠ m.1 := by
    intro hval
    apply j.2
    calc
      j.1 = engelsmaIndexEquiv hfull :=
        (engelsmaIndexEquiv.apply_symm_apply j.1).symm
      _ = engelsmaIndexEquiv m := by
        congr 1
        exact Subtype.ext hval
  let h : engelsmaOffFaceFinset m :=
    ⟨hfull.1, Finset.mem_erase.mpr ⟨hne, hfull.2⟩⟩
  refine ⟨h, ?_⟩
  apply Subtype.ext
  simp [engelsmaOffFaceToFaceIndex, h, hfull]

noncomputable def engelsmaOffFaceIndexEquiv (m : BoundedGaps.engelsmaTuple) :
    engelsmaOffFaceFinset m ≃
      maynardFaceIndex 105 (engelsmaIndexEquiv m) :=
  Equiv.ofBijective (engelsmaOffFaceToFaceIndex m)
    ⟨engelsmaOffFaceToFaceIndex_injective m,
      engelsmaOffFaceToFaceIndex_surjective m⟩

@[simp] theorem engelsmaOffFaceIndexEquiv_apply
    (m : BoundedGaps.engelsmaTuple) (h : engelsmaOffFaceFinset m) :
    engelsmaOffFaceIndexEquiv m h = engelsmaOffFaceToFaceIndex m h := rfl

end BoundedGaps.Maynard
