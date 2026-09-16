import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRows

/-! First-moment row bounds on contiguous ranges. -/

namespace PrimesRestrictedDigits

theorem firstMomentIndexedRows_append
    (a : Fin 5) (start leftSize rightSize : Nat)
    (hbound : start + (leftSize + rightSize) <= 10000)
    (left : forall offset : Fin leftSize,
      firstMomentIndexedRow a ⟨start + offset.val, by omega⟩)
    (right : forall offset : Fin rightSize,
      firstMomentIndexedRow a
        ⟨start + leftSize + offset.val, by omega⟩) :
    forall offset : Fin (leftSize + rightSize),
      firstMomentIndexedRow a ⟨start + offset.val, by omega⟩ := by
  intro offset
  refine Fin.addCases (motive := fun offset : Fin (leftSize + rightSize) =>
    firstMomentIndexedRow a ⟨start + offset.val, by omega⟩) ?_ ?_ offset
  · intro leftOffset
    exact left leftOffset
  · intro rightOffset
    have hindex :
        (⟨start + (Fin.natAdd leftSize rightOffset).val,
            by omega⟩ : Fin 10000) =
          ⟨start + leftSize + rightOffset.val, by omega⟩ := by
      apply Fin.ext
      simp only [ Fin.val_natAdd]
      omega
    rw [hindex]
    exact right rightOffset

end PrimesRestrictedDigits
