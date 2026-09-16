import PrimesRestrictedDigits.Fourier.Moment235CertificateRows

/-!
# Contiguous range assembly for fractional-moment certificate rows

Finite row checkers use small blocks for predictable kernel resource use. This
lemma joins adjacent checked intervals without simplifying the row predicate.
-/

namespace PrimesRestrictedDigits

theorem moment235IndexedRows_append
    (a : Fin 5) (start leftSize rightSize : Nat)
    (hbound : start + (leftSize + rightSize) <= 10000)
    (left : forall offset : Fin leftSize,
      moment235IndexedRow a ⟨start + offset.val, by omega⟩)
    (right : forall offset : Fin rightSize,
      moment235IndexedRow a
        ⟨start + leftSize + offset.val, by omega⟩) :
    forall offset : Fin (leftSize + rightSize),
      moment235IndexedRow a ⟨start + offset.val, by omega⟩ := by
  intro offset
  refine Fin.addCases (motive := fun offset : Fin (leftSize + rightSize) =>
    moment235IndexedRow a ⟨start + offset.val, by omega⟩) ?_ ?_ offset
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
