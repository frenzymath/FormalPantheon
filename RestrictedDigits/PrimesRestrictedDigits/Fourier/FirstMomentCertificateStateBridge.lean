import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRows

/-!
# State-space bridge for exact first-moment rows

The checkers enumerate four-digit states by decimal value. This transports
their results to the tuple-state interface used by the transfer matrix.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Tuple-state form of a representative's natural subeigenvector. -/
def firstMomentStateVectorNumerator
    (a : Fin 5) (state : DigitWindowState 4) : Nat :=
  firstMomentVectorNumerator a (digitWindowStateFourEquiv.symm state)

/-- Tuple-window form of a representative's natural first-moment edge. -/
def firstMomentWindowPoweredNumerator
    (a : Fin 5) (window : DigitWindowState 5) : Nat :=
  firstMomentPoweredNumerator firstMomentCertificateDenominator
    (firstMomentRepresentativeDigit a) window

theorem firstMomentStateVectorNumerator_decimalDigitWindow
    (a : Fin 5) (index : Fin 10000) :
    firstMomentStateVectorNumerator a
        (decimalDigitWindow 4 index.val) =
      firstMomentVectorNumerator a index := by
  change firstMomentVectorNumerator a
    (digitWindowStateFourEquiv.symm (digitWindowStateFourEquiv index)) = _
  rw [Equiv.symm_apply_apply]

theorem firstMomentStateVectorNumerator_prefix_prepend
    (a : Fin 5) (first : Fin 10) (future : Fin 10000) :
    firstMomentStateVectorNumerator a
        (digitWindowPrefix (prependDigitWindow first
          (decimalDigitWindow 4 future.val))) =
      firstMomentVectorNumerator a
        (firstMomentIncomingPreviousIndex first future) := by
  rw [prefix_prependDigitWindow_decimalDigitWindow_four first future.isLt]
  change firstMomentVectorNumerator a
    (digitWindowStateFourEquiv.symm
      (digitWindowStateFourEquiv
        (firstMomentIncomingPreviousIndex first future))) = _
  rw [Equiv.symm_apply_apply]

theorem firstMomentWindowPoweredNumerator_prepend
    (a : Fin 5) (first : Fin 10) (future : Fin 10000) :
    firstMomentWindowPoweredNumerator a
        (prependDigitWindow first (decimalDigitWindow 4 future.val)) =
      firstMomentPairedPoweredNumerator firstMomentCertificateDenominator
        (firstMomentRepresentativeDigit a)
        (10000 * first.val + future.val) := by
  unfold firstMomentWindowPoweredNumerator
  rw [prependDigitWindow_decimalDigitWindow_four first future.isLt]
  rw [← firstMomentIndexedPoweredNumerator_eq_window
    firstMomentCertificateDenominator (firstMomentRepresentativeDigit a)
    (by omega)]
  rw [← firstMomentPairedPoweredNumerator_eq]

theorem firstMomentStateRows_of_indexedRows
    (a : Fin 5)
    (hrow : forall future : Fin 10000, firstMomentIndexedRow a future) :
    forall future : DigitWindowState 4,
      firstMomentCertificateGrowthDenominator *
          (∑ first : Fin 10,
            firstMomentWindowPoweredNumerator a
                (prependDigitWindow first future) *
              firstMomentStateVectorNumerator a
                (digitWindowPrefix (prependDigitWindow first future))) <=
        firstMomentCertificateDenominator *
          firstMomentCertificateGrowthNumerator *
            firstMomentStateVectorNumerator a future := by
  intro future
  let index := digitWindowStateFourEquiv.symm future
  have hfuture : decimalDigitWindow 4 index.val = future :=
    digitWindowStateFourEquiv.apply_symm_apply future
  rw [← hfuture]
  have h := hrow index
  rw [firstMomentIndexedRow_def] at h
  unfold firstMomentIndexedRowSum at h
  simp_rw [firstMomentStateVectorNumerator_prefix_prepend]
  rw [firstMomentStateVectorNumerator_decimalDigitWindow]
  simp_rw [firstMomentWindowPoweredNumerator_prepend]
  exact h

end PrimesRestrictedDigits
