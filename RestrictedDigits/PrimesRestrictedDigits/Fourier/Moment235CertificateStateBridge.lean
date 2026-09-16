import PrimesRestrictedDigits.Fourier.Moment235CertificateRows

/-!
# State-space bridge for the exact fractional-moment certificate

The kernel checkers enumerate width-four future states by their decimal value.
This module transports those rows to the tuple-state interface consumed by the
scaled natural certificate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

def moment235StateVectorNumerator
    (a : Fin 5) (state : DigitWindowState 4) : Nat :=
  moment235VectorNumerator a (digitWindowStateFourEquiv.symm state)

def moment235WindowPoweredNumerator
    (a : Fin 5) (window : DigitWindowState 5) : Nat :=
  moment235PoweredNumerator moment235CertificateDenominator
    (moment235RepresentativeDigit a) window

theorem moment235StateVectorNumerator_decimalDigitWindow
    (a : Fin 5) (index : Fin 10000) :
    moment235StateVectorNumerator a
        (decimalDigitWindow 4 index.val) =
      moment235VectorNumerator a index := by
  change moment235VectorNumerator a
    (digitWindowStateFourEquiv.symm (digitWindowStateFourEquiv index)) = _
  rw [Equiv.symm_apply_apply]

theorem moment235StateVectorNumerator_prefix_prepend
    (a : Fin 5) (first : Fin 10) (future : Fin 10000) :
    moment235StateVectorNumerator a
        (digitWindowPrefix (prependDigitWindow first
          (decimalDigitWindow 4 future.val))) =
      moment235VectorNumerator a
        (moment235IncomingPreviousIndex first future) := by
  rw [prefix_prependDigitWindow_decimalDigitWindow_four first future.isLt]
  change moment235VectorNumerator a
    (digitWindowStateFourEquiv.symm
      (digitWindowStateFourEquiv
        (moment235IncomingPreviousIndex first future))) = _
  rw [Equiv.symm_apply_apply]

theorem moment235WindowPoweredNumerator_prepend
    (a : Fin 5) (first : Fin 10) (future : Fin 10000) :
    moment235WindowPoweredNumerator a
        (prependDigitWindow first (decimalDigitWindow 4 future.val)) =
      moment235PairedPoweredNumerator moment235CertificateDenominator
        (moment235RepresentativeDigit a)
        (10000 * first.val + future.val) := by
  unfold moment235WindowPoweredNumerator
  rw [prependDigitWindow_decimalDigitWindow_four first future.isLt]
  rw [← moment235IndexedPoweredNumerator_eq_window
    moment235CertificateDenominator (moment235RepresentativeDigit a)
    (by omega)]
  rw [← moment235PairedPoweredNumerator_eq]

theorem moment235StateRows_of_indexedRows
    (a : Fin 5)
    (hrow : forall future : Fin 10000, moment235IndexedRow a future) :
    forall future : DigitWindowState 4,
      moment235CertificateGrowthDenominator *
          (∑ first : Fin 10,
            moment235WindowPoweredNumerator a
                (prependDigitWindow first future) *
              moment235StateVectorNumerator a
                (digitWindowPrefix (prependDigitWindow first future))) <=
        moment235CertificateDenominator *
          moment235CertificateGrowthNumerator *
            moment235StateVectorNumerator a future := by
  intro future
  let index := digitWindowStateFourEquiv.symm future
  have hfuture : decimalDigitWindow 4 index.val = future :=
    digitWindowStateFourEquiv.apply_symm_apply future
  rw [← hfuture]
  have h := hrow index
  rw [moment235IndexedRow_def] at h
  unfold moment235IndexedRowSum at h
  simp_rw [moment235StateVectorNumerator_prefix_prepend]
  rw [moment235StateVectorNumerator_decimalDigitWindow]
  simp_rw [moment235WindowPoweredNumerator_prepend]
  exact h

end PrimesRestrictedDigits
