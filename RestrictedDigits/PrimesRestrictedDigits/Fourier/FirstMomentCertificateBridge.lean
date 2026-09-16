import PrimesRestrictedDigits.Fourier.FirstMomentCertificateStateBridge
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateBounds
import PrimesRestrictedDigits.Fourier.GrowthThresholds
import PrimesRestrictedDigits.Fourier.MatrixUpperBound
import PrimesRestrictedDigits.Fourier.PositiveMomentSymmetry
import PrimesRestrictedDigits.Fourier.ScaledNaturalCertificate

/-!
# First-moment path bound from exact indexed rows

The indexed row bounds imply the transfer-matrix path estimate.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 10.3, pp. 173--175.
-/

set_option maxRecDepth 1000000

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

theorem firstMomentStateVectorScale_le
    (a : Fin 5) (state : DigitWindowState 4) :
    firstMomentVectorScale a <= firstMomentStateVectorNumerator a state := by
  exact firstMomentVectorScale_le a (digitWindowStateFourEquiv.symm state)

theorem firstMomentStateVectorNumerator_le_two_mul_scale
    (a : Fin 5) (state : DigitWindowState 4) :
    firstMomentStateVectorNumerator a state <=
      2 * firstMomentVectorScale a := by
  exact firstMomentVectorNumerator_le_two_mul_scale a
    (digitWindowStateFourEquiv.symm state)

private theorem digitWordPathSum_firstMoment_representative_le
    (hrows : forall a : Fin 5, forall future : Fin 10000,
      firstMomentIndexedRow a future)
    (a : Fin 5) (length : Nat) (future : DigitWindowState 4) :
    digitWordPathSum
        (poweredWindowMajorantWeight (firstMomentRepresentativeDigit a) 4 1)
        length future <=
      2 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
  let exactWeight : DigitWindowState 5 → Real :=
    poweredWindowMajorantWeight (firstMomentRepresentativeDigit a) 4 1
  let upperWeight : DigitWindowState 5 → Real :=
    naturalWindowWeight firstMomentCertificateDenominator
      (firstMomentWindowPoweredNumerator a)
  let exactMatrix : Matrix (DigitWindowState 4) (DigitWindowState 4) Real :=
    digitWindowTransitionMatrix 4 exactWeight
  let upperMatrix : Matrix (DigitWindowState 4) (DigitWindowState 4) Real :=
    digitWindowTransitionMatrix 4 upperWeight
  let stateVector : DigitWindowState 4 → Real :=
    naturalStateVector (firstMomentVectorScale a)
      (firstMomentStateVectorNumerator a)
  let rho : Real := naturalRatio firstMomentCertificateGrowthNumerator
    firstMomentCertificateGrowthDenominator
  have hD : 0 < firstMomentCertificateDenominator := by
    norm_num [firstMomentCertificateDenominator]
  have hS : 0 < firstMomentVectorScale a := firstMomentVectorScale_pos a
  have hQ : 0 < firstMomentCertificateGrowthDenominator := by
    norm_num [firstMomentCertificateGrowthDenominator]
  have hweight : forall window : DigitWindowState 5,
      exactWeight window <= upperWeight window := by
    intro window
    exact poweredWindowMajorant_four_one_le_firstMomentNaturalWeight
      firstMomentCertificateDenominator hD
      (firstMomentRepresentativeDigit a) window
  have hexactNonneg : forall row column, 0 <= exactMatrix row column := by
    intro row column
    apply digitWindowTransitionMatrix_nonneg
    intro window
    exact Real.rpow_nonneg
      (oneSidedWindowMajorant_nonneg
        (firstMomentRepresentativeDigit a) 4 window) 1
  have hmatrix : forall row column,
      exactMatrix row column <= upperMatrix row column :=
    digitWindowTransitionMatrix_mono hweight
  have hvector : forall state, 1 <= stateVector state :=
    naturalStateVector_one_le (firstMomentVectorScale a) hS
      (firstMomentStateVectorNumerator a) (firstMomentStateVectorScale_le a)
  have hrho : 0 <= rho := by
    unfold rho naturalRatio
    positivity
  have hsub : (upperMatrix *ᵥ stateVector) <= rho • stateVector := by
    exact naturalWindowTransition_mulVec_le
      firstMomentCertificateDenominator (firstMomentVectorScale a)
      firstMomentCertificateGrowthNumerator
      firstMomentCertificateGrowthDenominator hD hS hQ
      (firstMomentWindowPoweredNumerator a)
      (firstMomentStateVectorNumerator a)
      (firstMomentStateRows_of_indexedRows a (hrows a))
  have hstateVector : stateVector future <= 2 := by
    unfold stateVector naturalStateVector
    rw [div_le_iff₀ (by exact_mod_cast hS)]
    exact_mod_cast firstMomentStateVectorNumerator_le_two_mul_scale a future
  have hpow : rho ^ length <=
      ((10 : Real) ^ (27 / 77 : Real)) ^ length := by
    apply pow_le_pow_left₀ hrho
    change firstGrowthConstant <= (10 : Real) ^ (27 / 77 : Real)
    exact firstGrowthConstant_lt_ten_rpow.le
  have hscale : ((10 : Real) ^ (27 / 77 : Real)) ^ length =
      (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
    calc
      ((10 : Real) ^ (27 / 77 : Real)) ^ length =
          ((10 : Real) ^ (27 / 77 : Real)) ^ (length : Real) := by
            rw [Real.rpow_natCast]
      _ = (10 : Real) ^ ((27 / 77 : Real) * (length : Real)) := by
            rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 10)]
      _ = ((10 : Real) ^ (length : Real)) ^ (27 / 77 : Real) := by
            rw [mul_comm, Real.rpow_mul (by norm_num : (0 : Real) <= 10)]
      _ = (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
            norm_num [Nat.cast_pow, Real.rpow_natCast]
  calc
    digitWordPathSum
        (poweredWindowMajorantWeight (firstMomentRepresentativeDigit a) 4 1)
        length future = matrixRowPathSum exactMatrix length future :=
      digitWordPathSum_apply_eq_matrixRowPathSum exactWeight length future
    _ = ∑ previous, (exactMatrix ^ length) future previous :=
      matrixRowPathSum_eq_rowSum exactMatrix length future
    _ <= rho ^ length * stateVector future :=
      rowSum_pow_le_of_entrywise_upper_subEigen
        hexactNonneg hmatrix hvector hrho hsub length future
    _ <= rho ^ length * 2 :=
      mul_le_mul_of_nonneg_left hstateVector (pow_nonneg hrho length)
    _ <= ((10 : Real) ^ (27 / 77 : Real)) ^ length * 2 :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = 2 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
      rw [hscale]
      ring

private theorem digitWordPathSum_firstMoment_rev
    (digit : Fin 10) (length : Nat) (future : DigitWindowState 4) :
    digitWordPathSum
        (poweredWindowMajorantWeight digit.rev 4 1) length future =
      digitWordPathSum
        (poweredWindowMajorantWeight digit 4 1) length future := by
  induction length generalizing future with
  | zero => rfl
  | succ length ih =>
      rw [digitWordPathSum_succ_apply, digitWordPathSum_succ_apply]
      apply Finset.sum_congr rfl
      intro first hfirst
      rw [poweredWindowMajorantWeight_rev, ih]

theorem digitWordPathSum_firstMoment_le_of_indexedRows
    (hrows : forall a : Fin 5, forall future : Fin 10000,
      firstMomentIndexedRow a future)
    (digit : Fin 10) (length : Nat) (future : DigitWindowState 4) :
    digitWordPathSum
        (poweredWindowMajorantWeight digit 4 1)
        length future <=
      2 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
  by_cases hdigit : digit.val <= 4
  · let representative : Fin 5 := ⟨digit.val, by omega⟩
    have heq : firstMomentRepresentativeDigit representative = digit := by
      apply Fin.ext
      rfl
    simpa only [heq] using
      digitWordPathSum_firstMoment_representative_le
        hrows representative length future
  · have hrev : digit.rev.val <= 4 := by
      rw [Fin.val_rev]
      omega
    let representative : Fin 5 := ⟨digit.rev.val, by omega⟩
    have heq : firstMomentRepresentativeDigit representative = digit.rev := by
      apply Fin.ext
      rfl
    have h := digitWordPathSum_firstMoment_representative_le
      hrows representative length future
    rw [heq, digitWordPathSum_firstMoment_rev] at h
    exact h

theorem firstMomentFrequencySum_le_of_indexedRows
    (hrows : forall a : Fin 5, forall future : Fin 10000,
      firstMomentIndexedRow a future)
    (digit : Fin 10) (length : Nat) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude
        digit length frequency.val) <=
      2 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
  calc
    (∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude digit length frequency.val) =
        ∑ frequency : Fin (10 ^ length),
          normalizedPaddedDigitFourierMagnitude
            digit length frequency.val ^ (1 : Real) := by
      simp only [Real.rpow_one]
    _ <= digitWordPathSum
          (poweredWindowMajorantWeight digit 4 1)
          length (fun _ : Fin 4 => 0) :=
      positiveMomentFrequencySum_le_digitWordPathSum
        digit length 4 1 (by norm_num)
    _ <= 2 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) :=
      digitWordPathSum_firstMoment_le_of_indexedRows
        hrows digit length (fun _ : Fin 4 => 0)

end PrimesRestrictedDigits
