import PrimesRestrictedDigits.Fourier.GrowthThresholds
import PrimesRestrictedDigits.Fourier.Moment235CertificateStateBridge
import PrimesRestrictedDigits.Fourier.PositiveMomentSymmetry
import PrimesRestrictedDigits.Fourier.ScaledNaturalCertificate

/-!
# Fractional-moment theorem from exact indexed rows

The five finite row families imply the uniform complete-grid moment estimate.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 10.2, pp. 170--173.
-/

set_option maxRecDepth 1000000

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem moment235StateVectorScale_le
    (a : Fin 5) (state : DigitWindowState 4) :
    moment235VectorScale a <= moment235StateVectorNumerator a state := by
  exact moment235VectorScale_le a (digitWindowStateFourEquiv.symm state)

theorem moment235StateVector_zero_eq_scale (a : Fin 5) :
    moment235StateVectorNumerator a (fun _ : Fin 4 => 0) =
      moment235VectorScale a := by
  have hzero : decimalDigitWindow 4 0 = (fun _ : Fin 4 => 0) := by
    funext index
    apply Fin.ext
    simp [decimalDigitWindow]
  rw [← hzero]
  calc
    moment235StateVectorNumerator a (decimalDigitWindow 4 0) =
        moment235VectorNumerator a 0 :=
      moment235StateVectorNumerator_decimalDigitWindow a 0
    _ = moment235VectorScale a := moment235Vector_zero_eq_scale' a

theorem positiveMomentFrequencySum_le_moment235_representative
    (hrows : forall a : Fin 5, forall future : Fin 10000,
      moment235IndexedRow a future)
    (a : Fin 5) (length : Nat) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude
          (moment235RepresentativeDigit a) length frequency.val ^
        (235 / 154 : Real)) <=
      (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) := by
  have hD : 0 < moment235CertificateDenominator := by
    norm_num [moment235CertificateDenominator]
  have hS : 0 < moment235VectorScale a :=
    moment235VectorScale_pos' a
  have hQ : 0 < moment235CertificateGrowthDenominator := by
    norm_num [moment235CertificateGrowthDenominator]
  have hweight : forall window : DigitWindowState 5,
      poweredWindowMajorantWeight (moment235RepresentativeDigit a) 4
          (235 / 154 : Real) window <=
        naturalWindowWeight moment235CertificateDenominator
          (moment235WindowPoweredNumerator a) window := by
    intro window
    change poweredWindowMajorantWeight (moment235RepresentativeDigit a) 4
        (235 / 154 : Real) window <=
      naturalWindowWeight moment235CertificateDenominator
        (moment235PoweredNumerator moment235CertificateDenominator
          (moment235RepresentativeDigit a)) window
    exact poweredWindowMajorant_four_le_moment235NaturalWeight
      moment235CertificateDenominator hD (moment235RepresentativeDigit a)
      window
  have hcertificate := positiveMomentFrequencySum_le_naturalCertificate
    (moment235RepresentativeDigit a) length 4 (235 / 154 : Real)
    (by norm_num) moment235CertificateDenominator (moment235VectorScale a)
    moment235CertificateGrowthNumerator
    moment235CertificateGrowthDenominator hD hS hQ
    (moment235WindowPoweredNumerator a)
    (moment235StateVectorNumerator a) hweight
    (moment235StateVectorScale_le a)
    (moment235StateRows_of_indexedRows a (hrows a))
  have hterminal :
      naturalStateVector (moment235VectorScale a)
          (moment235StateVectorNumerator a) (fun _ : Fin 4 => 0) = 1 := by
    rw [naturalStateVector, moment235StateVector_zero_eq_scale]
    exact div_self (by exact_mod_cast (ne_of_gt hS))
  have hgrowth :
      naturalRatio moment235CertificateGrowthNumerator
          moment235CertificateGrowthDenominator = secondGrowthConstant := by
    rfl
  have hpow : secondGrowthConstant ^ length <=
      ((10 : Real) ^ (59 / 433 : Real)) ^ length :=
    pow_le_pow_left₀ secondGrowthConstant_nonneg
      secondGrowthConstant_lt_ten_rpow.le length
  have hscale : ((10 : Real) ^ (59 / 433 : Real)) ^ length =
      (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) := by
    calc
      ((10 : Real) ^ (59 / 433 : Real)) ^ length =
          ((10 : Real) ^ (59 / 433 : Real)) ^ (length : Real) := by
            rw [Real.rpow_natCast]
      _ = (10 : Real) ^ ((59 / 433 : Real) * (length : Real)) := by
            rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 10)]
      _ = ((10 : Real) ^ (length : Real)) ^ (59 / 433 : Real) := by
            rw [mul_comm, Real.rpow_mul (by norm_num : (0 : Real) <= 10)]
      _ = (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) := by
            norm_num [Nat.cast_pow, Real.rpow_natCast]
  calc
    (∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude
            (moment235RepresentativeDigit a) length frequency.val ^
          (235 / 154 : Real)) <=
        naturalRatio moment235CertificateGrowthNumerator
              moment235CertificateGrowthDenominator ^ length *
          naturalStateVector (moment235VectorScale a)
            (moment235StateVectorNumerator a) (fun _ : Fin 4 => 0) :=
      hcertificate
    _ = secondGrowthConstant ^ length := by
      rw [hterminal, hgrowth, mul_one]
    _ <= ((10 : Real) ^ (59 / 433 : Real)) ^ length := hpow
    _ = (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) := hscale

theorem positiveMomentFrequencySum_le_moment235_of_indexedRows
    (hrows : forall a : Fin 5, forall future : Fin 10000,
      moment235IndexedRow a future)
    (a : Fin 10) (length : Nat) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^
        (235 / 154 : Real)) <=
      (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) := by
  apply positiveMomentFrequencySum_le_of_smallDigits length
    (235 / 154 : Real)
    (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real))
  intro small hsmall
  let representative : Fin 5 := ⟨small.val, by omega⟩
  have heq : moment235RepresentativeDigit representative = small := by
    apply Fin.ext
    rfl
  simpa only [heq] using
    positiveMomentFrequencySum_le_moment235_representative
      hrows representative length

/-- The zero-length boundary case of the exact fractional-moment estimate. -/
theorem positiveMomentFrequencySum_moment235_length_zero (a : Fin 10) :
    (∑ frequency : Fin (10 ^ 0),
      normalizedPaddedDigitFourierMagnitude a 0 frequency.val ^
        (235 / 154 : Real)) =
      (((10 ^ 0 : Nat) : Real) ^ (59 / 433 : Real)) := by
  norm_num [normalizedPaddedDigitFourierMagnitude_zero_frequency]

end PrimesRestrictedDigits
