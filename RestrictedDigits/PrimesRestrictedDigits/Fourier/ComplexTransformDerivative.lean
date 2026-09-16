import PrimesRestrictedDigits.Fourier.ContinuousTransformPeriodicity
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Derivative of the normalized complex digit transform

The magnitude of a differentiable complex transform need not be differentiable at its zeros.
This module differentiates the normalized source sum instead and controls its variation by a
nonnegative prefix envelope.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 10.5, pp. 175--178.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The derivative of the normalized one-digit complex factor. -/
noncomputable def normalizedDigitFourierFactorDerivativeAt
    (digit : Fin 10) (theta : Real) : Complex :=
  (∑ d ∈ allowedDecimalDigits digit,
    digitPhaseAt theta d *
      (((2 * Real.pi * (d : Real) : Real) : Complex) * Complex.I)) / 9

theorem digitPhaseAt_hasDerivAt (theta : Real) (n : Nat) :
    HasDerivAt (fun x : Real => digitPhaseAt x n)
      (digitPhaseAt theta n *
        (((2 * Real.pi * (n : Real) : Real) : Complex) * Complex.I)) theta := by
  unfold digitPhaseAt
  have hreal : HasDerivAt
      (fun x : Real => (2 * Real.pi * (n : Real)) * x)
      (2 * Real.pi * (n : Real)) theta :=
    hasDerivAt_const_mul (2 * Real.pi * (n : Real))
  exact (hreal.ofReal_comp.mul_const Complex.I).cexp

theorem normalizedDigitFourierFactorAt_hasDerivAt
    (digit : Fin 10) (theta : Real) :
    HasDerivAt (normalizedDigitFourierFactorAt digit)
      (normalizedDigitFourierFactorDerivativeAt digit theta) theta := by
  unfold normalizedDigitFourierFactorAt
    normalizedDigitFourierFactorDerivativeAt
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro d hd
  exact digitPhaseAt_hasDerivAt theta d

private theorem allowedDecimalDigits_sum_le (digit : Fin 10) :
    (∑ d ∈ allowedDecimalDigits digit, (d : Real)) <= 45 := by
  calc
    (∑ d ∈ allowedDecimalDigits digit, (d : Real)) <=
        ∑ d ∈ Finset.range 10, (d : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro d hd hnot
        positivity
    _ = 45 := by norm_num [Finset.sum_range_succ]

theorem norm_normalizedDigitFourierFactorDerivativeAt_le
    (digit : Fin 10) (theta : Real) :
    ‖normalizedDigitFourierFactorDerivativeAt digit theta‖ <= 40 := by
  unfold normalizedDigitFourierFactorDerivativeAt
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_div_of_nonneg_right (norm_sum_le _ _) (by norm_num)).trans
  have hphase (d : Nat) : ‖digitPhaseAt theta d‖ = 1 := by
    unfold digitPhaseAt
    exact Complex.norm_exp_ofReal_mul_I _
  have hsum :
      (∑ d ∈ allowedDecimalDigits digit,
        ‖digitPhaseAt theta d *
          (((2 * Real.pi * (d : Real) : Real) : Complex) * Complex.I)‖) =
        (2 * Real.pi) *
          ∑ d ∈ allowedDecimalDigits digit, (d : Real) := by
    calc
      _ = ∑ d ∈ allowedDecimalDigits digit,
          (2 * Real.pi) * (d : Real) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [norm_mul, hphase, one_mul, norm_mul, Complex.norm_real,
          Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg]
        positivity
      _ = _ := by rw [Finset.mul_sum]
  rw [hsum]
  calc
    (2 * Real.pi * ∑ d ∈ allowedDecimalDigits digit, (d : Real)) / 9 <=
        (2 * 4 * 45 : Real) / 9 := by
      gcongr
      · exact Real.pi_le_four
      · exact allowedDecimalDigits_sum_le digit
    _ = 40 := by norm_num

/-- The exact complex derivative, recursively following the digit product. -/
noncomputable def normalizedPaddedDigitFourierDerivativeAt
    (digit : Fin 10) : Nat -> Real -> Complex
  | 0, _ => 0
  | length + 1, theta =>
      normalizedDigitFourierFactorDerivativeAt digit theta *
          normalizedPaddedDigitFourierTransformAt digit length (10 * theta) +
        normalizedDigitFourierFactorAt digit theta *
          ((10 : Real) •
            normalizedPaddedDigitFourierDerivativeAt digit length (10 * theta))

theorem normalizedPaddedDigitFourierTransformAt_zero
    (digit : Fin 10) (theta : Real) :
    normalizedPaddedDigitFourierTransformAt digit 0 theta = 1 := by
  rw [normalizedPaddedDigitFourierTransformAt_eq_factorProduct]
  simp

theorem normalizedPaddedDigitFourierTransformAt_succ
    (digit : Fin 10) (length : Nat) (theta : Real) :
    normalizedPaddedDigitFourierTransformAt digit (length + 1) theta =
      normalizedDigitFourierFactorAt digit theta *
        normalizedPaddedDigitFourierTransformAt digit length (10 * theta) := by
  rw [normalizedPaddedDigitFourierTransformAt_eq_factorProduct,
    Fin.prod_univ_succ,
    normalizedPaddedDigitFourierTransformAt_eq_factorProduct]
  simp only [Fin.val_zero, pow_zero, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro start hstart
  congr 1
  simp only [Fin.val_succ, pow_succ]
  ring

theorem normalizedPaddedDigitFourierTransformAt_hasDerivAt
    (digit : Fin 10) (length : Nat) (theta : Real) :
    HasDerivAt (normalizedPaddedDigitFourierTransformAt digit length)
      (normalizedPaddedDigitFourierDerivativeAt digit length theta) theta := by
  induction length generalizing theta with
  | zero =>
      have hconst : HasDerivAt (fun _ : Real => (1 : Complex)) 0 theta :=
        hasDerivAt_const (x := theta) (c := (1 : Complex))
      have htransform : HasDerivAt
          (normalizedPaddedDigitFourierTransformAt digit 0) 0 theta := by
        apply hconst.congr_of_eventuallyEq
        filter_upwards [] with x
        exact normalizedPaddedDigitFourierTransformAt_zero digit x
      exact htransform.congr_deriv rfl
  | succ length ih =>
      have hinner : HasDerivAt
          (fun x : Real =>
            normalizedPaddedDigitFourierTransformAt digit length (10 * x))
          ((10 : Real) •
            normalizedPaddedDigitFourierDerivativeAt digit length (10 * theta))
          theta := by
        simpa only [Function.comp_def] using
          (ih (theta := 10 * theta)).scomp theta
            (hasDerivAt_const_mul (10 : Real))
      have hproduct :=
        (normalizedDigitFourierFactorAt_hasDerivAt digit theta).mul hinner
      have htransform : HasDerivAt
          (normalizedPaddedDigitFourierTransformAt digit (length + 1))
          (normalizedDigitFourierFactorDerivativeAt digit theta *
              normalizedPaddedDigitFourierTransformAt digit length (10 * theta) +
            normalizedDigitFourierFactorAt digit theta *
              ((10 : Real) •
                normalizedPaddedDigitFourierDerivativeAt digit length (10 * theta)))
          theta := by
        apply hproduct.congr_of_eventuallyEq
        filter_upwards [] with x
        exact normalizedPaddedDigitFourierTransformAt_succ digit length x
      exact htransform.congr_deriv rfl

/-- A pointwise majorant for the norm of the complex derivative. -/
noncomputable def normalizedPaddedDigitFourierDerivativeEnvelopeAt
    (digit : Fin 10) (length : Nat) (theta : Real) : Real :=
  40 * ∑ start : Fin length,
    (10 : Real) ^ start.val *
      normalizedPaddedDigitFourierMagnitudeAt digit start.val theta

theorem normalizedPaddedDigitFourierMagnitudeAt_zero
    (digit : Fin 10) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit 0 theta = 1 := by
  rw [normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct]
  simp

theorem normalizedPaddedDigitFourierMagnitudeAt_succ
    (digit : Fin 10) (length : Nat) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit (length + 1) theta =
      digitKernel digit theta *
        normalizedPaddedDigitFourierMagnitudeAt digit length (10 * theta) := by
  rw [normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct,
    Fin.prod_univ_succ,
    normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct]
  simp only [Fin.val_zero, pow_zero, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro start hstart
  congr 1
  simp only [Fin.val_succ, pow_succ]
  ring

theorem normalizedPaddedDigitFourierDerivativeEnvelopeAt_succ
    (digit : Fin 10) (length : Nat) (theta : Real) :
    normalizedPaddedDigitFourierDerivativeEnvelopeAt digit (length + 1) theta =
      40 + 10 * digitKernel digit theta *
        normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length
          (10 * theta) := by
  rw [normalizedPaddedDigitFourierDerivativeEnvelopeAt,
    Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero,
    normalizedPaddedDigitFourierMagnitudeAt_zero, one_mul,
    Fin.val_succ, pow_succ,
    normalizedPaddedDigitFourierMagnitudeAt_succ,
    normalizedPaddedDigitFourierDerivativeEnvelopeAt]
  have hsum :
      (∑ start : Fin length,
        (10 : Real) ^ start.val * 10 *
          (digitKernel digit theta *
            normalizedPaddedDigitFourierMagnitudeAt digit start.val (10 * theta))) =
        10 * digitKernel digit theta *
          ∑ start : Fin length,
            (10 : Real) ^ start.val *
              normalizedPaddedDigitFourierMagnitudeAt digit start.val (10 * theta) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro start hstart
    ring
  rw [hsum]
  ring

theorem normalizedPaddedDigitFourierDerivativeEnvelopeAt_nonneg
    (digit : Fin 10) (length : Nat) (theta : Real) :
    0 <= normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length theta := by
  unfold normalizedPaddedDigitFourierDerivativeEnvelopeAt
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro start hstart
  exact mul_nonneg (by positivity)
    (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit start.val theta)

theorem normalizedPaddedDigitFourierDerivativeEnvelopeAt_continuous
    (digit : Fin 10) (length : Nat) :
    Continuous
      (normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length) := by
  unfold normalizedPaddedDigitFourierDerivativeEnvelopeAt
  apply continuous_const.mul
  apply continuous_finsetSum
  intro start hstart
  exact continuous_const.mul
    (normalizedPaddedDigitFourierMagnitudeAt_continuous digit start.val)

theorem normalizedPaddedDigitFourierDerivativeEnvelopeAt_periodic
    (digit : Fin 10) (length : Nat) :
    Function.Periodic
      (normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length) 1 := by
  intro theta
  unfold normalizedPaddedDigitFourierDerivativeEnvelopeAt
  congr 1
  apply Finset.sum_congr rfl
  intro start hstart
  congr 1
  exact normalizedPaddedDigitFourierMagnitudeAt_periodic digit start.val theta

theorem norm_normalizedPaddedDigitFourierDerivativeAt_le
    (digit : Fin 10) (length : Nat) (theta : Real) :
    ‖normalizedPaddedDigitFourierDerivativeAt digit length theta‖ <=
      normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length theta := by
  induction length generalizing theta with
  | zero =>
      simp [normalizedPaddedDigitFourierDerivativeAt,
        normalizedPaddedDigitFourierDerivativeEnvelopeAt]
  | succ length ih =>
      rw [normalizedPaddedDigitFourierDerivativeAt,
        normalizedPaddedDigitFourierDerivativeEnvelopeAt_succ]
      calc
        ‖normalizedDigitFourierFactorDerivativeAt digit theta *
              normalizedPaddedDigitFourierTransformAt digit length (10 * theta) +
            normalizedDigitFourierFactorAt digit theta *
              ((10 : Real) •
                normalizedPaddedDigitFourierDerivativeAt digit length
                  (10 * theta))‖ <=
            ‖normalizedDigitFourierFactorDerivativeAt digit theta *
              normalizedPaddedDigitFourierTransformAt digit length (10 * theta)‖ +
            ‖normalizedDigitFourierFactorAt digit theta *
              ((10 : Real) •
                normalizedPaddedDigitFourierDerivativeAt digit length
                  (10 * theta))‖ := norm_add_le _ _
        _ = ‖normalizedDigitFourierFactorDerivativeAt digit theta‖ *
              normalizedPaddedDigitFourierMagnitudeAt digit length (10 * theta) +
            digitKernel digit theta *
              (10 * ‖normalizedPaddedDigitFourierDerivativeAt digit length
                (10 * theta)‖) := by
          rw [norm_mul, norm_normalizedPaddedDigitFourierTransformAt,
            norm_mul, norm_normalizedDigitFourierFactorAt, norm_smul]
          norm_num
        _ <= 40 * 1 + digitKernel digit theta *
              (10 * normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length
                (10 * theta)) := by
          apply add_le_add
          · exact mul_le_mul
              (norm_normalizedDigitFourierFactorDerivativeAt_le digit theta)
              (normalizedPaddedDigitFourierMagnitudeAt_le_one digit length _)
              (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)
              (by norm_num)
          · apply mul_le_mul_of_nonneg_left _ (digitKernel_nonneg digit theta)
            exact mul_le_mul_of_nonneg_left (ih (theta := 10 * theta))
              (by norm_num)
        _ = 40 + 10 * digitKernel digit theta *
              normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length
                (10 * theta) := by ring

/-- The normalized complex transform varies by at most the envelope integral. -/
theorem normalizedPaddedDigitFourierTransformAt_norm_sub_le_integral_envelope
    (digit : Fin 10) (length : Nat) {s t : Real} (hst : s <= t) :
    ‖normalizedPaddedDigitFourierTransformAt digit length t -
        normalizedPaddedDigitFourierTransformAt digit length s‖ <=
  ∫ theta in s..t,
        normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length theta := by
  let transform := normalizedPaddedDigitFourierTransformAt digit length
  have hdiff : Differentiable Real transform := fun theta =>
    (normalizedPaddedDigitFourierTransformAt_hasDerivAt digit length theta).differentiableAt
  apply norm_sub_le_integral_of_norm_deriv_le_of_le hst
  · exact hdiff.continuous.continuousOn
  · exact hdiff.differentiableOn
  · filter_upwards [] with theta htheta
    rw [(normalizedPaddedDigitFourierTransformAt_hasDerivAt
      digit length theta).deriv]
    exact norm_normalizedPaddedDigitFourierDerivativeAt_le digit length theta
  · exact (normalizedPaddedDigitFourierDerivativeEnvelopeAt_continuous
      digit length).intervalIntegrable s t

theorem abs_normalizedPaddedDigitFourierMagnitudeAt_sub_le_integral_envelope
    (digit : Fin 10) (length : Nat) {s t : Real} (hst : s <= t) :
    |normalizedPaddedDigitFourierMagnitudeAt digit length t -
        normalizedPaddedDigitFourierMagnitudeAt digit length s| <=
      ∫ theta in s..t,
        normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length theta := by
  calc
    |normalizedPaddedDigitFourierMagnitudeAt digit length t -
        normalizedPaddedDigitFourierMagnitudeAt digit length s| =
        |‖normalizedPaddedDigitFourierTransformAt digit length t‖ -
          ‖normalizedPaddedDigitFourierTransformAt digit length s‖| := by
      rw [norm_normalizedPaddedDigitFourierTransformAt,
        norm_normalizedPaddedDigitFourierTransformAt]
    _ <= ‖normalizedPaddedDigitFourierTransformAt digit length t -
          normalizedPaddedDigitFourierTransformAt digit length s‖ :=
      abs_norm_sub_norm_le _ _
    _ <= ∫ theta in s..t,
        normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length theta :=
      normalizedPaddedDigitFourierTransformAt_norm_sub_le_integral_envelope
        digit length hst

end PrimesRestrictedDigits
