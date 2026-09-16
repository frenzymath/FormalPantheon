import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeBandCellPerronError
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronHalfIntegerPower
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronVerticalNorm

/-!
# One-cell Perron contour bound

This composes the fixed-height localized bilinear estimate with the positive half-integer
cutoff power and logarithmic reciprocal-line norm.
-/

open Complex MeasureTheory
open scoped Interval

namespace PrimesRestrictedDigits

noncomputable section

private theorem perronLogLine_ne_zero
    {X : Nat} (hX : 4 ≤ X) (t : Real) :
    ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
      Complex.I * (t : Complex)) ≠ 0 := by
  have hlogPos : 0 < Real.log (X : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < X by omega)
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
    sub_zero, add_zero, Complex.zero_re] at hre
  exact (inv_pos.mpr hlogPos).ne' hre

private theorem perronLogLineReciprocal_continuous
    {X : Nat} (hX : 4 ≤ X) :
    Continuous (fun t : Real =>
      1 / ‖((((Real.log (X : Real))⁻¹ : Real) : Complex) +
        Complex.I * (t : Complex))‖) := by
  apply continuous_const.div₀
  · fun_prop
  · intro t
    exact norm_ne_zero_iff.mpr (perronLogLine_ne_zero hX t)

/-- A pointwise bound for the localized bilinear factor gives the explicit
one-cell contour bound. -/
theorem norm_finitePerronIntegral_splitPrimeBandCell_le_of_pointwise
    {length : Nat} (hlength : 0 < length) (digit : Fin 10)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) (K : Real) (hK : 0 ≤ K)
    (hpointwise : ∀ t : Real,
      ‖localizedSplitPrimePerronBilinearSum digit length a delta eta I S
        bandKey productKey
        (((Real.log ((10 ^ length : Nat) : Real))⁻¹ : Real) +
          Complex.I * t)
        (fun h => paddedDigitFourierNormPhase digit length h.val)‖ ≤ K) :
    ‖finitePerronIntegral
        (splitPrimeCellPerronSupport length)
        (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
          bandKey productKey)
        (((10 ^ length : Nat) : Real) - 1 / 2)
        (Real.log ((10 ^ length : Nat) : Real))⁻¹
        (((10 ^ length : Nat) : Real) ^ 4)‖ ≤
      30 * K * Real.log ((10 ^ length : Nat) : Real) := by
  let X : Nat := 10 ^ length
  have hXTen : 10 ≤ X := by
    dsimp only [X]
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 10)
        (by omega : 1 ≤ length))
  have hXFour : 4 ≤ X := by omega
  have hTNonneg : (0 : Real) ≤ (X : Real) ^ 4 := by positivity
  let g : Real → Real := fun t =>
    3 * K *
      (1 / ‖((((Real.log (X : Real))⁻¹ : Real) : Complex) +
        Complex.I * (t : Complex))‖)
  have hg : IntervalIntegrable g volume (-((X : Real) ^ 4))
      ((X : Real) ^ 4) := by
    exact (continuous_const.mul
      (perronLogLineReciprocal_continuous hXFour)).intervalIntegrable _ _
  have hintegral :
      ‖∫ t in -((X : Real) ^ 4)..((X : Real) ^ 4),
        localizedSplitPrimePerronBilinearSum digit length a delta eta I S
            bandKey productKey
            ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
              Complex.I * (t : Complex))
            (fun h => paddedDigitFourierNormPhase digit length h.val) *
          (((X : Real) - 1 / 2 : Real) : Complex) ^
              ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
                Complex.I * (t : Complex)) /
            ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
              Complex.I * (t : Complex))‖ ≤
        ∫ t in -((X : Real) ^ 4)..((X : Real) ^ 4), g t := by
    apply intervalIntegral.norm_integral_le_of_norm_le
    · linarith
    · filter_upwards with t
      intro ht
      rw [norm_div, norm_mul]
      have hpower := norm_halfIntegerPerronCutoffCpow_le_three hXFour t
      calc
        ‖localizedSplitPrimePerronBilinearSum digit length a delta eta I S
              bandKey productKey
              ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
                Complex.I * (t : Complex))
              (fun h => paddedDigitFourierNormPhase digit length h.val)‖ *
              ‖(((X : Real) - 1 / 2 : Real) : Complex) ^
                ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
                  Complex.I * (t : Complex))‖ /
            ‖((((Real.log (X : Real))⁻¹ : Real) : Complex) +
              Complex.I * (t : Complex))‖ ≤
            (K * 3) /
              ‖((((Real.log (X : Real))⁻¹ : Real) : Complex) +
                Complex.I * (t : Complex))‖ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul (hpointwise t) hpower (norm_nonneg _) hK)
            (norm_nonneg _)
        _ = g t := by
          dsimp only [g]
          ring
    · exact hg
  have hreciprocal := integral_norm_inv_logLine_le hXFour
  have hmajorant :
      (∫ t in -((X : Real) ^ 4)..((X : Real) ^ 4), g t) ≤
        30 * K * Real.log (X : Real) := by
    dsimp only [g]
    rw [intervalIntegral.integral_const_mul]
    calc
      3 * K *
          (∫ t in -((X : Real) ^ 4)..((X : Real) ^ 4),
            1 / ‖((((Real.log (X : Real))⁻¹ : Real) : Complex) +
              Complex.I * (t : Complex))‖) ≤
          3 * K * (10 * Real.log (X : Real)) :=
        mul_le_mul_of_nonneg_left hreciprocal
          (mul_nonneg (by norm_num) hK)
      _ = 30 * K * Real.log (X : Real) := by ring
  have hscale : (1 / (2 * Real.pi) : Real) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.two_le_pi]
  rw [finitePerronIntegral_splitPrimeBandCellPerronCoefficient_eq,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  dsimp only [X] at hintegral hmajorant ⊢
  calc
    1 / (2 * Real.pi) *
        ‖∫ t in -(((10 ^ length : Nat) : Real) ^ 4)..
            (((10 ^ length : Nat) : Real) ^ 4),
          localizedSplitPrimePerronBilinearSum digit length a delta eta I S
                bandKey productKey
                ((((Real.log ((10 ^ length : Nat) : Real))⁻¹ : Real) :
                    Complex) + Complex.I * (t : Complex))
                (fun h => paddedDigitFourierNormPhase digit length h.val) *
              ((((10 ^ length : Nat) : Real) - 1 / 2 : Real) : Complex) ^
                  ((((Real.log ((10 ^ length : Nat) : Real))⁻¹ : Real) :
                      Complex) + Complex.I * (t : Complex)) /
                ((((Real.log ((10 ^ length : Nat) : Real))⁻¹ : Real) :
                    Complex) + Complex.I * (t : Complex))‖ ≤
        1 * (30 * K * Real.log ((10 ^ length : Nat) : Real)) := by
      exact mul_le_mul hscale (hintegral.trans hmajorant)
        (norm_nonneg _) (by positivity)
    _ = 30 * K * Real.log ((10 ^ length : Nat) : Real) := by ring

/-- Adding the explicit half-Perron error converts any contour bound into a
bound for the literal strict band/product cell. -/
theorem norm_splitPrimeBandCellStrictSum_le_of_integral
    {length : Nat} (hlength : 0 < length) (digit : Fin 10)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) (K : Real)
    (hintegral :
      ‖finitePerronIntegral
          (splitPrimeCellPerronSupport length)
          (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
            bandKey productKey)
          (((10 ^ length : Nat) : Real) - 1 / 2)
          (Real.log ((10 ^ length : Nat) : Real))⁻¹
          (((10 ^ length : Nat) : Real) ^ 4)‖ ≤ K) :
    ‖splitPrimeBandCellStrictSum digit length a delta eta I S
        bandKey productKey‖ ≤
      20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
          selectedPrimePerronCoefficientCap (10 ^ length) I *
          complementaryPrimePerronCoefficientCap (10 ^ length) I /
        ((10 ^ length : Nat) : Real) + K := by
  let P := finitePerronIntegral
    (splitPrimeCellPerronSupport length)
    (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
      bandKey productKey)
    (((10 ^ length : Nat) : Real) - 1 / 2)
    (Real.log ((10 ^ length : Nat) : Real))⁻¹
    (((10 ^ length : Nat) : Real) ^ 4)
  have herror :=
    norm_splitPrimeBandCellStrictSum_sub_finitePerronIntegral_le
      hlength digit a delta eta I S bandKey productKey
  change ‖splitPrimeBandCellStrictSum digit length a delta eta I S
      bandKey productKey‖ ≤ _
  calc
    ‖splitPrimeBandCellStrictSum digit length a delta eta I S
        bandKey productKey‖ =
        ‖(splitPrimeBandCellStrictSum digit length a delta eta I S
            bandKey productKey - P) + P‖ := by rw [sub_add_cancel]
    _ ≤ ‖splitPrimeBandCellStrictSum digit length a delta eta I S
          bandKey productKey - P‖ + ‖P‖ := norm_add_le _ _
    _ ≤ 20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
            selectedPrimePerronCoefficientCap (10 ^ length) I *
            complementaryPrimePerronCoefficientCap (10 ^ length) I /
          ((10 ^ length : Nat) : Real) + K := by
      exact add_le_add herror hintegral

/-- The fixed-height bilinear theorem, the cutoff-power bound, and the
reciprocal-line estimate give uniform integral and strict-cell bounds on every
active rational/product cell. -/
theorem exists_activeSplitPrimeBandCellPerronBounds :
    ∃ C : Real, 0 < C ∧ ∃ logLoss length0 : Nat,
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (delta eta mu : Real) (I : Finset (Fin k))
        (S : Finset (Fin (10 ^ length)))
        (bandKey productKey : Nat × Nat),
        let X : Real := ((10 ^ length : Nat) : Real)
        let Q := exceptionalDirichletDenominatorScaleAt
          (10 ^ length) bandKey.1
        let E := exceptionalDirichletErrorScaleAt
          (10 ^ length) bandKey.2
        let A := selectedPrimePerronCoefficientCap (10 ^ length) I
        let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
        let K := A * B *
          (C * X * Real.log X ^ logLoss /
            (Q + E) ^ (latticeSumSaving / 10))
        0 ≤ delta →
        ((k + 1 : Nat) : Real) * delta + 1 / (length : Real) ≤ mu →
        ((∑ i ∈ I, a i) ∈
            Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
            Set.Icc (23 / 40 + mu) (16 / 25 - mu)) →
        S ⊆ genericExceptionalFrequencies digit length →
        IsActiveSplitPrimeCell length a delta eta I productKey →
        ‖finitePerronIntegral
            (splitPrimeCellPerronSupport length)
            (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
              bandKey productKey)
            (X - 1 / 2) (Real.log X)⁻¹ (X ^ 4)‖ ≤
              30 * K * Real.log X ∧
          ‖splitPrimeBandCellStrictSum digit length a delta eta I S
              bandKey productKey‖ ≤
            20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
                A * B / X + 30 * K * Real.log X := by
  obtain ⟨C, hC, logLoss, sourceLength, hsource⟩ :=
    exists_localizedSplitPrimePerronBilinearBound
  refine ⟨C, hC, logLoss, max sourceLength 1, ?_⟩
  intro length hlength digit k a delta eta mu I S bandKey productKey
  dsimp only
  intro hdelta hmargin hconvenient hS hactive
  have hsourceLength : sourceLength ≤ length :=
    (le_max_left sourceLength 1).trans hlength
  have hlengthOne : 1 ≤ length :=
    (le_max_right sourceLength 1).trans hlength
  have hlengthPos : 0 < length := Nat.zero_lt_of_lt hlengthOne
  let X : Real := ((10 ^ length : Nat) : Real)
  let Q := exceptionalDirichletDenominatorScaleAt
    (10 ^ length) bandKey.1
  let E := exceptionalDirichletErrorScaleAt
    (10 ^ length) bandKey.2
  let A := selectedPrimePerronCoefficientCap (10 ^ length) I
  let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
  let K := A * B *
    (C * X * Real.log X ^ logLoss /
      (Q + E) ^ (latticeSumSaving / 10))
  have hXOne : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow hlengthPos.ne' (by norm_num : 1 < 10)
  have hlogPos : 0 < Real.log X := Real.log_pos hXOne
  have hpointwise (t : Real) :
      ‖localizedSplitPrimePerronBilinearSum digit length a delta eta I S
        bandKey productKey
        ((((Real.log X)⁻¹ : Real) : Complex) +
          Complex.I * (t : Complex))
        (fun h => paddedDigitFourierNormPhase digit length h.val)‖ ≤ K := by
    dsimp only [K, A, B, X, Q, E]
    apply hsource length hsourceLength digit k a delta eta mu I S
      bandKey productKey
      ((((Real.log ((10 ^ length : Nat) : Real))⁻¹ : Real) : Complex) +
        Complex.I * (t : Complex))
      (fun h => paddedDigitFourierNormPhase digit length h.val)
      hdelta hmargin hconvenient hS hactive
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
        sub_zero, add_zero]
      exact (inv_pos.mpr hlogPos).le
    · intro h
      exact norm_paddedDigitFourierNormPhase_le_one digit length h.val
  have hK : 0 ≤ K :=
    (norm_nonneg (localizedSplitPrimePerronBilinearSum digit length a delta
      eta I S bandKey productKey
      ((((Real.log X)⁻¹ : Real) : Complex) + Complex.I * (0 : Complex))
      (fun h => paddedDigitFourierNormPhase digit length h.val))).trans
        (hpointwise 0)
  have hcontour :=
    norm_finitePerronIntegral_splitPrimeBandCell_le_of_pointwise
      hlengthPos digit a delta eta I S bandKey productKey K hK
      (fun t => by simpa only [X] using hpointwise t)
  have hstrict := norm_splitPrimeBandCellStrictSum_le_of_integral
    hlengthPos digit a delta eta I S bandKey productKey
    (30 * K * Real.log X) (by simpa only [X] using hcontour)
  constructor
  · simpa only [X, K, A, B, Q, E] using hcontour
  · simpa only [X, K, A, B, Q, E] using hstrict

end

end PrimesRestrictedDigits
