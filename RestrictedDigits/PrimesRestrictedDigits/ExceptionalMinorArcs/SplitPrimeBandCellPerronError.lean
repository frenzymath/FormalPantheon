import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeBandCellPerronCoefficient

/-!
# Quantitative Perron error for one rational/product cell

The combined coefficient mass retains the exact rational-fiber cardinality. The half-integer
theorem then gives the explicit band-cell error.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The normalized magnitude times the canonical digit phase is one-bounded. -/
theorem norm_splitPrimeBandCellFrequencyScalar_le_one
    (digit : Fin 10) (length frequency : Nat) :
    ‖(normalizedPaddedDigitFourierMagnitude
        digit length frequency : Complex) *
      paddedDigitFourierNormPhase digit length frequency‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg
      (normalizedPaddedDigitFourierMagnitude_nonneg digit length frequency)]
  calc
    normalizedPaddedDigitFourierMagnitude digit length frequency *
        ‖paddedDigitFourierNormPhase digit length frequency‖ ≤ 1 * 1 :=
      mul_le_mul
        (normalizedPaddedDigitFourierMagnitude_le_one digit length frequency)
        (norm_paddedDigitFourierNormPhase_le_one digit length frequency)
        (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-- The combined coefficient mass is the fixed-frequency mass bound times
the exact cardinality of its disjoint rational fiber. -/
theorem sum_norm_splitPrimeBandCellPerronCoefficient_le
    {length : Nat} (hlength : 0 < length) (digit : Fin 10)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) :
    (∑ r ∈ splitPrimeCellPerronSupport length,
      ‖splitPrimeBandCellPerronCoefficient digit length a delta eta I S
        bandKey productKey r‖) ≤
      ((exceptionalDirichletBandFiber S bandKey).card : Real) *
        ((10 ^ length : Nat) : Real) ^ 2 *
        selectedPrimePerronCoefficientCap (10 ^ length) I *
        complementaryPrimePerronCoefficientCap (10 ^ length) I := by
  classical
  let H := exceptionalDirichletBandFiber S bandKey
  let R := splitPrimeCellPerronSupport length
  let d (h : Fin (10 ^ length)) : Complex :=
    (normalizedPaddedDigitFourierMagnitude digit length h.val : Complex) *
      paddedDigitFourierNormPhase digit length h.val
  let c (h : Fin (10 ^ length)) :=
    splitPrimeCellPerronCoefficient
      length h.val a delta eta I productKey
  let X : Real := ((10 ^ length : Nat) : Real)
  let A := selectedPrimePerronCoefficientCap (10 ^ length) I
  let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
  calc
    (∑ r ∈ R,
        ‖splitPrimeBandCellPerronCoefficient digit length a delta eta I S
          bandKey productKey r‖) ≤
        ∑ r ∈ R, ∑ h ∈ H, ‖d h * c h r‖ := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [splitPrimeBandCellPerronCoefficient, H, d, c] using
        norm_sum_le H (fun h => d h * c h r)
    _ = ∑ h ∈ H, ∑ r ∈ R, ‖d h * c h r‖ := Finset.sum_comm
    _ ≤ ∑ h ∈ H, X ^ 2 * A * B := by
      apply Finset.sum_le_sum
      intro h hh
      calc
        (∑ r ∈ R, ‖d h * c h r‖) ≤ ∑ r ∈ R, ‖c h r‖ := by
          apply Finset.sum_le_sum
          intro r hr
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right
            (show ‖d h‖ ≤ 1 by
              exact norm_splitPrimeBandCellFrequencyScalar_le_one
                digit length h.val)
            (norm_nonneg _)).trans_eq (one_mul _)
        _ ≤ X ^ 2 * A * B := by
          simpa only [R, c, X, A, B] using
            sum_norm_splitPrimeCellPerronCoefficient_le
              hlength h.val a delta eta I productKey
    _ = ((H.card : Nat) : Real) * X ^ 2 * A * B := by
      simp
      ring
    _ = ((exceptionalDirichletBandFiber S bandKey).card : Real) *
        ((10 ^ length : Nat) : Real) ^ 2 *
        selectedPrimePerronCoefficientCap (10 ^ length) I *
        complementaryPrimePerronCoefficientCap (10 ^ length) I := by
      rfl

/-- The explicit half-integer Perron error for one rational/product cell. -/
theorem norm_splitPrimeBandCellStrictSum_sub_finitePerronIntegral_le
    {length : Nat} (hlength : 0 < length) (digit : Fin 10)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) :
    ‖splitPrimeBandCellStrictSum digit length a delta eta I S
        bandKey productKey -
      finitePerronIntegral
        (splitPrimeCellPerronSupport length)
        (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
          bandKey productKey)
        (((10 ^ length : Nat) : Real) - 1 / 2)
        (Real.log ((10 ^ length : Nat) : Real))⁻¹
        (((10 ^ length : Nat) : Real) ^ 4)‖ ≤
      20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
          selectedPrimePerronCoefficientCap (10 ^ length) I *
          complementaryPrimePerronCoefficientCap (10 ^ length) I /
        ((10 ^ length : Nat) : Real) := by
  let X : Nat := 10 ^ length
  let H := exceptionalDirichletBandFiber S bandKey
  let R := splitPrimeCellPerronSupport length
  let c := splitPrimeBandCellPerronCoefficient digit length a delta eta I S
    bandKey productKey
  let A := selectedPrimePerronCoefficientCap X I
  let B := complementaryPrimePerronCoefficientCap X I
  have hXTen : 10 ≤ X := by
    dsimp only [X]
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 10)
        (by omega : 1 ≤ length))
  have hXFour : 4 ≤ X := by omega
  have hXPos : (0 : Real) < X := by positivity
  have hsupport : ∀ r, r ∈ R → 0 < r := by
    intro r hr
    exact (Finset.mem_Ico.mp hr).1
  have hperron := norm_sum_lt_sub_halfIntegerPerronIntegral_le
    (X := X) hXFour (S := R) (c := c) hsupport
  have hmass : (∑ r ∈ R, ‖c r‖) ≤
      ((H.card : Nat) : Real) * (X : Real) ^ 2 * A * B := by
    simpa only [X, H, R, c, A, B] using
      sum_norm_splitPrimeBandCellPerronCoefficient_le
        hlength digit a delta eta I S bandKey productKey
  rw [splitPrimeBandCellStrictSum]
  exact hperron.trans <| calc
    20 * (∑ r ∈ R, ‖c r‖) / (X : Real) ^ 3 ≤
        20 * (((H.card : Nat) : Real) * (X : Real) ^ 2 * A * B) /
          (X : Real) ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) (by positivity)
    _ = 20 * ((H.card : Nat) : Real) * A * B / (X : Real) := by
      field_simp [hXPos.ne']
    _ = 20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
          selectedPrimePerronCoefficientCap (10 ^ length) I *
          complementaryPrimePerronCoefficientCap (10 ^ length) I /
        ((10 ^ length : Nat) : Real) := by
      rfl

end

end PrimesRestrictedDigits
