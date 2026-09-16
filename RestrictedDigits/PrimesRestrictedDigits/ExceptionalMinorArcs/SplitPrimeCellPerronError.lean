import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeCellPerronCoefficient

/-!
# Quantitative Perron error for one split-prime cell

The product-fiber coefficient has norm mass at most `X^2` times the two factorial-logarithm
caps. The half-integer Perron theorem therefore gives an explicit error of `20 * capA * capB /
X`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A coordinate fiber is a subset of the positive ambient interval and so
has at most `10^length` elements. -/
theorem card_splitProductCoordinateFiber_le_ambient
    (length i : Nat) :
    (splitProductCoordinateFiber length i).card ≤ 10 ^ length := by
  calc
    (splitProductCoordinateFiber length i).card ≤
        (Finset.Ico 1 (10 ^ length)).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ 10 ^ length := by simp

/-- The norm of a pair coefficient is exactly the product of its two
nonnegative real prime weights. -/
theorem norm_splitPrimeCellPairCoefficient
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k)) (nm : Nat × Nat) :
    ‖splitPrimeCellPairCoefficient
        length frequency a delta eta I nm‖ =
      selectedProjectedPrimeWeightAtProduct
          (10 ^ length) a delta I nm.1 *
        complementaryLastPrimeWeightAtProduct
          (10 ^ length) a delta eta I nm.2 := by
  rw [splitPrimeCellPairCoefficient, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg
      (selectedProjectedPrimeWeightAtProduct_nonneg _ _ _ _ _),
    Real.norm_of_nonneg
      (complementaryLastPrimeWeightAtProduct_nonneg _ _ _ _ _ _),
    norm_majorArcPhase_eq_one, mul_one]

/-- The full positive-support coefficient norm mass is bounded by the two
pointwise caps and the at-most-`X^2` pair count. -/
theorem sum_norm_splitPrimeCellPerronCoefficient_le
    {length : Nat} (hlength : 0 < length) (frequency : Nat)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (productKey : Nat × Nat) :
    (∑ r ∈ splitPrimeCellPerronSupport length,
        ‖splitPrimeCellPerronCoefficient
          length frequency a delta eta I productKey r‖) ≤
      ((10 ^ length : Nat) : Real) ^ 2 *
        selectedPrimePerronCoefficientCap (10 ^ length) I *
        complementaryPrimePerronCoefficientCap (10 ^ length) I := by
  classical
  let X : Nat := 10 ^ length
  let N := splitProductCoordinateFiber length productKey.1
  let M := splitProductCoordinateFiber length productKey.2
  let P := splitPrimeCellPairs length productKey
  let R := splitPrimeCellPerronSupport length
  let w := splitPrimeCellPairCoefficient length frequency a delta eta I
  let A := selectedPrimePerronCoefficientCap X I
  let B := complementaryPrimePerronCoefficientCap X I
  have hX : 1 < X := by
    dsimp only [X]
    exact Nat.one_lt_pow hlength.ne' (by norm_num)
  have hAPos : 0 < A := selectedPrimePerronCoefficientCap_pos hX I
  have hBPos : 0 < B := complementaryPrimePerronCoefficientCap_pos hX I
  have hmaps : ∀ nm ∈ P, nm.1 * nm.2 ∈ R := by
    intro nm hnm
    exact splitPrimeCellPair_product_mem_perronSupport hnm
  have hcardN : ((N.card : Nat) : Real) ≤ (X : Real) := by
    exact_mod_cast card_splitProductCoordinateFiber_le_ambient
      length productKey.1
  have hcardM : ((M.card : Nat) : Real) ≤ (X : Real) := by
    exact_mod_cast card_splitProductCoordinateFiber_le_ambient
      length productKey.2
  calc
    (∑ r ∈ R,
        ‖splitPrimeCellPerronCoefficient
          length frequency a delta eta I productKey r‖) ≤
        ∑ r ∈ R, ∑ nm ∈ P with nm.1 * nm.2 = r, ‖w nm‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact norm_sum_le _ _
    _ = ∑ nm ∈ P, ‖w nm‖ :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ nm ∈ P,
          selectedProjectedPrimeWeightAtProduct X a delta I nm.1 *
            complementaryLastPrimeWeightAtProduct
              X a delta eta I nm.2 := by
      apply Finset.sum_congr rfl
      intro nm hnm
      exact norm_splitPrimeCellPairCoefficient
        length frequency a delta eta I nm
    _ = ∑ n ∈ N, ∑ m ∈ M,
          selectedProjectedPrimeWeightAtProduct X a delta I n *
            complementaryLastPrimeWeightAtProduct X a delta eta I m := by
      dsimp only [P, N, M, X]
      rw [splitPrimeCellPairs]
      exact Finset.sum_product _ _ _
    _ ≤ ∑ n ∈ N, ∑ m ∈ M, A * B := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul
        (selectedProjectedPrimeWeightAtProduct_le
          X n a delta I (splitProductCoordinateFiber_lt_ambient hn))
        (complementaryLastPrimeWeightAtProduct_le
          X m a delta eta I (splitProductCoordinateFiber_lt_ambient hm))
        (complementaryLastPrimeWeightAtProduct_nonneg _ _ _ _ _ _)
        hAPos.le
    _ = ((N.card : Nat) : Real) * ((M.card : Nat) : Real) * (A * B) := by
      simp
      ring
    _ ≤ (X : Real) ^ 2 * (A * B) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hAPos.le hBPos.le)
      rw [pow_two]
      exact mul_le_mul hcardN hcardM (by positivity) (by positivity)
    _ = ((10 ^ length : Nat) : Real) ^ 2 *
        selectedPrimePerronCoefficientCap (10 ^ length) I *
        complementaryPrimePerronCoefficientCap (10 ^ length) I := by
      simp only [X, A, B]
      ring

/-- The finite Perron error for one fixed-frequency, fixed-product cell. -/
theorem norm_splitPrimeCellStrictSum_sub_finitePerronIntegral_le
    {length : Nat} (hlength : 0 < length) (frequency : Nat)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (productKey : Nat × Nat) :
    ‖splitPrimeCellStrictSum
        length frequency a delta eta I productKey -
      finitePerronIntegral
        (splitPrimeCellPerronSupport length)
        (splitPrimeCellPerronCoefficient
          length frequency a delta eta I productKey)
        (((10 ^ length : Nat) : Real) - 1 / 2)
        (Real.log ((10 ^ length : Nat) : Real))⁻¹
        (((10 ^ length : Nat) : Real) ^ 4)‖ ≤
      20 * selectedPrimePerronCoefficientCap (10 ^ length) I *
          complementaryPrimePerronCoefficientCap (10 ^ length) I /
        ((10 ^ length : Nat) : Real) := by
  let X : Nat := 10 ^ length
  let R := splitPrimeCellPerronSupport length
  let c := splitPrimeCellPerronCoefficient
    length frequency a delta eta I productKey
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
  have hmass : (∑ r ∈ R, ‖c r‖) ≤ (X : Real) ^ 2 * A * B := by
    simpa only [X, R, c, A, B] using
      sum_norm_splitPrimeCellPerronCoefficient_le
        hlength frequency a delta eta I productKey
  rw [splitPrimeCellStrictSum]
  exact hperron.trans <| calc
    20 * (∑ r ∈ R, ‖c r‖) / (X : Real) ^ 3 ≤
        20 * ((X : Real) ^ 2 * A * B) / (X : Real) ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) (by positivity)
    _ = 20 * A * B / (X : Real) := by
      field_simp [hXPos.ne']
    _ = 20 * selectedPrimePerronCoefficientCap (10 ^ length) I *
          complementaryPrimePerronCoefficientCap (10 ^ length) I /
        ((10 ^ length : Nat) : Real) := by
      rfl

end

end PrimesRestrictedDigits
