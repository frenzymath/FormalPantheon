import Waring.LargeNumber.DigitCount
import Waring.LargeNumber.ScaleFloorBounds

/-!
# Product lower bound for Chen's eleven scales

This file completes the omitted floor bookkeeping in Chen's English Lemma 11 /
Chinese Lemma 12 [CHEN1964-EN, pp. 1567-1568;
CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

open scoped BigOperators

noncomputable section

/-- Sum of the eleven geometric exponents in Chen's scales. -/
def scaleExponentSum : Real :=
  ∑ i ∈ Finset.range 11, scaleRatio ^ i

/-- Every one of the eleven scales is large enough for the relative floor
bound. -/
theorem tenThousand_le_iterScale {p₁ : Nat} (hp₁ : 10 ^ 155 ≤ p₁)
    (i : Fin 11) :
    10 ^ 4 ≤ iterScale p₁ i := by
  have h := ten_pow_scaleThresholdExponent_le_iterScale hp₁ i
  have hExponent : 16 ≤ scaleThresholdExponent i := by
    fin_cases i <;> norm_num [scaleThresholdExponent]
  have hTen : 10 ^ 16 ≤ 10 ^ scaleThresholdExponent i :=
    pow_le_pow_right' (by norm_num) hExponent
  exact (by norm_num : 10 ^ 4 ≤ 10 ^ 16) |>.trans (hTen.trans h)

/-- The initial irrational floor retains the stable loss times its ideal
unfloored scale. -/
theorem scaleLoss_mul_main_div_denominator_le_firstScale {p : Nat}
    (hp : 10 ^ 156 ≤ p) :
    scaleLoss * ((p : Real) / firstScaleDenominator) ≤ firstScale p := by
  have hp₁ : 10 ^ 155 ≤ firstScale p :=
    ten_pow_oneFiftyFive_le_firstScale hp
  have hFloorLower : (1000 : Real) ≤ firstScale p := by
    exact_mod_cast (show 1000 ≤ firstScale p from
      (by norm_num : 1000 ≤ 10 ^ 155).trans hp₁)
  have hFloorUpper : ((firstScale p : Nat) : Real) ≤
      (p : Real) / firstScaleDenominator := by
    exact Nat.floor_le (div_nonneg (by positivity) firstScaleDenominator_pos.le)
  have hInput : (1000 : Real) ≤ (p : Real) / firstScaleDenominator :=
    hFloorLower.trans hFloorUpper
  have hRetained := floorRetention_mul_le_natFloor hInput
  have hInputNonneg : 0 ≤ (p : Real) / firstScaleDenominator := by positivity
  exact (mul_le_mul_of_nonneg_right scaleLoss_le_floorRetention hInputNonneg).trans
    hRetained

private theorem scaleLoss_mul_rpow_succ (b : Real) (hb : 0 ≤ b) (i : Nat) :
    scaleLoss * b ^ (scaleRatio ^ (i + 1)) =
      floorRetention *
        (scaleLoss * b ^ (scaleRatio ^ i)) ^ scaleRatio := by
  calc
    scaleLoss * b ^ (scaleRatio ^ (i + 1)) =
        scaleLoss * b ^ (scaleRatio ^ i * scaleRatio) := by rw [pow_succ]
    _ = (floorRetention * scaleLoss ^ scaleRatio) *
        b ^ (scaleRatio ^ i * scaleRatio) := by
      rw [floorRetention_mul_scaleLoss_rpow]
    _ = floorRetention *
        (scaleLoss ^ scaleRatio * b ^ (scaleRatio ^ i * scaleRatio)) := by ring
    _ = floorRetention *
        (scaleLoss * b ^ (scaleRatio ^ i)) ^ scaleRatio := by
      rw [Real.mul_rpow scaleLoss_nonneg (Real.rpow_nonneg hb _),
        ← Real.rpow_mul hb]

/-- Stable pointwise lower bound for every one of the eleven scales. -/
theorem scaleLoss_mul_base_rpow_le_iterScale {p : Nat}
    (hp : 10 ^ 156 ≤ p) {i : Nat} (hi : i ≤ 10) :
    scaleLoss *
        ((p : Real) / firstScaleDenominator) ^ (scaleRatio ^ i) ≤
      iterScale (firstScale p) i := by
  let b : Real := (p : Real) / firstScaleDenominator
  have hb : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg (Nat.cast_nonneg p) firstScaleDenominator_pos.le
  have hp₁ : 10 ^ 155 ≤ firstScale p :=
    ten_pow_oneFiftyFive_le_firstScale hp
  induction i with
  | zero =>
      simpa [b, iterScale] using
        scaleLoss_mul_main_div_denominator_le_firstScale hp
  | succ i ih =>
      have hi' : i ≤ 10 := Nat.le_trans (Nat.le_succ i) hi
      have hiFin : i < 11 := by omega
      have hLarge : 10 ^ 4 ≤ iterScale (firstScale p) i :=
        tenThousand_le_iterScale hp₁ ⟨i, hiFin⟩
      have hRec := floorRetention_mul_rpow_le_nextScale hLarge
      have hRpow :
          (scaleLoss * b ^ (scaleRatio ^ i)) ^ scaleRatio ≤
            (iterScale (firstScale p) i : Real) ^ scaleRatio :=
        Real.rpow_le_rpow (mul_nonneg scaleLoss_nonneg (Real.rpow_nonneg hb _))
          (ih hi') scaleRatio_nonneg
      calc
        scaleLoss * b ^ (scaleRatio ^ (i + 1)) =
            floorRetention *
              (scaleLoss * b ^ (scaleRatio ^ i)) ^ scaleRatio :=
          scaleLoss_mul_rpow_succ b hb i
        _ ≤ floorRetention *
            (iterScale (firstScale p) i : Real) ^ scaleRatio :=
          mul_le_mul_of_nonneg_left hRpow floorRetention_nonneg
        _ ≤ iterScale (firstScale p) (i + 1) := by
          simpa [iterScale] using hRec

/-- Multiplying the pointwise estimates collects the geometric exponent sum. -/
theorem scaleLoss_pow_eleven_mul_base_rpow_le_scaleProduct {p : Nat}
    (hp : 10 ^ 156 ≤ p) :
    scaleLoss ^ 11 *
        ((p : Real) / firstScaleDenominator) ^ scaleExponentSum ≤
      ∏ i : Fin 11, (digitScale (firstScale p) i : Real) := by
  have hPoint : ∀ i : Fin 11,
      scaleLoss *
          ((p : Real) / firstScaleDenominator) ^ (scaleRatio ^ (i : Nat)) ≤
        digitScale (firstScale p) i := by
    intro i
    exact scaleLoss_mul_base_rpow_le_iterScale hp (by omega)
  have hBase : 0 ≤ (p : Real) / firstScaleDenominator :=
    div_nonneg (Nat.cast_nonneg p) firstScaleDenominator_pos.le
  have hProd :
      (∏ i : Fin 11,
        scaleLoss *
          ((p : Real) / firstScaleDenominator) ^ (scaleRatio ^ (i : Nat))) ≤
        ∏ i : Fin 11, (digitScale (firstScale p) i : Real) := by
    exact Finset.prod_le_prod
      (fun i _ ↦ mul_nonneg scaleLoss_nonneg (Real.rpow_nonneg hBase _))
      (fun i _ ↦ hPoint i)
  have hCollect :
      (∏ i : Fin 11,
        scaleLoss *
          ((p : Real) / firstScaleDenominator) ^ (scaleRatio ^ (i : Nat))) =
        scaleLoss ^ 11 *
          ((p : Real) / firstScaleDenominator) ^ scaleExponentSum := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← Real.rpow_sum_of_nonneg hBase
      (fun _ _ ↦ pow_nonneg scaleRatio_nonneg _)]
    rw [Fin.sum_univ_eq_sum_range]
    rfl
  rw [← hCollect]
  exact hProd

/-- Exact geometric identity for Chen's exponent. -/
theorem scaleExponentSum_eq :
    scaleExponentSum = 5 - 5 * scaleRatio ^ 11 := by
  norm_num [scaleExponentSum, scaleRatio, Finset.sum_range_succ]

/-- The accumulated relative floor loss remains above `9/10`. -/
theorem nineTenths_le_scaleLoss_pow_eleven :
    (9 / 10 : Real) ≤ scaleLoss ^ 11 := by
  norm_num [scaleLoss, floorRetention]

/-- The fifth root of four is at most `4 / 3` for the product estimate. -/
lemma fifthRootFour_le_fourThirds : fifthRootFour ≤ (4 / 3 : Real) := by
  unfold fifthRootFour
  apply (Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num)
    (by norm_num : (0 : Real) < 5)).2
  norm_num [Real.rpow_natCast]

/-- A rational upper bound for the first-scale denominator. -/
theorem firstScaleDenominator_le_eightThirds :
    firstScaleDenominator ≤ (8 / 3 : Real) := by
  unfold firstScaleDenominator
  nlinarith [fifthRootFour_le_fourThirds]

/-- The geometric exponent sum is nonnegative. -/
lemma scaleExponentSum_nonneg : 0 ≤ scaleExponentSum := by
  apply Finset.sum_nonneg
  intro i _
  exact pow_nonneg scaleRatio_nonneg _

/-- The geometric exponent sum is at most `23 / 5`. -/
lemma scaleExponentSum_le_twentyThreeFifths :
    scaleExponentSum ≤ (23 / 5 : Real) := by
  norm_num [scaleExponentSum, scaleRatio, Finset.sum_range_succ]

private theorem eightThirds_rpow_twentyThreeFifths_le_hundred :
    (8 / 3 : Real) ^ (23 / 5 : Real) ≤ 100 := by
  have hRewrite :
      (8 / 3 : Real) ^ (23 / 5 : Real) =
        ((8 / 3 : Real) ^ 23) ^ ((5 : Real)⁻¹) := by
    rw [show (23 / 5 : Real) = 23 * (5 : Real)⁻¹ by ring,
      Real.rpow_mul (by norm_num)]
    exact congrArg (fun x : Real => x ^ ((5 : Real)⁻¹))
      (Real.rpow_natCast (8 / 3 : Real) 23)
  rw [hRewrite]
  apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num)
    (by norm_num : (0 : Real) < 5)).2
  norm_num [Real.rpow_natCast]

/-- The irrational first-scale denominator raised to the geometric exponent
costs at most a factor 100. -/
theorem firstScaleDenominator_rpow_scaleExponentSum_le_hundred :
    firstScaleDenominator ^ scaleExponentSum ≤ 100 := by
  calc
    firstScaleDenominator ^ scaleExponentSum ≤
        (8 / 3 : Real) ^ scaleExponentSum :=
      Real.rpow_le_rpow firstScaleDenominator_pos.le
        firstScaleDenominator_le_eightThirds scaleExponentSum_nonneg
    _ ≤ (8 / 3 : Real) ^ (23 / 5 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        scaleExponentSum_le_twentyThreeFifths
    _ ≤ 100 := eightThirds_rpow_twentyThreeFifths_le_hundred

/-- The fixed floor loss and denominator bounds together leave Chen's
`2^-7` scale-product factor. -/
theorem one_div_two_pow_seven_mul_rpow_le_floorLoss {p : Real}
    (hp : 0 ≤ p) :
    (1 / 2 ^ 7 : Real) * p ^ scaleExponentSum ≤
      scaleLoss ^ 11 *
        (p / firstScaleDenominator) ^ scaleExponentSum := by
  have hDenomPos : 0 < firstScaleDenominator ^ scaleExponentSum :=
    Real.rpow_pos_of_pos firstScaleDenominator_pos _
  have hCoefficient : (1 / 2 ^ 7 : Real) ≤
      scaleLoss ^ 11 / firstScaleDenominator ^ scaleExponentSum := by
    apply (le_div_iff₀ hDenomPos).2
    calc
      (1 / 2 ^ 7 : Real) *
          firstScaleDenominator ^ scaleExponentSum ≤
        (1 / 2 ^ 7 : Real) * 100 :=
          mul_le_mul_of_nonneg_left
            firstScaleDenominator_rpow_scaleExponentSum_le_hundred
            (by norm_num)
      _ ≤ (9 / 10 : Real) := by norm_num
      _ ≤ scaleLoss ^ 11 := nineTenths_le_scaleLoss_pow_eleven
  rw [Real.div_rpow hp firstScaleDenominator_pos.le]
  calc
    (1 / 2 ^ 7 : Real) * p ^ scaleExponentSum ≤
        (scaleLoss ^ 11 / firstScaleDenominator ^ scaleExponentSum) *
          p ^ scaleExponentSum :=
      mul_le_mul_of_nonneg_right hCoefficient (Real.rpow_nonneg hp _)
    _ = scaleLoss ^ 11 *
        (p ^ scaleExponentSum /
          firstScaleDenominator ^ scaleExponentSum) := by ring

/-- Chen's exact `2^-7` lower bound for the product of the eleven scales. -/
theorem one_div_two_pow_seven_mul_main_rpow_le_scaleProduct {p : Nat}
    (hp : 10 ^ 156 ≤ p) :
    (1 / 2 ^ 7 : Real) *
        (p : Real) ^ (5 - 5 * scaleRatio ^ 11) ≤
      ∏ i : Fin 11, (digitScale (firstScale p) i : Real) := by
  rw [← scaleExponentSum_eq]
  exact (one_div_two_pow_seven_mul_rpow_le_floorLoss (Nat.cast_nonneg p)).trans
    (scaleLoss_pow_eleven_mul_base_rpow_le_scaleProduct hp)

/-- Full source lower bound for the number of distinct eleven-coordinate
fifth-power sums. -/
theorem chenDigitSums_card_lower {N : Nat} (hN : 10 ^ 780 ≤ N) :
    (17 / 10 : Real) / 2 ^ 17 *
        (mainScale N : Real) ^ (5 - 5 * scaleRatio ^ 11) ≤
      ((chenDigitSums (firstScale (mainScale N))).card : Real) := by
  have hp : 10 ^ 156 ≤ mainScale N := ten_pow_oneFiftySix_le_mainScale hN
  have hp₁ : 10 ^ 155 ≤ firstScale (mainScale N) :=
    ten_pow_oneFiftyFive_le_firstScale hp
  have hScale := one_div_two_pow_seven_mul_main_rpow_le_scaleProduct hp
  have hCount := digitScale_product_le_card_chenDigitSums hp₁
  calc
    (17 / 10 : Real) / 2 ^ 17 *
        (mainScale N : Real) ^ (5 - 5 * scaleRatio ^ 11) =
      ((17 / 10 : Real) / 2 ^ 10) *
        ((1 / 2 ^ 7 : Real) *
          (mainScale N : Real) ^ (5 - 5 * scaleRatio ^ 11)) := by ring
    _ ≤ ((17 / 10 : Real) / 2 ^ 10) *
        (∏ i : Fin 11,
          (digitScale (firstScale (mainScale N)) i : Real)) :=
      mul_le_mul_of_nonneg_left hScale (by norm_num)
    _ ≤ ((chenDigitSums (firstScale (mainScale N))).card : Real) := hCount

end

end Waring.LargeNumber
