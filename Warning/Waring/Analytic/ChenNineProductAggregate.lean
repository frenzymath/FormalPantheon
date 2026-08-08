import Waring.Analytic.ChenNineProductScale
import Waring.Analytic.ChenNineReducedGrid
import Waring.Analytic.ProductMajorantSum
import Waring.Analytic.WeightedThresholdSplit

/-!
# Direct product aggregation in Chen's Lemma 9

This file combines the bounded-product fifth moment, reduced rational grid,
and direct product-fiber second moment.
-/

namespace Waring.Analytic

open scoped BigOperators

private theorem diophantineMinWeight_le_length
    (q P : Nat) [NeZero q] (x : ZMod q) :
    diophantineMinWeight q P x ≤ P := by
  by_cases hx : x = 0
  · simp [diophantineMinWeight, hx]
  · rw [diophantineMinWeight, if_neg hx]
    exact min_le_left _ _

/-- The product-count-weighted Diophantine sum is bounded at the common
fifth-root scale. -/
theorem sum_boundedProductCount_mul_diophantineMinWeight_le
    {P q : Nat} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4) :
    (∑ m ∈ Finset.Icc 1 ((P ^ 3 / 27) * P),
        (boundedProductCount (P ^ 3 / 27) P m : Real) *
          diophantineMinWeight q P
            (-(a * (120 * (m : ZMod q))))) ≤
      ((81 / 16 : Real) + 297 / 28) * chenNineProductScale P := by
  let A := P ^ 3 / 27
  let support := Finset.Icc 1 (A * P)
  let count : Nat → Real := fun m ↦ boundedProductCount A P m
  let weight : Nat → Real := fun m ↦
    diophantineMinWeight q P (-(a * (120 * (m : ZMod q))))
  let H := chenNineProductThreshold P
  have hPone : 1 ≤ P :=
    (by norm_num : 1 ≤ (10 : Nat) ^ 150).trans hP
  have hPthree : 3 ≤ P :=
    (by norm_num : 3 ≤ (10 : Nat) ^ 150).trans hP
  have hH : 0 < H := chenNineProductThreshold_pos hPone
  have hsplit := sum_mul_le_fifthMoment_threshold support count weight
    (P : Real) H (by positivity) hH
    (fun _ _ ↦ by dsimp [count]; positivity)
    (fun m _ ↦ diophantineMinWeight_nonneg q P _)
    (fun m _ ↦ diophantineMinWeight_le_length q P _)
  have hmoment := sum_boundedProductCount_pow_five_le_scale hPthree
  change
    ((∑ m ∈ Finset.Icc 1 (A * P),
        boundedProductCount A P m ^ 5 : Nat) : Real) ≤ _ at hmoment
  simp only [Nat.cast_sum, Nat.cast_pow] at hmoment
  have hgrid := sum_restrictedProduct_diophantineMinWeight_le
    a ha hP hqLower hqUpper
  change (∑ m ∈ support, weight m) ≤
    40 * (P : Real) ^ 4 * (Real.log P + 4) at hgrid
  change (∑ m ∈ support, count m * weight m) ≤ _
  calc
    ∑ m ∈ support, count m * weight m ≤
        (P : Real) * (H ^ 4)⁻¹ *
            ∑ m ∈ support, count m ^ 5 +
          H * ∑ m ∈ support, weight m := hsplit
    _ ≤ (P : Real) * (H ^ 4)⁻¹ *
          ((3 : Real) ^ 12 / (24 * 192) ^ 2 * (P : Real) ^ 4 *
            (Real.log P + 4) ^ 30) +
        H * (40 * (P : Real) ^ 4 * (Real.log P + 4)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hmoment (by positivity)
      · exact mul_le_mul_of_nonneg_left hgrid hH.le
    _ ≤ (81 / 16 : Real) * chenNineProductScale P +
        (297 / 28 : Real) * chenNineProductScale P := by
      apply add_le_add
      · exact le_of_eq (chenNine_highProduct_identity hPone)
      · exact chenNine_lowProduct_le hPone
    _ = ((81 / 16 : Real) + 297 / 28) * chenNineProductScale P := by ring

/-- The sum of all fourth-difference product majorants is controlled by the
same scale, including the diagonal term. -/
theorem sum_fifthProductMajorant_le
    {P q : Nat} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4) :
    ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27), fifthProductMajorant a P z ≤
      2 * (1 / 54 + 81 / 16 + 297 / 28 : Real) *
        chenNineProductScale P := by
  have hPone : 1 ≤ P :=
    (by norm_num : 1 ≤ (10 : Nat) ^ 150).trans hP
  have hweighted :=
    sum_boundedProductCount_mul_diophantineMinWeight_le
      a ha hP hqLower hqUpper
  have hendpoint := restrictedProductEndpoint_cast_le P
  have hpowScale := pow_four_le_chenNineProductScale hPone
  have hdiag : ((P ^ 3 / 27 : Nat) : Real) * P ≤
      (1 / 27 : Real) * chenNineProductScale P := by
    have hcast : ((P ^ 3 / 27 : Nat) : Real) * P ≤
        (P : Real) ^ 4 / 27 := by
      simpa only [Nat.cast_mul] using hendpoint
    calc
      ((P ^ 3 / 27 : Nat) : Real) * P ≤
          (P : Real) ^ 4 / 27 := hcast
      _ ≤ chenNineProductScale P / 27 := by gcongr
      _ = (1 / 27 : Real) * chenNineProductScale P := by ring
  rw [sum_fifthProductMajorant_eq]
  calc
    ((P ^ 3 / 27 : Nat) : Real) * P + 2 *
        ∑ m ∈ Finset.Icc 1 ((P ^ 3 / 27) * P),
          (boundedProductCount (P ^ 3 / 27) P m : Real) *
            diophantineMinWeight q P
              (-(a * (120 * (m : ZMod q)))) ≤
        (1 / 27 : Real) * chenNineProductScale P +
          2 * (((81 / 16 : Real) + 297 / 28) *
            chenNineProductScale P) := by gcongr
    _ = 2 * (1 / 54 + 81 / 16 + 297 / 28 : Real) *
        chenNineProductScale P := by ring

private theorem chenNine_lengthScale_eq_rpow {P : Nat} (hP : 0 < P) :
    (P : Real) ^ 7 * chenNineLengthRoot P =
      (P : Real) ^ (36 / 5 : Real) := by
  unfold chenNineLengthRoot
  rw [← Real.rpow_natCast (P : Real) 7]
  rw [← Real.rpow_add (by exact_mod_cast hP : (0 : Real) < P)]
  norm_num

private theorem chenNine_logScale_eq_rpow {P : Nat} (hP : 1 ≤ P) :
    chenNineLogRoot P ^ 74 =
      (Real.log P + 4) ^ (74 / 5 : Real) := by
  unfold chenNineLogRoot
  have hbase : 0 ≤ Real.log P + 4 := by
    have hlog : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
    linarith
  rw [← Real.rpow_mul_natCast hbase]
  norm_num

/-- The complete direct product-fiber aggregate has constant `160` and the
source-facing real exponents `36/5` and `74/5`. -/
theorem sq_sum_restrictedQuadraticValue_le_direct
    {P q : Nat} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4) :
    (∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
        ∑ x ∈ restrictedTripleDivisorChoices P z,
          restrictedQuadraticValue a P z x) ^ 2 ≤
      160 * (P : Real) ^ (36 / 5 : Real) *
        (Real.log P + 4) ^ (74 / 5 : Real) := by
  have hPone : 1 ≤ P :=
    (by norm_num : 1 ≤ (10 : Nat) ^ 150).trans hP
  have hPthree : 3 ≤ P :=
    (by norm_num : 3 ≤ (10 : Nat) ^ 150).trans hP
  have hPpos : 0 < P := by omega
  have hlog : 0 ≤ Real.log P :=
    Real.log_nonneg (by exact_mod_cast hPone)
  have hmajorant := sum_fifthProductMajorant_le a ha hP hqLower hqUpper
  have hfiber := sq_sum_restrictedQuadraticValue_le a hPthree
  have hscaleNonneg := chenNineProductScale_nonneg P
  have hlogPow := chenNineLogRoot_pow_five hPone
  calc
    (∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
        ∑ x ∈ restrictedTripleDivisorChoices P z,
          restrictedQuadraticValue a P z x) ^ 2 ≤
        ((81 : Real) / 16 * (P : Real) ^ 3 *
          (Real.log P + 2) ^ 8) *
            ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
              fifthProductMajorant a P z := hfiber
    _ ≤ ((81 : Real) / 16 * (P : Real) ^ 3 *
          (Real.log P + 2) ^ 8) *
        (2 * (1 / 54 + 81 / 16 + 297 / 28 : Real) *
          chenNineProductScale P) := by
      exact mul_le_mul_of_nonneg_left hmajorant (by positivity)
    _ = ((81 : Real) / 8 *
          (1 / 54 + 81 / 16 + 297 / 28)) *
        ((P : Real) ^ 3 * (Real.log P + 2) ^ 8 *
          chenNineProductScale P) := by ring
    _ ≤ ((81 : Real) / 8 *
          (1 / 54 + 81 / 16 + 297 / 28)) *
        ((P : Real) ^ 3 * (Real.log P + 4) ^ 8 *
          chenNineProductScale P) := by
      have hlogPowLe : (Real.log P + 2) ^ 8 ≤
          (Real.log P + 4) ^ 8 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 8
      gcongr
    _ ≤ 160 * ((P : Real) ^ 3 * (Real.log P + 4) ^ 8 *
          chenNineProductScale P) := by
      exact mul_le_mul_of_nonneg_right
        (le_of_lt chenNine_productAggregate_coefficient_lt)
        (mul_nonneg
          (mul_nonneg (pow_nonneg (by positivity : (0 : Real) ≤ P) 3)
            (pow_nonneg (by linarith : 0 ≤ Real.log P + 4) 8))
          hscaleNonneg)
    _ = 160 * ((P : Real) ^ 7 * chenNineLengthRoot P) *
          chenNineLogRoot P ^ 74 := by
      unfold chenNineProductScale
      rw [← hlogPow]
      ring
    _ = 160 * (P : Real) ^ (36 / 5 : Real) *
          (Real.log P + 4) ^ (74 / 5 : Real) := by
      rw [chenNine_lengthScale_eq_rpow hPpos,
        chenNine_logScale_eq_rpow hPone]

end Waring.Analytic
