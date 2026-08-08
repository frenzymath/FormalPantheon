import Waring.Analytic.ChenTenMajorArcSum
import Waring.Analytic.ChenTenSingularIntegral
import Waring.Analytic.ChenTenSingularSeriesReindex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate
open Set MeasureTheory

noncomputable section

/-!
# Finite singular-integral comparison on Chen's reduced arcs

This file identifies the indexed reduced-arc singular terms with Chen's
finite singular-series truncation and bounds the error from replacing each
centered truncated kernel by the whole-line singular integral.
-/

private def invDenWeight (q : Nat) : Real := (q : Real)⁻¹

private theorem sum_invDenWeight_fiber_le_one (P q : Nat) :
    (∑ i ∈ chenTenArcDenominatorFiber P q, invDenWeight i.denominator) ≤ 1 := by
  let fiber := chenTenArcDenominatorFiber P q
  have hcardNat : fiber.card ≤ q :=
    (card_chenTenArcDenominatorFiber_le_totient P q).trans (Nat.totient_le q)
  have hcardReal : (fiber.card : Real) ≤ q := by exact_mod_cast hcardNat
  by_cases hq : q = 0
  · subst q
    have hfiber : fiber = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcardNat)
    simp [fiber] at hfiber
    simp [invDenWeight, hfiber]
  · have hqpos : (0 : Real) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    calc
      (∑ i ∈ fiber, invDenWeight i.denominator) =
          ∑ _i ∈ fiber, (q : Real)⁻¹ := by
        apply Finset.sum_congr
        · rfl
        · intro i hi
          have hiq : i.denominator = q := (Finset.mem_filter.mp hi).2
          simp [invDenWeight, hiq]
      _ = (fiber.card : Real) * (q : Real)⁻¹ := by simp
      _ ≤ (q : Real) * (q : Real)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hcardReal (inv_nonneg.mpr hqpos.le)
      _ = 1 := by field_simp

private theorem sum_invDenWeight_eq_fibers (P : Nat) :
    (∑ i : ChenTenArcIndex P, invDenWeight i.denominator) =
      ∑ q ∈ Finset.range (Nat.sqrt P + 1),
        ∑ i ∈ (Finset.univ : Finset (ChenTenArcIndex P)) with
          i.denominator = q, invDenWeight i.denominator := by
  have hmap : ∀ i ∈ (Finset.univ : Finset (ChenTenArcIndex P)),
      i.denominator ∈ Finset.range (Nat.sqrt P + 1) := by
    intro i hi
    rw [Finset.mem_range]
    have hqS : i.denominator ≤ Nat.sqrt P := by
      rw [Nat.le_sqrt]
      simpa [pow_two] using i.denominator_sq_le
    omega
  symm
  exact Finset.sum_fiberwise_of_maps_to hmap
    (fun i : ChenTenArcIndex P => invDenWeight i.denominator)

private theorem sum_invDenWeight_le_sqrt (P : Nat) :
    (∑ i : ChenTenArcIndex P, invDenWeight i.denominator) ≤
      (Nat.sqrt P : Real) := by
  rw [sum_invDenWeight_eq_fibers]
  rw [Finset.sum_range_succ']
  have hzeroSum :
      (∑ i ∈ (Finset.univ : Finset (ChenTenArcIndex P)) with
          i.denominator = 0, invDenWeight i.denominator) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiq : i.denominator = 0 := (Finset.mem_filter.mp hi).2
    exact False.elim ((Nat.ne_of_gt i.denominator_pos) hiq)
  rw [hzeroSum, add_zero]
  calc
    (∑ k ∈ Finset.range (Nat.sqrt P),
        let q := k + 1
        ∑ i ∈ (Finset.univ : Finset (ChenTenArcIndex P)) with
          i.denominator = q, invDenWeight i.denominator) ≤
      ∑ _k ∈ Finset.range (Nat.sqrt P), (1 : Real) := by
        apply Finset.sum_le_sum
        intro k hk
        change (∑ i ∈ chenTenArcDenominatorFiber P (k + 1),
          invDenWeight i.denominator) ≤ 1
        exact sum_invDenWeight_fiber_le_one P (k + 1)
    _ = (Nat.sqrt P : Real) := by simp

private theorem norm_indexed_singular_term_le
    (N : Nat) {P : Nat} (i : ChenTenArcIndex P) :
    ‖chenTenIndexedSingularTerm N i‖ ≤
      (40 : Real) ^ 15 * (i.denominator : Real) ^ (-3 : Real) := by
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have hsum := chen_two_completePowerSum_bound
    (i.numerator : ZMod i.denominator) i.numerator_isUnit
  unfold chenTenIndexedSingularTerm chenTenSingularTerm
  rw [norm_mul, norm_pow, norm_div, Complex.norm_natCast,
    norm_stdAddChar]
  have hquot :
      ‖completePowerSum 5 (i.numerator : ZMod i.denominator)‖ /
          (i.denominator : Real) ≤
        40 * (i.denominator : Real) ^ (-1 / 5 : Real) := by
    calc
      ‖completePowerSum 5 (i.numerator : ZMod i.denominator)‖ /
          (i.denominator : Real) ≤
        (40 * (i.denominator : Real) ^ (4 / 5 : Real)) /
          (i.denominator : Real) := by
        exact div_le_div_of_nonneg_right hsum hq.le
      _ = 40 * (i.denominator : Real) ^ (-1 / 5 : Real) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        calc
          40 * (i.denominator : Real) ^ (4 / 5 : Real) *
              (i.denominator : Real) ^ (-1 : Real) =
            40 * ((i.denominator : Real) ^ (4 / 5 : Real) *
              (i.denominator : Real) ^ (-1 : Real)) := by ring
          _ = 40 * (i.denominator : Real) ^ (-1 / 5 : Real) := by
            rw [← Real.rpow_add hq]
            norm_num
  have hpow :
      ((i.denominator : Real) ^ (-1 / 5 : Real)) ^ (15 : Nat) =
        (i.denominator : Real) ^ (-3 : Real) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num
  calc
    (‖completePowerSum 5 (i.numerator : ZMod i.denominator)‖ /
        (i.denominator : Real)) ^ 15 * 1 ≤
      (40 * (i.denominator : Real) ^ (-1 / 5 : Real)) ^ 15 :=
      by simpa using pow_le_pow_left₀ (by positivity) hquot 15
    _ = (40 : Real) ^ 15 *
        (i.denominator : Real) ^ (-3 : Real) := by
      rw [mul_pow, hpow]

private theorem norm_indexed_singular_term_mul_inv_tail_le
    (P N : Nat) (i : ChenTenArcIndex P)
    (tail : Complex) (htail : ‖tail‖ ≤
      (100 * 2 ^ 15 : Real) * (i.denominator : Real) ^ 2 *
        (P : Real) ^ 8) :
    ‖chenTenIndexedSingularTerm N i * tail‖ ≤
      (100 * 80 ^ 15 : Real) *
        (i.denominator : Real)⁻¹ * (P : Real) ^ 8 := by
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have hterm := norm_indexed_singular_term_le N i
  calc
    ‖chenTenIndexedSingularTerm N i * tail‖ =
        ‖chenTenIndexedSingularTerm N i‖ * ‖tail‖ := norm_mul _ _
    _ ≤ ((40 : Real) ^ 15 * (i.denominator : Real) ^ (-3 : Real)) *
        ((100 * 2 ^ 15 : Real) * (i.denominator : Real) ^ 2 *
          (P : Real) ^ 8) := by gcongr
    _ = (100 * 80 ^ 15 : Real) *
        (i.denominator : Real)⁻¹ * (P : Real) ^ 8 := by
      have hqpow :
          (i.denominator : Real) ^ (-3 : Real) *
              (i.denominator : Real) ^ (2 : Real) =
            (i.denominator : Real) ^ (-1 : Real) := by
        rw [← Real.rpow_add hq]
        norm_num
      calc
        (40 : Real) ^ 15 * (i.denominator : Real) ^ (-3 : Real) *
            ((100 * 2 ^ 15 : Real) * (i.denominator : Real) ^ 2 *
              (P : Real) ^ 8) =
          (40 : Real) ^ 15 * (100 * 2 ^ 15 : Real) *
            ((i.denominator : Real) ^ (-3 : Real) *
              (i.denominator : Real) ^ (2 : Real)) * (P : Real) ^ 8 := by
          norm_num
          ring
        _ = (40 : Real) ^ 15 * (100 * 2 ^ 15 : Real) *
            (i.denominator : Real) ^ (-1 : Real) * (P : Real) ^ 8 := by
          rw [hqpow]
        _ = (100 * 80 ^ 15 : Real) *
            (i.denominator : Real)⁻¹ * (P : Real) ^ 8 := by
          rw [show (i.denominator : Real) ^ (-1 : Real) =
              (i.denominator : Real)⁻¹ by exact Real.rpow_neg_one _]
          ring

private theorem natSqrt_le_rpow_half (P : Nat) :
    (Nat.sqrt P : Real) ≤ (P : Real) ^ (1 / 2 : Real) := by
  have hsqNat : Nat.sqrt P ^ 2 ≤ P := by
    simpa [pow_two] using Nat.sqrt_le P
  have hsq : (Nat.sqrt P : Real) ^ (2 : Real) ≤ (P : Real) := by
    calc
      (Nat.sqrt P : Real) ^ (2 : Real) = (Nat.sqrt P : Real) ^ (2 : Nat) :=
        Real.rpow_ofNat _ 2
      _ ≤ (P : Real) := by exact_mod_cast hsqNat
  have hnonneg : (0 : Real) ≤ Nat.sqrt P := by positivity
  calc
    (Nat.sqrt P : Real) =
        ((Nat.sqrt P : Real) ^ (2 : Real)) ^ (1 / 2 : Real) := by
      rw [← Real.rpow_mul hnonneg]
      norm_num
    _ ≤ (P : Real) ^ (1 / 2 : Real) := by
      exact Real.rpow_le_rpow (by positivity) hsq (by norm_num)

/-- A centered truncated singular integral differs from the whole-line integral by its tail. -/
theorem norm_chenTenTruncatedSingularIntegral_sub_full_le
    {P N : Nat} (hP : 1 ≤ P) (i : ChenTenArcIndex P) :
    ‖chenTenTruncatedSingularIntegral P N i -
        chenTenSingularIntegral P N‖ ≤
      (100 * 2 ^ 15 : Real) * (i.denominator : Real) ^ 2 *
        (P : Real) ^ 8 := by
  have hPpos : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_of_lt hP
  have hr := chenTenMajorArcRadius_pos (Nat.zero_lt_of_lt hP) i
  have htail := norm_chenTenSingularIntegral_sub_intervalIntegral_le
    P N hr
  have htail' :
      ‖(∫ z in -chenTenMajorArcRadius P i..
          chenTenMajorArcRadius P i,
          chenTenSingularIntegralKernel P N z) -
        chenTenSingularIntegral P N‖ ≤
        (2 : Real) ^ 15 *
          (chenTenMajorArcRadius P i) ^ (-2 : Real) := by
    simpa only [norm_sub_rev] using htail
  rw [chenTenMajorArcRadius_eq_pointwiseRadius]
    at htail'
  change ‖chenTenTruncatedSingularIntegral P N i -
      chenTenSingularIntegral P N‖ ≤ _
  rw [show chenTenTruncatedSingularIntegral P N i =
      (∫ z in -chenTenMajorArcRadius P i..
        chenTenMajorArcRadius P i,
        chenTenSingularIntegralKernel P N z) by rfl]
  rw [chenTenMajorArcRadius_eq_pointwiseRadius]
  calc
    ‖(∫ z in -(1 / (10 * (i.denominator : Real) * (P : Real) ^ 4))..
          1 / (10 * (i.denominator : Real) * (P : Real) ^ 4),
          chenTenSingularIntegralKernel P N z) -
        chenTenSingularIntegral P N‖ ≤
      (2 : Real) ^ 15 *
        (1 / (10 * (i.denominator : Real) * (P : Real) ^ 4)) ^
          (-2 : Real) := htail'
    _ = (100 * 2 ^ 15 : Real) * (i.denominator : Real) ^ 2 *
        (P : Real) ^ 8 := by
      have hq : (0 : Real) < i.denominator := by
        exact_mod_cast i.denominator_pos
      have hbase : (0 : Real) <
          10 * (i.denominator : Real) * (P : Real) ^ 4 := by positivity
      rw [show (1 / (10 * (i.denominator : Real) * (P : Real) ^ 4)) ^
          (-2 : Real) =
          (10 * (i.denominator : Real) * (P : Real) ^ 4) ^
            (2 : Real) by
            rw [one_div]
            rw [Real.inv_rpow hbase.le]
            rw [Real.rpow_neg (by positivity)]
            simp]
      norm_num
      ring

/-- Summing indexed singular terms against bounded tails gives the explicit aggregate error. -/
theorem norm_sum_chenTenIndexedSingularTerm_mul_tail_le
    {P N : Nat} (hP : 1 ≤ P)
    (tail : ChenTenArcIndex P → Complex)
    (htail : ∀ i,
      ‖tail i‖ ≤ (100 * 2 ^ 15 : Real) *
        (i.denominator : Real) ^ 2 * (P : Real) ^ 8) :
    ‖∑ i : ChenTenArcIndex P,
        chenTenIndexedSingularTerm N i * tail i‖ ≤
      4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) := by
  have hPpos : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_of_lt hP
  have hsumInv := sum_invDenWeight_le_sqrt P
  calc
    ‖∑ i : ChenTenArcIndex P,
        chenTenIndexedSingularTerm N i * tail i‖ ≤
      ∑ i : ChenTenArcIndex P,
        ‖chenTenIndexedSingularTerm N i * tail i‖ := norm_sum_le _ _
    _ ≤ ∑ i : ChenTenArcIndex P,
        (100 * 80 ^ 15 : Real) *
          (i.denominator : Real)⁻¹ * (P : Real) ^ 8 := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_indexed_singular_term_mul_inv_tail_le P N i
        (tail i) (htail i)
    _ = ((100 * 80 ^ 15 : Real) * (P : Real) ^ 8) *
        (∑ i : ChenTenArcIndex P, invDenWeight i.denominator) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold invDenWeight
      ring
    _ ≤ ((100 * 80 ^ 15 : Real) * (P : Real) ^ 8) *
        (Nat.sqrt P : Real) := by
      exact mul_le_mul_of_nonneg_left hsumInv (by positivity)
    _ ≤ ((100 * 80 ^ 15 : Real) * (P : Real) ^ 8) *
        (P : Real) ^ (1 / 2 : Real) := by
      gcongr
      exact natSqrt_le_rpow_half P
    _ = (100 * 80 ^ 15 : Real) *
        (P : Real) ^ (17 / 2 : Real) := by
      calc
        ((100 * 80 ^ 15 : Real) * (P : Real) ^ 8) *
            (P : Real) ^ (1 / 2 : Real) =
          (100 * 80 ^ 15 : Real) *
            ((P : Real) ^ (8 : Real) * (P : Real) ^ (1 / 2 : Real)) := by
              rw [Real.rpow_ofNat]
              ring
        _ = (100 * 80 ^ 15 : Real) *
            (P : Real) ^ (17 / 2 : Real) := by
              rw [← Real.rpow_add hPpos]
              norm_num
    _ ≤ 4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) := by
      have hconst : (100 * 80 ^ 15 : Real) ≤ 4 * (10 : Real) ^ 30 := by
        norm_num
      exact mul_le_mul_of_nonneg_right hconst
        (Real.rpow_nonneg (by positivity) _)

/-- Distributing the singular-series sum rewrites truncated-minus-full terms pointwise. -/
theorem sum_chenTenIndexedTruncated_sub_full_mul_sum
    {P N : Nat} :
    (∑ i : ChenTenArcIndex P,
        chenTenIndexedSingularTerm N i *
          chenTenTruncatedSingularIntegral P N i) -
      chenTenSingularIntegral P N *
        (∑ i : ChenTenArcIndex P, chenTenIndexedSingularTerm N i) =
      ∑ i : ChenTenArcIndex P,
        chenTenIndexedSingularTerm N i *
          (chenTenTruncatedSingularIntegral P N i -
            chenTenSingularIntegral P N) := by
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end
end Waring.Analytic
