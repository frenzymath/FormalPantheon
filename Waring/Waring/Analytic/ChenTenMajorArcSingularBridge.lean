import Waring.Analytic.ChenTenSingularIntegralComparison
import Waring.Analytic.ChenTenSingularSeriesTail

/-!
# Full singular-series comparison on Chen's major arcs

This module adds the convergent singular-series tail to the finite indexed
major-arc comparison.
-/

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate
open Set MeasureTheory

noncomputable section

/-- The finite major-arc sum differs from the partial singular-series model by explicit errors. -/
theorem norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_partial_le
    {P N : Nat} (hP : 1 ≤ P) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N *
          chenTenSingularSeriesPartial N (Nat.sqrt P)‖ ≤
      5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) := by
  have hmajor :=
    norm_sum_setIntegral_chenTenRepresentationIntegrand_sub_singular_le_decay
      hP N
  have htailAgg := norm_sum_chenTenIndexedSingularTerm_mul_tail_le (P := P) (N := N)
    hP (fun i => chenTenTruncatedSingularIntegral P N i -
      chenTenSingularIntegral P N)
    (fun i => norm_chenTenTruncatedSingularIntegral_sub_full_le hP i)
  have hsumEq :=
    sum_chenTenIndexedSingularTerm_eq_chenTenSingularSeriesPartial P N
  have hbridge :
      (∑ i : ChenTenArcIndex P,
          chenTenIndexedSingularTerm N i *
            chenTenTruncatedSingularIntegral P N i) -
        chenTenSingularIntegral P N *
          chenTenSingularSeriesPartial N (Nat.sqrt P) =
      ∑ i : ChenTenArcIndex P,
          chenTenIndexedSingularTerm N i *
            (chenTenTruncatedSingularIntegral P N i -
              chenTenSingularIntegral P N) := by
    rw [← hsumEq]
    exact sum_chenTenIndexedTruncated_sub_full_mul_sum
  calc
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N *
          chenTenSingularSeriesPartial N (Nat.sqrt P)‖ =
      ‖((∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
          ∑ i : ChenTenArcIndex P,
            chenTenIndexedSingularTerm N i *
              chenTenTruncatedSingularIntegral P N i) +
        ((∑ i : ChenTenArcIndex P,
            chenTenIndexedSingularTerm N i *
              chenTenTruncatedSingularIntegral P N i) -
          chenTenSingularIntegral P N *
            chenTenSingularSeriesPartial N (Nat.sqrt P))‖ := by
      congr 1
      ring
    _ ≤ ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
          ∑ i : ChenTenArcIndex P,
            chenTenIndexedSingularTerm N i *
              chenTenTruncatedSingularIntegral P N i‖ +
        ‖∑ i : ChenTenArcIndex P,
            chenTenIndexedSingularTerm N i *
              (chenTenTruncatedSingularIntegral P N i -
                chenTenSingularIntegral P N)‖ := by
      rw [hbridge]
      exact norm_add_le _ _
    _ ≤ 5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) :=
      add_le_add hmajor htailAgg

/-- Adding the finite singular-series tail gives the full-series comparison bound. -/
theorem norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_series_le
    {P N : Nat} (hP : 1 ≤ P) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N * chenTenSingularSeries N‖ ≤
      5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) +
        ‖chenTenSingularIntegral P N‖ *
          (2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real)) := by
  have hpartial :=
    norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_partial_le
      (P := P) (N := N) hP
  have hseries := norm_chenTenSingularSeries_sub_partial_le N (Nat.sqrt P)
  calc
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N * chenTenSingularSeries N‖ =
      ‖((∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
          chenTenSingularIntegral P N *
            chenTenSingularSeriesPartial N (Nat.sqrt P)) +
        chenTenSingularIntegral P N *
          (chenTenSingularSeriesPartial N (Nat.sqrt P) -
            chenTenSingularSeries N)‖ := by
      congr 1
      ring
    _ ≤ ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
          chenTenSingularIntegral P N *
            chenTenSingularSeriesPartial N (Nat.sqrt P)‖ +
        ‖chenTenSingularIntegral P N‖ *
          ‖chenTenSingularSeriesPartial N (Nat.sqrt P) -
            chenTenSingularSeries N‖ := by
      exact norm_add_le _ _ |>.trans_eq (by rw [norm_mul])
    _ ≤ 5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) +
        ‖chenTenSingularIntegral P N‖ *
          (2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real)) := by
      have hseries' :
          ‖chenTenSingularSeriesPartial N (Nat.sqrt P) -
              chenTenSingularSeries N‖ ≤
            2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real) := by
        simpa only [norm_sub_rev] using hseries
      have hR : 0 ≤ ‖chenTenSingularIntegral P N‖ := norm_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hseries' hR
      linarith [hpartial, hmul]

private theorem natSqrt_add_one_inv_le_rpow_neg_half
    {P : Nat} (hP : 1 ≤ P) :
    (Nat.sqrt P + 1 : Real)⁻¹ ≤ (P : Real) ^ (-1 / 2 : Real) := by
  have hPpos : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_of_lt hP
  have hspos : (0 : Real) < (Nat.sqrt P : Real) + 1 := by positivity
  have hsq : (P : Real) ≤ ((Nat.sqrt P : Real) + 1) ^ 2 := by
    have hnat := Nat.lt_succ_sqrt P
    have hcast : (P : Real) <
        ((Nat.sqrt P).succ : Real) * ((Nat.sqrt P).succ : Real) := by
      exact_mod_cast hnat
    simpa [Nat.succ_eq_add_one, pow_two] using hcast.le
  have hsq' : (P : Real) ≤ ((Nat.sqrt P : Real) + 1) ^ (2 : Real) := by
    simpa only [Real.rpow_ofNat] using hsq
  have hsqrt : (P : Real) ^ (1 / 2 : Real) ≤
      (Nat.sqrt P : Real) + 1 := by
    calc
      (P : Real) ^ (1 / 2 : Real) ≤
          (((Nat.sqrt P : Real) + 1) ^ (2 : Real)) ^
            (1 / 2 : Real) := by
        exact Real.rpow_le_rpow (by positivity) hsq' (by norm_num)
      _ = (Nat.sqrt P : Real) + 1 := by
        rw [← Real.rpow_mul hspos.le]
        norm_num
  have hinv : ((Nat.sqrt P : Real) + 1)⁻¹ ≤
      ((P : Real) ^ (1 / 2 : Real))⁻¹ := by
    exact (inv_le_inv₀ hspos (by positivity)).2 hsqrt
  calc
    (Nat.sqrt P + 1 : Real)⁻¹ ≤
        ((P : Real) ^ (1 / 2 : Real))⁻¹ := hinv
    _ = (P : Real) ^ (-1 / 2 : Real) := by
      rw [← Real.rpow_neg (by positivity)]
      congr 1
      ring

private theorem singularSeries_tail_coefficient_le_rpow
    {P : Nat} (hP : 1 ≤ P) :
    2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real) ≤
      (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) := by
  have hconst : 2 * (40 : Real) ^ 15 ≤ (10 : Real) ^ 30 := by
    norm_num
  have hinv := natSqrt_add_one_inv_le_rpow_neg_half hP
  calc
    2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real) =
        (2 * (40 : Real) ^ 15) * (Nat.sqrt P + 1 : Real)⁻¹ := by
      ring
    _ ≤ (2 * (40 : Real) ^ 15) *
        (P : Real) ^ (-1 / 2 : Real) := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) := by
      exact mul_le_mul_of_nonneg_right hconst
        (Real.rpow_nonneg (by positivity) _)

/-- The source-scale tail comparison retains the singular-integral norm term. -/
theorem norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_series_le_source_tail
    {P N : Nat} (hP : 1 ≤ P) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N * chenTenSingularSeries N‖ ≤
      5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) +
        (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) *
          ‖chenTenSingularIntegral P N‖ := by
  have hraw := norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_series_le
    (P := P) (N := N) hP
  have hcoef := singularSeries_tail_coefficient_le_rpow hP
  have hmul := mul_le_mul_of_nonneg_left hcoef
    (norm_nonneg (chenTenSingularIntegral P N))
  calc
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N * chenTenSingularSeries N‖ ≤
      5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) +
        ‖chenTenSingularIntegral P N‖ *
          (2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real)) := hraw
    _ ≤ 5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) +
        (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) *
          ‖chenTenSingularIntegral P N‖ := by
      have hmul' :
          ‖chenTenSingularIntegral P N‖ *
              (2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real)) ≤
            (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) *
              ‖chenTenSingularIntegral P N‖ := by
        calc
          ‖chenTenSingularIntegral P N‖ *
              (2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real)) =
            (2 * (40 : Real) ^ 15 / (Nat.sqrt P + 1 : Real)) *
              ‖chenTenSingularIntegral P N‖ := by ring
          _ ≤ (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) *
              ‖chenTenSingularIntegral P N‖ := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      linarith

private theorem absorb_chenTenMajorArc_error
    {P : Nat} (hPbig : (10 : Real) ^ 30 ≤ (P : Real)) :
    5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) ≤
      (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) := by
  have hP1 : (1 : Real) ≤ P := by
    have : (1 : Real) ≤ 10 ^ 30 := by norm_num
    exact this.trans hPbig
  have hPpos : (0 : Real) < P := lt_of_lt_of_le (by norm_num) hP1
  have hexp : (17 / 2 : Real) ≤ 91 / 10 := by norm_num
  have hE2 : (P : Real) ^ (17 / 2 : Real) ≤
      (P : Real) ^ (91 / 10 : Real) := by
    exact Real.rpow_le_rpow_of_exponent_le hP1 hexp
  have hPpow : (10 : Real) ^ 6 ≤ (P : Real) ^ (1 / 5 : Real) := by
    have hpow := Real.rpow_le_rpow (by positivity) hPbig
      (show (0 : Real) ≤ 1 / 5 by norm_num)
    calc
      (10 : Real) ^ 6 = ((10 : Real) ^ 30) ^ (1 / 5 : Real) := by
        calc
          (10 : Real) ^ 6 = (10 : Real) ^ (6 : Real) :=
            (Real.rpow_natCast 10 6).symm
          _ = (10 : Real) ^ ((30 : Real) * (1 / 5 : Real)) := by norm_num
          _ = ((10 : Real) ^ (30 : Real)) ^ (1 / 5 : Real) := by
            rw [Real.rpow_mul (by positivity)]
          _ = ((10 : Real) ^ 30) ^ (1 / 5 : Real) := by
            congr 1
            exact Real.rpow_natCast 10 30
      _ ≤ _ := hpow
  have hconst : (9 : Real) * 10 ^ 30 ≤ 10 ^ 25 * (P : Real) ^ (1 / 5 : Real) := by
    calc
      (9 : Real) * 10 ^ 30 ≤ 10 ^ 25 * 10 ^ 6 := by norm_num
      _ ≤ 10 ^ 25 * (P : Real) ^ (1 / 5 : Real) := by
        exact mul_le_mul_of_nonneg_left hPpow (by positivity)
  calc
    5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
          4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) ≤
        9 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) := by
      have hE2scaled :
          4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) ≤
            4 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) := by
        exact mul_le_mul_of_nonneg_left hE2 (by positivity)
      calc
        5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
              4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) ≤
            5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
              4 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) := by
          exact add_le_add (le_refl _) hE2scaled
        _ = 9 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) := by ring
    _ = (9 * (10 : Real) ^ 30) * (P : Real) ^ (91 / 10 : Real) := by ring
    _ ≤ (10 : Real) ^ 25 * (P : Real) ^ (1 / 5 : Real) *
        (P : Real) ^ (91 / 10 : Real) := by
      exact mul_le_mul_of_nonneg_right hconst
        (Real.rpow_nonneg (by positivity) _)
    _ = (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) := by
      calc
        (10 : Real) ^ 25 * (P : Real) ^ (1 / 5 : Real) *
            (P : Real) ^ (91 / 10 : Real) =
          (10 : Real) ^ 25 * ((P : Real) ^ (1 / 5 : Real) *
            (P : Real) ^ (91 / 10 : Real)) := by ring
        _ = (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) := by
          rw [← Real.rpow_add hPpos]
          norm_num

/-- The source threshold absorbs the finite major-arc errors into the final comparison scale. -/
theorem norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_series_le_source
    {P N : Nat} (hPbig : (10 : Real) ^ 30 ≤ (P : Real)) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N * chenTenSingularSeries N‖ ≤
      (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) +
        (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) *
          ‖chenTenSingularIntegral P N‖ := by
  have hP1 : (1 : Real) ≤ P := by
    have : (1 : Real) ≤ 10 ^ 30 := by norm_num
    exact this.trans hPbig
  have hPnat : 1 ≤ P := by
    have hnat : (10 : Nat) ^ 30 ≤ P := by exact_mod_cast hPbig
    omega
  have hraw := norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_series_le_source_tail
    (P := P) (N := N) hPnat
  have habs := absorb_chenTenMajorArc_error hPbig
  calc
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N * chenTenSingularSeries N‖ ≤
      5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) +
        4 * (10 : Real) ^ 30 * (P : Real) ^ (17 / 2 : Real) +
        (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) *
          ‖chenTenSingularIntegral P N‖ := hraw
    _ ≤ (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) +
        (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) *
          ‖chenTenSingularIntegral P N‖ := by
      linarith [habs]

end
end Waring.Analytic
