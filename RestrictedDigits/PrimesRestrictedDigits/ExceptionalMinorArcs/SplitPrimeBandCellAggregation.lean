import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeBandCellMinorBound

/-!
# Canonical rational/product-cell aggregation

This sums a uniform strict-cell bound over the canonical rational keys and active product
keys. The rational-fiber error cardinalities sum exactly to the original frequency carrier
cardinality.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A uniform contour term and the exact fiberwise Perron errors aggregate
with their correct finite cardinalities. -/
theorem norm_sum_band_activeCellStrictSums_le
    {length : Nat} (hlength : 0 < length) (digit : Fin 10)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (S : Finset (Fin (10 ^ length)))
    (A B X contour : Real)
    (hcell : ∀ bandKey ∈ exceptionalDirichletBandKeys length,
      ∀ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
        ‖splitPrimeBandCellStrictSum digit length a delta eta I S
            bandKey productKey‖ ≤
          20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
            A * B / X + contour) :
    ‖∑ bandKey ∈ exceptionalDirichletBandKeys length,
        ∑ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
          splitPrimeBandCellStrictSum digit length a delta eta I S
            bandKey productKey‖ ≤
      20 *
          ((activeSplitPrimeCellKeys length a delta eta I).card : Real) *
          (S.card : Real) * A * B / X +
        ((exceptionalDirichletBandKeys length).card : Real) *
          ((activeSplitPrimeCellKeys length a delta eta I).card : Real) *
          contour := by
  let R := exceptionalDirichletBandKeys length
  let P := activeSplitPrimeCellKeys length a delta eta I
  let error : Nat × Nat → Real := fun bandKey =>
    20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
      A * B / X
  have hsum :
      ‖∑ bandKey ∈ R,
          ∑ productKey ∈ P,
            splitPrimeBandCellStrictSum digit length a delta eta I S
              bandKey productKey‖ ≤
        ∑ bandKey ∈ R, ∑ productKey ∈ P,
          (error bandKey + contour) := by
    calc
      ‖∑ bandKey ∈ R,
          ∑ productKey ∈ P,
            splitPrimeBandCellStrictSum digit length a delta eta I S
              bandKey productKey‖ ≤
          ∑ bandKey ∈ R,
            ‖∑ productKey ∈ P,
              splitPrimeBandCellStrictSum digit length a delta eta I S
                bandKey productKey‖ := norm_sum_le _ _
      _ ≤ ∑ bandKey ∈ R, ∑ productKey ∈ P,
          ‖splitPrimeBandCellStrictSum digit length a delta eta I S
            bandKey productKey‖ := by
        apply Finset.sum_le_sum
        intro bandKey hbandKey
        exact norm_sum_le _ _
      _ ≤ ∑ bandKey ∈ R, ∑ productKey ∈ P,
          (error bandKey + contour) := by
        apply Finset.sum_le_sum
        intro bandKey hbandKey
        apply Finset.sum_le_sum
        intro productKey hproductKey
        exact hcell bandKey hbandKey productKey hproductKey
  have hfiberCard :
      (∑ bandKey ∈ R,
          ((exceptionalDirichletBandFiber S bandKey).card : Real)) =
        (S.card : Real) := by
    exact_mod_cast sum_card_exceptionalDirichletBandFibers hlength S
  have herrorSum : (∑ bandKey ∈ R, error bandKey) =
      20 * (S.card : Real) * A * B / X := by
    calc
      (∑ bandKey ∈ R, error bandKey) =
          (∑ bandKey ∈ R,
            ((exceptionalDirichletBandFiber S bandKey).card : Real)) *
              (20 * A * B / X) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro bandKey hbandKey
        dsimp only [error]
        ring
      _ = 20 * (S.card : Real) * A * B / X := by
        rw [hfiberCard]
        ring
  have hsumValue :
      (∑ bandKey ∈ R, ∑ productKey ∈ P,
          (error bandKey + contour)) =
        20 * (P.card : Real) * (S.card : Real) * A * B / X +
          (R.card : Real) * (P.card : Real) * contour := by
    calc
      (∑ bandKey ∈ R, ∑ productKey ∈ P,
          (error bandKey + contour)) =
          ∑ bandKey ∈ R,
            (P.card : Real) * (error bandKey + contour) := by
        apply Finset.sum_congr rfl
        intro bandKey hbandKey
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ = (P.card : Real) * (∑ bandKey ∈ R, error bandKey) +
          (R.card : Real) * (P.card : Real) * contour := by
        rw [Finset.mul_sum]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp
        ring
      _ = 20 * (P.card : Real) * (S.card : Real) * A * B / X +
          (R.card : Real) * (P.card : Real) * contour := by
        rw [herrorSum]
        ring
  dsimp only [R, P] at hsum hsumValue ⊢
  exact hsum.trans_eq hsumValue

/-- Outside a positive raw-major-arc cutoff, the literal source frequency sum
is bounded by the exactly aggregated Perron errors and contour terms. -/
theorem exists_norm_splitPrimeExceptionalSource_le :
    ∃ C : Real, 0 < C ∧ ∃ logLoss length0 : Nat,
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (delta eta mu H : Real) (I : Finset (Fin k))
        (S : Finset (Fin (10 ^ length))),
        let X : Real := ((10 ^ length : Nat) : Real)
        let A := selectedPrimePerronCoefficientCap (10 ^ length) I
        let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
        let contour := 30 * A * B *
            (C * X * Real.log X ^ logLoss /
              H ^ (latticeSumSaving / 10)) *
          Real.log X
        0 < H →
        (∀ h ∈ S,
          h.val ∉ majorArcRawFrequencies (10 ^ length) H) →
        0 ≤ delta →
        ((k + 1 : Nat) : Real) * delta + 1 / (length : Real) ≤ mu →
        ((∑ i ∈ I, a i) ∈
            Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
            Set.Icc (23 / 40 + mu) (16 / 25 - mu)) →
        S ⊆ genericExceptionalFrequencies digit length →
        ‖∑ h ∈ S,
            paddedDigitFourierSum digit length h.val *
              majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                (fun r => (majorArcRegionWeightAtProduct
                  (10 ^ length) a delta eta r : Complex))
                (-((h.val : Real) / X))‖ ≤
          (9 : Real) ^ length *
            (20 *
                ((activeSplitPrimeCellKeys length a delta eta I).card :
                  Real) *
                (S.card : Real) * A * B / X +
              ((exceptionalDirichletBandKeys length).card : Real) *
                ((activeSplitPrimeCellKeys length a delta eta I).card :
                  Real) *
                contour) := by
  obtain ⟨C, hC, logLoss, length0, hcell⟩ :=
    exists_splitPrimeBandCellMinorBound
  refine ⟨C, hC, logLoss, max length0 1, ?_⟩
  intro length hlength digit k a delta eta mu H I S
  dsimp only
  intro hH hminor hdelta hmargin hconvenient hS
  have hcellLength : length0 ≤ length :=
    (le_max_left length0 1).trans hlength
  have hlengthOne : 1 ≤ length :=
    (le_max_right length0 1).trans hlength
  have hlengthPos : 0 < length := Nat.zero_lt_of_lt hlengthOne
  let X : Real := ((10 ^ length : Nat) : Real)
  let A := selectedPrimePerronCoefficientCap (10 ^ length) I
  let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
  let contour := 30 * A * B *
      (C * X * Real.log X ^ logLoss /
        H ^ (latticeSumSaving / 10)) *
    Real.log X
  have hcellUniform :
      ∀ bandKey ∈ exceptionalDirichletBandKeys length,
      ∀ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
        ‖splitPrimeBandCellStrictSum digit length a delta eta I S
            bandKey productKey‖ ≤
          20 * ((exceptionalDirichletBandFiber S bandKey).card : Real) *
            A * B / X + contour := by
    intro bandKey hbandKey productKey hproductKey
    have hactive := (mem_activeSplitPrimeCellKeys_iff.mp hproductKey).2
    have hbound := hcell length hcellLength digit k a delta eta mu H I S
      bandKey productKey hH hminor hdelta hmargin hconvenient hS hactive
    simpa only [X, A, B, contour] using hbound
  have haggregate := norm_sum_band_activeCellStrictSums_le
    hlengthPos digit a delta eta I S A B X contour hcellUniform
  rw [← ninePow_mul_sum_band_activeCellStrictSums_eq_source
    hlengthPos digit a delta eta I S]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  dsimp only [X, A, B, contour] at haggregate ⊢
  exact mul_le_mul_of_nonneg_left haggregate (by positivity)

end

end PrimesRestrictedDigits
