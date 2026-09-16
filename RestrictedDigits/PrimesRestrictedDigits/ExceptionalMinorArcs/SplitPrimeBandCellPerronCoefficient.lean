import PrimesRestrictedDigits.ExceptionalMinorArcs.DigitFourierNormPhase
import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeCellPerronError

/-!
# Perron coefficient for one rational-band and product cell

This combines all fixed-frequency coefficients in one disjoint canonical rational fiber before
Perron integration. Its finite L-series is exactly the existing localized fixed-height
bilinear sum.
-/

open Complex MeasureTheory
open scoped BigOperators Interval

namespace PrimesRestrictedDigits

noncomputable section

/-- Frequency-band aggregation of one product-cell Perron coefficient. -/
def splitPrimeBandCellPerronCoefficient
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) (r : Nat) : Complex :=
  ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
    (normalizedPaddedDigitFourierMagnitude
      digit length h.val : Complex) *
      paddedDigitFourierNormPhase digit length h.val *
      splitPrimeCellPerronCoefficient
        length h.val a delta eta I productKey r

/-- Strict product cutoff after aggregating a whole rational/product cell. -/
def splitPrimeBandCellStrictSum
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) : Complex :=
  ∑ r ∈ splitPrimeCellPerronSupport length,
    ((if r < 10 ^ length then 1 else 0 : Real) : Complex) *
      splitPrimeBandCellPerronCoefficient digit length a delta eta I S
        bandKey productKey r

/-- The combined strict sum is the corresponding frequency sum of the
fixed-frequency strict cells. -/
theorem splitPrimeBandCellStrictSum_eq_frequencySum
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) :
    splitPrimeBandCellStrictSum
        digit length a delta eta I S bandKey productKey =
      ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
        (normalizedPaddedDigitFourierMagnitude
          digit length h.val : Complex) *
        paddedDigitFourierNormPhase digit length h.val *
        splitPrimeCellStrictSum
          length h.val a delta eta I productKey := by
  classical
  unfold splitPrimeBandCellStrictSum splitPrimeBandCellPerronCoefficient
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [splitPrimeCellStrictSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Restoring the padded digit cardinality gives the literal frequency and
strict prime-pair cell sum. -/
theorem ninePow_mul_splitPrimeBandCellStrictSum_eq_literalCellSum
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) :
    (((9 : Real) ^ length : Real) : Complex) *
        splitPrimeBandCellStrictSum
          digit length a delta eta I S bandKey productKey =
      ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
        ∑ n ∈ splitProductCoordinateFiber length productKey.1,
          ∑ m ∈ splitProductCoordinateFiber length productKey.2 with
              n * m < 10 ^ length,
            paddedDigitFourierSum digit length h.val *
              (selectedProjectedPrimeWeightAtProduct
                (10 ^ length) a delta I n : Complex) *
              (complementaryLastPrimeWeightAtProduct
                (10 ^ length) a delta eta I m : Complex) *
              majorArcPhase
                (-((h.val : Real) * (n : Real) * (m : Real) /
                  ((10 ^ length : Nat) : Real))) := by
  classical
  rw [splitPrimeBandCellStrictSum_eq_frequencySum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [splitPrimeCellStrictSum_eq_pairSum, ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [splitPrimeCellPairCoefficient]
  have hrestore := ninePow_mul_normalizedMagnitude_mul_normPhase
    digit length h.val
  ring_nf at hrestore ⊢
  rw [hrestore]
  ring

/-- The finite L-series of the combined coefficient is exactly the existing
localized fixed-height bilinear sum. -/
theorem sum_lSeriesTerm_splitPrimeBandCellPerronCoefficient_eq
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) (s : Complex) :
    (∑ r ∈ splitPrimeCellPerronSupport length,
      LSeries.term
        (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
          bandKey productKey) s r) =
      localizedSplitPrimePerronBilinearSum digit length a delta eta I S
        bandKey productKey s
        (fun h => paddedDigitFourierNormPhase digit length h.val) := by
  classical
  let H := exceptionalDirichletBandFiber S bandKey
  let R := splitPrimeCellPerronSupport length
  let d (h : Fin (10 ^ length)) : Complex :=
    (normalizedPaddedDigitFourierMagnitude digit length h.val : Complex) *
      paddedDigitFourierNormPhase digit length h.val
  let c (h : Fin (10 ^ length)) :=
    splitPrimeCellPerronCoefficient
      length h.val a delta eta I productKey
  calc
    (∑ r ∈ R,
        LSeries.term
          (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
            bandKey productKey) s r) =
        ∑ r ∈ R, ∑ h ∈ H, d h * LSeries.term (c h) s r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrPos : 0 < r :=
        (Finset.mem_Ico.mp (show r ∈ R from hr)).1
      rw [LSeries.term_of_ne_zero hrPos.ne',
        splitPrimeBandCellPerronCoefficient, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro h hh
      rw [LSeries.term_of_ne_zero hrPos.ne']
      dsimp only [H, d, c]
      ring
    _ = ∑ h ∈ H, d h * ∑ r ∈ R, LSeries.term (c h) s r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]
    _ = ∑ h ∈ H, d h *
        (∑ n ∈ splitProductCoordinateFiber length productKey.1,
          ∑ m ∈ splitProductCoordinateFiber length productKey.2,
            ((selectedProjectedPrimeWeightAtProduct
                (10 ^ length) a delta I n : Complex) /
                (n : Complex) ^ s) *
              ((complementaryLastPrimeWeightAtProduct
                (10 ^ length) a delta eta I m : Complex) /
                (m : Complex) ^ s) *
              majorArcPhase
                (-((h.val : Real) * (n : Real) * (m : Real) /
                  ((10 ^ length : Nat) : Real)))) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [sum_lSeriesTerm_splitPrimeCellPerronCoefficient_eq]
    _ = localizedSplitPrimePerronBilinearSum digit length a delta eta I S
        bandKey productKey s
        (fun h => paddedDigitFourierNormPhase digit length h.val) := by
      unfold localizedSplitPrimePerronBilinearSum
        localizedExceptionalBilinearSum
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only [H, d]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring

/-- The combined finite Perron integral has the literal localized bilinear
sum as its contour integrand. -/
theorem finitePerronIntegral_splitPrimeBandCellPerronCoefficient_eq
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) (x sigma T : Real) :
    finitePerronIntegral
        (splitPrimeCellPerronSupport length)
        (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
          bandKey productKey) x sigma T =
      ((1 / (2 * Real.pi) : Real) : Complex) *
        ∫ t in -T..T,
          localizedSplitPrimePerronBilinearSum digit length a delta eta I S
              bandKey productKey
              ((sigma : Complex) + Complex.I * t)
              (fun h => paddedDigitFourierNormPhase digit length h.val) *
            (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
              ((sigma : Complex) + Complex.I * t) := by
  rw [finitePerronIntegral]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change ((∑ r ∈ splitPrimeCellPerronSupport length,
      LSeries.term
        (splitPrimeBandCellPerronCoefficient digit length a delta eta I S
          bandKey productKey)
        ((sigma : Complex) + Complex.I * t) r) *
      (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
        ((sigma : Complex) + Complex.I * t)) = _
  rw [sum_lSeriesTerm_splitPrimeBandCellPerronCoefficient_eq]

end

end PrimesRestrictedDigits
