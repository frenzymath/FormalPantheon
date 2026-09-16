import PrimesRestrictedDigits.ExceptionalMinorArcs.LocalizedPerronBilinear
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronHalfInteger

/-!
# Finite Perron coefficient for one split-prime cell

This groups one fixed-frequency two-product cell by the positive product variable. The
resulting finite Dirichlet polynomial factors exactly into the two Perron coefficients used by
the localized bilinear estimate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The positive product pairs in one canonical two-coordinate cell. -/
def splitPrimeCellPairs
    (length : Nat) (productKey : Nat × Nat) : Finset (Nat × Nat) :=
  (splitProductCoordinateFiber length productKey.1).product
    (splitProductCoordinateFiber length productKey.2)

/-- Every product of two positive factors below `X` lies in `[1,X^2)`. -/
def splitPrimeCellPerronSupport (length : Nat) : Finset Nat :=
  Finset.Ico 1 ((10 ^ length) ^ 2)

/-- The contribution of one pair before grouping by its product. -/
def splitPrimeCellPairCoefficient
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (nm : Nat × Nat) : Complex :=
  (selectedProjectedPrimeWeightAtProduct
      (10 ^ length) a delta I nm.1 : Complex) *
    (complementaryLastPrimeWeightAtProduct
      (10 ^ length) a delta eta I nm.2 : Complex) *
    majorArcPhase
      (-((frequency : Real) * (nm.1 : Real) * (nm.2 : Real) /
        ((10 ^ length : Nat) : Real)))

/-- The product-fiber coefficient of one fixed grid frequency and one
canonical two-product cell. -/
def splitPrimeCellPerronCoefficient
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (productKey : Nat × Nat) (r : Nat) : Complex :=
  ∑ nm ∈ splitPrimeCellPairs length productKey with nm.1 * nm.2 = r,
    splitPrimeCellPairCoefficient length frequency a delta eta I nm

/-- The strict product cutoff appearing before Perron inversion. -/
def splitPrimeCellStrictSum
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (productKey : Nat × Nat) : Complex :=
  ∑ r ∈ splitPrimeCellPerronSupport length,
    ((if r < 10 ^ length then 1 else 0 : Real) : Complex) *
      splitPrimeCellPerronCoefficient
        length frequency a delta eta I productKey r

/-- The product map sends the cell-pair carrier into its exact positive
Perron support. -/
theorem splitPrimeCellPair_product_mem_perronSupport
    {length : Nat} {productKey : Nat × Nat} {nm : Nat × Nat}
    (hnm : nm ∈ splitPrimeCellPairs length productKey) :
    nm.1 * nm.2 ∈ splitPrimeCellPerronSupport length := by
  have hpair := Finset.mem_product.mp hnm
  have hnPos := splitProductCoordinateFiber_pos hpair.1
  have hmPos := splitProductCoordinateFiber_pos hpair.2
  have hnLt := splitProductCoordinateFiber_lt_ambient hpair.1
  have hmLt := splitProductCoordinateFiber_lt_ambient hpair.2
  rw [splitPrimeCellPerronSupport, Finset.mem_Ico, pow_two]
  exact ⟨Nat.mul_pos hnPos hmPos,
    Nat.mul_lt_mul_of_lt_of_le hnLt hmLt.le (by positivity)⟩

/-- The half-integer indicator recovers exactly the literal nested cell sum
with strict product cutoff. Products at least `X` remain in the coefficient
support but contribute zero here. -/
theorem splitPrimeCellStrictSum_eq_pairSum
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (productKey : Nat × Nat) :
    splitPrimeCellStrictSum
        length frequency a delta eta I productKey =
      ∑ n ∈ splitProductCoordinateFiber length productKey.1,
        ∑ m ∈ splitProductCoordinateFiber length productKey.2 with
            n * m < 10 ^ length,
          splitPrimeCellPairCoefficient length frequency a delta eta I
            (n, m) := by
  classical
  let P := splitPrimeCellPairs length productKey
  let R := splitPrimeCellPerronSupport length
  let w := splitPrimeCellPairCoefficient length frequency a delta eta I
  have hmaps : ∀ nm ∈ P, nm.1 * nm.2 ∈ R := by
    intro nm hnm
    exact splitPrimeCellPair_product_mem_perronSupport hnm
  rw [splitPrimeCellStrictSum]
  calc
    (∑ r ∈ R,
        ((if r < 10 ^ length then 1 else 0 : Real) : Complex) *
          splitPrimeCellPerronCoefficient
            length frequency a delta eta I productKey r) =
        ∑ r ∈ R,
          ∑ nm ∈ P with nm.1 * nm.2 = r,
            ((if nm.1 * nm.2 < 10 ^ length then 1 else 0 : Real) : Complex) *
              w nm := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [splitPrimeCellPerronCoefficient, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro nm hnm
      rw [(Finset.mem_filter.mp hnm).2]
    _ = ∑ nm ∈ P,
        ((if nm.1 * nm.2 < 10 ^ length then 1 else 0 : Real) : Complex) *
          w nm :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ nm ∈ P with nm.1 * nm.2 < 10 ^ length, w nm := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro nm hnm
      by_cases hproduct : nm.1 * nm.2 < 10 ^ length <;>
        simp [hproduct]
    _ = ∑ n ∈ splitProductCoordinateFiber length productKey.1,
          ∑ m ∈ splitProductCoordinateFiber length productKey.2 with
              n * m < 10 ^ length,
            splitPrimeCellPairCoefficient length frequency a delta eta I
              (n, m) := by
      dsimp only [P, w]
      rw [splitPrimeCellPairs, Finset.sum_filter]
      simp_rw [Finset.sum_filter]
      change (∑ nm ∈
          splitProductCoordinateFiber length productKey.1 ×ˢ
            splitProductCoordinateFiber length productKey.2,
          if nm.1 * nm.2 < 10 ^ length then
            splitPrimeCellPairCoefficient
              length frequency a delta eta I nm
          else 0) = _
      simpa only using
        (Finset.sum_product
          (splitProductCoordinateFiber length productKey.1)
          (splitProductCoordinateFiber length productKey.2)
          (fun nm => if nm.1 * nm.2 < 10 ^ length then
            splitPrimeCellPairCoefficient
              length frequency a delta eta I nm
          else 0))

/-- Regrouping by the product and splitting the positive-real complex power
gives the literal fixed-height bilinear Dirichlet polynomial. -/
theorem sum_lSeriesTerm_splitPrimeCellPerronCoefficient_eq
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (productKey : Nat × Nat) (s : Complex) :
    (∑ r ∈ splitPrimeCellPerronSupport length,
        LSeries.term
          (splitPrimeCellPerronCoefficient
            length frequency a delta eta I productKey) s r) =
      ∑ n ∈ splitProductCoordinateFiber length productKey.1,
        ∑ m ∈ splitProductCoordinateFiber length productKey.2,
          ((selectedProjectedPrimeWeightAtProduct
              (10 ^ length) a delta I n : Complex) /
              (n : Complex) ^ s) *
            ((complementaryLastPrimeWeightAtProduct
              (10 ^ length) a delta eta I m : Complex) /
              (m : Complex) ^ s) *
            majorArcPhase
              (-((frequency : Real) * (n : Real) * (m : Real) /
                ((10 ^ length : Nat) : Real))) := by
  classical
  let P := splitPrimeCellPairs length productKey
  let R := splitPrimeCellPerronSupport length
  let w := splitPrimeCellPairCoefficient length frequency a delta eta I
  have hmaps : ∀ nm ∈ P, nm.1 * nm.2 ∈ R := by
    intro nm hnm
    exact splitPrimeCellPair_product_mem_perronSupport hnm
  calc
    (∑ r ∈ R,
        LSeries.term
          (splitPrimeCellPerronCoefficient
            length frequency a delta eta I productKey) s r) =
        ∑ r ∈ R, ∑ nm ∈ P with nm.1 * nm.2 = r,
          ((selectedProjectedPrimeWeightAtProduct
              (10 ^ length) a delta I nm.1 : Complex) /
              (nm.1 : Complex) ^ s) *
            ((complementaryLastPrimeWeightAtProduct
              (10 ^ length) a delta eta I nm.2 : Complex) /
              (nm.2 : Complex) ^ s) *
            majorArcPhase
              (-((frequency : Real) * (nm.1 : Real) * (nm.2 : Real) /
                ((10 ^ length : Nat) : Real))) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrPos : 0 < r :=
        (Finset.mem_Ico.mp (show r ∈ R from hr)).1
      rw [LSeries.term_of_ne_zero hrPos.ne',
        splitPrimeCellPerronCoefficient, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro nm hnm
      have hproduct : nm.1 * nm.2 = r :=
        (Finset.mem_filter.mp hnm).2
      rw [← hproduct, splitPrimeCellPairCoefficient]
      norm_num only [Nat.cast_mul]
      rw [
        Complex.natCast_mul_natCast_cpow, div_eq_mul_inv, mul_inv]
      ring
    _ = ∑ nm ∈ P,
          ((selectedProjectedPrimeWeightAtProduct
              (10 ^ length) a delta I nm.1 : Complex) /
              (nm.1 : Complex) ^ s) *
            ((complementaryLastPrimeWeightAtProduct
              (10 ^ length) a delta eta I nm.2 : Complex) /
              (nm.2 : Complex) ^ s) *
            majorArcPhase
              (-((frequency : Real) * (nm.1 : Real) * (nm.2 : Real) /
                ((10 ^ length : Nat) : Real))) :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ n ∈ splitProductCoordinateFiber length productKey.1,
          ∑ m ∈ splitProductCoordinateFiber length productKey.2,
            ((selectedProjectedPrimeWeightAtProduct
                (10 ^ length) a delta I n : Complex) /
                (n : Complex) ^ s) *
              ((complementaryLastPrimeWeightAtProduct
                (10 ^ length) a delta eta I m : Complex) /
                (m : Complex) ^ s) *
              majorArcPhase
                (-((frequency : Real) * (n : Real) * (m : Real) /
                  ((10 ^ length : Nat) : Real))) := by
      exact Finset.sum_product _ _ _

end

end PrimesRestrictedDigits
