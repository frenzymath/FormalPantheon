import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeContinuationBuchstab

/-!
# Finite bridge for the low central-large below term

This file reindexes the raw continuation Buchstab main sum by the exact left-associated
normalized triple carrier. The kernel algebra contributes exactly one division by `log X`.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.10).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralLargeBelowBuchstabSummand_eq
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstPairContinuationIndex)
    (hp : index.1.1.Prime) (hq : index.1.2.Prime)
    (hr : index.2.Prime) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    buchstabFunction
        (Real.log (X /
          ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) /
            Real.log (index.2 : Real)) /
      ((index.1.1 : Real) * (index.1.2 : Real) *
        (index.2 : Real) * Real.log (index.2 : Real)) =
      normalizedPrimeLogWeight XNat index.1.1 *
          normalizedPrimeLogWeight XNat index.1.2 *
          normalizedPrimeLogWeight XNat index.2 *
          sectionSixFirstLowCentralLargeBelowKernel
            ((normalizedPrimeLog XNat index.1.1,
              normalizedPrimeLog XNat index.1.2),
              normalizedPrimeLog XNat index.2) /
        Real.log X := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1.1
  let q : Nat := index.1.2
  let r : Nat := index.2
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hX0 : X ≠ 0 := (zero_lt_one.trans hX).ne'
  have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : Real) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hr0 : (r : Real) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hlogp : Real.log (p : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hlogq : Real.log (q : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
  have hlogr : Real.log (r : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hr.one_lt)).ne'
  have hlogProduct :
      Real.log (X / ((p * q * r : Nat) : Real)) =
        Real.log X - Real.log (p : Real) - Real.log (q : Real) -
          Real.log (r : Real) := by
    rw [Real.log_div hX0 (by
      exact_mod_cast mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero)
        hr.ne_zero)]
    norm_num only [Nat.cast_mul]
    rw [Real.log_mul (mul_ne_zero hp0 hq0) hr0,
      Real.log_mul hp0 hq0]
    ring
  have hargument :
      Real.log (X / ((p * q * r : Nat) : Real)) /
          Real.log (r : Real) =
        (1 - normalizedPrimeLog XNat p - normalizedPrimeLog XNat q -
            normalizedPrimeLog XNat r) /
          normalizedPrimeLog XNat r := by
    rw [hlogProduct]
    unfold normalizedPrimeLog
    dsimp only [X, XNat]
    field_simp [hlogX, hlogr]
  dsimp only
  simp only [p, q, r] at hargument ⊢
  rw [hargument]
  unfold normalizedPrimeLogWeight
    sectionSixFirstLowCentralLargeBelowKernel normalizedPrimeLog
  have hlogX' : Real.log ((10 ^ length : Nat) : Real) ≠ 0 := by
    simpa only [X, XNat] using hlogX
  have hlogp' : Real.log (index.1.1 : Real) ≠ 0 := by
    simpa only [p] using hlogp
  have hlogq' : Real.log (index.1.2 : Real) ≠ 0 := by
    simpa only [q] using hlogq
  have hlogr' : Real.log (index.2 : Real) ≠ 0 := by
    simpa only [r] using hlogr
  dsimp only [X, XNat, p, q, r]
  field_simp [hlogX', hlogp', hlogq', hlogr', hp0, hq0, hr0]

theorem sectionSixFirstLowCentralLargeBelowBuchstabMainSum_eq_normalized
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
        epsilon length .below =
      normalizedPrimeLogTripleSum
          (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
          (sectionSixFirstLowCentralLargeBelowRegion epsilon)
          sectionSixFirstLowCentralLargeBelowKernel /
        Real.log ((10 ^ length : Nat) : Real) := by
  classical
  let indices := sectionSixFirstLowCentralLargeContinuationPieceIndices
    epsilon length .below
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hpoint : ∀ index ∈ indices,
      buchstabFunction
          (Real.log (X /
            ((index.1.1 * index.1.2 * index.2 : Nat) : Real)) /
              Real.log (index.2 : Real)) /
        ((index.1.1 : Real) * (index.1.2 : Real) *
          (index.2 : Real) * Real.log (index.2 : Real)) =
        normalizedPrimeLogWeight XNat index.1.1 *
            normalizedPrimeLogWeight XNat index.1.2 *
            normalizedPrimeLogWeight XNat index.2 *
            sectionSixFirstLowCentralLargeBelowKernel
              ((normalizedPrimeLog XNat index.1.1,
                normalizedPrimeLog XNat index.1.2),
                normalizedPrimeLog XNat index.2) /
          Real.log X := by
    intro index hindex
    have hindex' : index ∈
        sectionSixFirstLowCentralLargeContinuationPieceIndices
          epsilon length .below := by
      simpa only [indices] using hindex
    have hpiece :=
      mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mp hindex'
    have hcontinuation :=
      mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hpiece.1
    have hpqFiltered := Finset.mem_filter.mp hcontinuation.1
    have hpqPiece :
        index.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
          sectionSixZThree epsilon X <
              (sectionSixFirstPairProduct index.1 : Real) ∧
            (sectionSixFirstPairProduct index.1 : Real) <
                sectionSixZFive epsilon X ∧
              sectionSixZSix epsilon X <=
                (sectionSixFirstPairSquareProduct index.1 : Real) := by
      simpa [sectionSixFirstPairMem, X, XNat] using hpqFiltered.2
    have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpqPiece.1
    have hrData := mem_sievePrimeInterval.mp hcontinuation.2
    exact sectionSixFirstLowCentralLargeBelowBuchstabSummand_eq hlength index
      (mem_sievePrimeInterval.mp hpqData.1).1
      (mem_sievePrimeInterval.mp hpqData.2).1 hrData.1
  unfold sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
    normalizedPrimeLogTripleSum
  dsimp only [X, XNat, indices]
  rw [← image_sectionSixFirstLowCentralLargeBelowContinuationIndices
      epsilon hepsilon hepsilonSmall hlength,
    Finset.sum_image
      sectionSixFirstLowCentralLargeContinuationNatTriple_injective.injOn,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index hindex
  exact hpoint index hindex

end

end PrimesRestrictedDigits
