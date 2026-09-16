import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleBuchstab

/-!
# Finite bridge for the high central-small quadruple term

This file reindexes the raw Buchstab main sum by the exact left-associated normalized fourfold
carrier. The coefficient is one, and the kernel algebra contributes exactly one division by
`log X`.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 145--146, Eq. (6.16), region `R5`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstHighCentralSmallQuadrupleBuchstabSummand_eq
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstHighCentralSmallQuadrupleIndex)
    (hp : index.1.1.1.Prime) (hq : index.1.1.2.Prime)
    (hr : index.1.2.Prime) (hs : index.2.Prime) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    buchstabFunction
        (Real.log (X /
          ((sectionSixFirstHighCentralSmallTripleProduct index.1 * index.2 :
            Nat) : Real)) / Real.log (index.2 : Real)) /
      ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
        (index.1.2 : Real) * (index.2 : Real) * Real.log (index.2 : Real)) =
      normalizedPrimeLogWeight XNat index.1.1.1 *
          normalizedPrimeLogWeight XNat index.1.1.2 *
          normalizedPrimeLogWeight XNat index.1.2 *
          normalizedPrimeLogWeight XNat index.2 *
          sectionSixFirstHighCentralSmallQuadrupleKernel
            (((normalizedPrimeLog XNat index.1.1.1,
                normalizedPrimeLog XNat index.1.1.2),
              normalizedPrimeLog XNat index.1.2),
              normalizedPrimeLog XNat index.2) /
        Real.log X := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1.1.1
  let q : Nat := index.1.1.2
  let r : Nat := index.1.2
  let s : Nat := index.2
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
  have hs0 : (s : Real) ≠ 0 := by exact_mod_cast hs.ne_zero
  have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hlogp : Real.log (p : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hlogq : Real.log (q : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
  have hlogr : Real.log (r : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hr.one_lt)).ne'
  have hlogs : Real.log (s : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hs.one_lt)).ne'
  have hlogProduct :
      Real.log (X / ((p * q * r * s : Nat) : Real)) =
        Real.log X - Real.log (p : Real) - Real.log (q : Real) -
          Real.log (r : Real) - Real.log (s : Real) := by
    rw [Real.log_div hX0 (by
      exact_mod_cast mul_ne_zero
        (mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero)
          hs.ne_zero)]
    norm_num only [Nat.cast_mul]
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hp0 hq0) hr0) hs0,
      Real.log_mul (mul_ne_zero hp0 hq0) hr0,
      Real.log_mul hp0 hq0]
    ring
  have hargument :
      Real.log (X / ((p * q * r * s : Nat) : Real)) /
          Real.log (s : Real) =
        (1 - normalizedPrimeLog XNat p - normalizedPrimeLog XNat q -
            normalizedPrimeLog XNat r - normalizedPrimeLog XNat s) /
          normalizedPrimeLog XNat s := by
    rw [hlogProduct]
    unfold normalizedPrimeLog
    dsimp only [X, XNat]
    field_simp [hlogX, hlogs]
  dsimp only
  simp only [sectionSixFirstHighCentralSmallTripleProduct,
    sectionSixFirstPairProduct, p, q, r, s] at hargument ⊢
  rw [hargument]
  unfold normalizedPrimeLogWeight
    sectionSixFirstHighCentralSmallQuadrupleKernel normalizedPrimeLog
  have hlogX' : Real.log ((10 ^ length : Nat) : Real) ≠ 0 := by
    simpa only [X, XNat] using hlogX
  have hlogp' : Real.log (index.1.1.1 : Real) ≠ 0 := by
    simpa only [p] using hlogp
  have hlogq' : Real.log (index.1.1.2 : Real) ≠ 0 := by
    simpa only [q] using hlogq
  have hlogr' : Real.log (index.1.2 : Real) ≠ 0 := by
    simpa only [r] using hlogr
  have hlogs' : Real.log (index.2 : Real) ≠ 0 := by
    simpa only [s] using hlogs
  dsimp only [X, XNat, p, q, r, s]
  field_simp [hlogX', hlogp', hlogq', hlogr', hlogs',
    hp0, hq0, hr0, hs0]

/-- The raw quadruple Buchstab sum is its coefficient-one normalized sum. -/
theorem sectionSixFirstHighCentralSmallQuadrupleBuchstabMainSum_eq_normalized
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstHighCentralSmallQuadrupleBuchstabMainSum epsilon length =
      normalizedPrimeLogFourfoldSum
          (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
          (sectionSixFirstHighCentralSmallQuadrupleRegion epsilon)
          sectionSixFirstHighCentralSmallQuadrupleKernel /
        Real.log ((10 ^ length : Nat) : Real) := by
  classical
  let indices := sectionSixFirstHighCentralSmallQuadrupleIndices epsilon length
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hpoint : ∀ index ∈ indices,
      buchstabFunction
          (Real.log (X /
            ((sectionSixFirstHighCentralSmallTripleProduct index.1 * index.2 :
              Nat) : Real)) / Real.log (index.2 : Real)) /
        ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
          (index.1.2 : Real) * (index.2 : Real) * Real.log (index.2 : Real)) =
        normalizedPrimeLogWeight XNat index.1.1.1 *
            normalizedPrimeLogWeight XNat index.1.1.2 *
            normalizedPrimeLogWeight XNat index.1.2 *
            normalizedPrimeLogWeight XNat index.2 *
            sectionSixFirstHighCentralSmallQuadrupleKernel
              (((normalizedPrimeLog XNat index.1.1.1,
                  normalizedPrimeLog XNat index.1.1.2),
                normalizedPrimeLog XNat index.1.2),
                normalizedPrimeLog XNat index.2) /
          Real.log X := by
    intro index hindex
    have hquad := mem_sectionSixFirstHighCentralSmallQuadrupleIndices.mp
      (by simpa only [indices] using hindex)
    have htriple :=
      mem_sectionSixFirstHighCentralSmallTripleIndices.mp hquad.1
    have hpqFiltered := Finset.mem_filter.mp htriple.1
    have hpqPiece :
        index.1.1 ∈ sectionSixFirstHighStrictIndices epsilon length ∧
          sectionSixZThree epsilon X <
              (sectionSixFirstPairProduct index.1.1 : Real) ∧
            (sectionSixFirstPairProduct index.1.1 : Real) <
                sectionSixZFive epsilon X ∧
              (sectionSixFirstPairSquareProduct index.1.1 : Real) <
                sectionSixZSix epsilon X := by
      simpa only [sectionSixFirstPairMem, X] using hpqFiltered.2
    have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpqPiece.1
    exact sectionSixFirstHighCentralSmallQuadrupleBuchstabSummand_eq hlength
      index (mem_sievePrimeInterval.mp hpqData.1).1
      (mem_sievePrimeInterval.mp hpqData.2).1
      (mem_sievePrimeInterval.mp htriple.2).1
      (mem_sievePrimeInterval.mp hquad.2).1
  unfold sectionSixFirstHighCentralSmallQuadrupleBuchstabMainSum
    normalizedPrimeLogFourfoldSum
  dsimp only [X, XNat, indices]
  rw [← sectionSixFirstHighCentralSmallQuadrupleIndices_map_eq_normalizedPrimeLogFourfoldIndices
      epsilon hepsilon hepsilonSmall hlength]
  simp only [Finset.sum_map,
    sectionSixFirstHighCentralSmallQuadrupleNestedEquiv]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index hindex
  exact hpoint index hindex

end

end PrimesRestrictedDigits
