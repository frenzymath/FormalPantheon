import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairBridges
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalCarriers

/-!
# Low central-large terminal normalization

This file identifies the raw terminal main sum with its normalized prime-log pair sum.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def sectionSixFirstLowCentralLargeTerminalMainSum
    (epsilon : Real) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge,
    1 / ((index.1 : Real) * (index.2 : Real) *
      Real.log (X / (sectionSixFirstPairProduct index : Real)))

private theorem sectionSixFirstLowCentralLargeTerminalSummand_eq
    {length : Nat} (hlength : 1 <= length)
    (index : SectionSixFirstStrictIndex)
    (hp : index.1.Prime) (hq : index.2.Prime)
    (hY : (1 : Real) < ((10 ^ length : Nat) : Real) /
      (sectionSixFirstPairProduct index : Real)) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    1 / ((index.1 : Real) * (index.2 : Real) *
        Real.log (X / (sectionSixFirstPairProduct index : Real))) =
      normalizedPrimeLogWeight XNat index.2 *
          normalizedPrimeLogWeight XNat index.1 *
          sectionSixFirstLowCentralLargeTerminalKernel
            (normalizedPrimeLog XNat index.2,
              normalizedPrimeLog XNat index.1) /
        Real.log X := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1
  let q : Nat := index.2
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : Real) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hlogp : Real.log (p : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt : (1 : Real) < p)).ne'
  have hlogq : Real.log (q : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hq.one_lt : (1 : Real) < q)).ne'
  have hlogY : Real.log (X / ((p * q : Nat) : Real)) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    simpa only [X, XNat, p, q, sectionSixFirstPairProduct] using hY
  have hlogProduct :
      Real.log (X / ((p * q : Nat) : Real)) =
        Real.log X - Real.log (p : Real) - Real.log (q : Real) := by
    rw [Real.log_div (ne_of_gt (zero_lt_one.trans hX))
      (by exact_mod_cast mul_ne_zero hp.ne_zero hq.ne_zero),
      Nat.cast_mul, Real.log_mul hp0 hq0]
    ring
  rw [hlogProduct] at hlogY
  dsimp only
  simp only [sectionSixFirstPairProduct]
  unfold normalizedPrimeLogWeight
    sectionSixFirstLowCentralLargeTerminalKernel normalizedPrimeLog
  rw [hlogProduct]
  dsimp only [X, XNat, p, q] at hlogX hlogp hlogq hlogY ⊢
  field_simp [hlogX, hlogp, hlogq, hp0, hq0, hlogY]

theorem sectionSixFirstLowCentralLargeTerminalMainSum_eq_normalized
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstLowCentralLargeTerminalMainSum epsilon length =
      normalizedPrimeLogPairSum
          (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
          (sectionSixFirstLowCentralLargeTerminalRegion epsilon)
          sectionSixFirstLowCentralLargeTerminalKernel /
        Real.log ((10 ^ length : Nat) : Real) := by
  classical
  let indices := sectionSixFirstPairPieceIndices epsilon length
    (.lowCentralLarge)
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hpoint : ∀ index ∈ indices,
      1 / ((index.1 : Real) * (index.2 : Real) *
          Real.log (X / (sectionSixFirstPairProduct index : Real))) =
        normalizedPrimeLogWeight XNat index.2 *
            normalizedPrimeLogWeight XNat index.1 *
            sectionSixFirstLowCentralLargeTerminalKernel
              (normalizedPrimeLog XNat index.2,
                normalizedPrimeLog XNat index.1) /
          Real.log X := by
    intro index hindex
    have hindex' : index ∈ sectionSixFirstPairPieceIndices epsilon length
        .lowCentralLarge := by
      simpa only [indices] using hindex
    have hpiece : index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
        sectionSixZThree epsilon X <
            (sectionSixFirstPairProduct index : Real) ∧
          (sectionSixFirstPairProduct index : Real) <
            sectionSixZFive epsilon X ∧
          sectionSixZSix epsilon X <=
            (sectionSixFirstPairSquareProduct index : Real) := by
      have hmem := (Finset.mem_filter.mp hindex').2
      simpa [sectionSixFirstPairMem, X, XNat] using hmem
    have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
    have hp := (mem_sievePrimeInterval.mp hdata.1).1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hq := hqData.1
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hp hq).1 hqData.2.2
    have hdPos : (0 : Real) <
        (sectionSixFirstPairProduct index : Real) := by
      simp only [sectionSixFirstPairProduct, Nat.cast_mul]
      exact mul_pos (by exact_mod_cast hp.pos) (by exact_mod_cast hq.pos)
    have hqLeY : (index.2 : Real) <=
        X / (sectionSixFirstPairProduct index : Real) := by
      apply (le_div_iff₀ hdPos).2
      have hcapReal :
          (((index.1 * index.2 * index.2 : Nat) : Real)) <= X := by
        dsimp only [X, XNat]
        exact_mod_cast hthreshold.2
      simpa [sectionSixFirstPairProduct, Nat.cast_mul, mul_assoc,
        mul_left_comm, mul_comm] using hcapReal
    have hqOne : (1 : Real) < (index.2 : Real) := by
      exact_mod_cast hq.one_lt
    have hY : (1 : Real) <
        X / (sectionSixFirstPairProduct index : Real) :=
      hqOne.trans_le hqLeY
    simpa only [X, XNat] using
      sectionSixFirstLowCentralLargeTerminalSummand_eq hlength index hp hq hY
  unfold sectionSixFirstLowCentralLargeTerminalMainSum
    normalizedPrimeLogPairSum
  dsimp only [X, XNat, indices]
  rw [← image_sectionSixFirstLowCentralLargePairPieceIndices
      epsilon hepsilon hepsilonSmall hlength,
    Finset.sum_image sectionSixFirstNatPair_injective.injOn,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index hindex
  exact hpoint index hindex

end

end PrimesRestrictedDigits
