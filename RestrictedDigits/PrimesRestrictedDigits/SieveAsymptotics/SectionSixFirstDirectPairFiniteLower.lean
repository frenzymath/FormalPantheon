import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairBridges
import PrimesRestrictedDigits.SieveDecomposition.RoughBridge

/-!
# Finite lower bound for the first direct pair pieces

The nonnegative restricted cofactor count is discarded, while the ambient strict rough count
is bounded by the one-sided Buchstab estimate. The constant is chosen before epsilon, length,
the excluded digit, and the piece.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 140--141 and 145, Eqs. (6.7), (6.14), and
(6.15).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstDirectPair_finiteIndexData
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {piece : SectionSixFirstPairPiece}
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length piece) :
    index.1.Prime ∧ index.2.Prime ∧
      ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon < index.1 ∧
      ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon < index.2 ∧
      index.2 <= index.1 ∧ index.1 * index.2 * index.2 <= 10 ^ length := by
  classical
  have hstrict : index ∈ sectionSixFirstStrictIndices epsilon length :=
    (Finset.mem_filter.mp hindex).1
  rw [sectionSixFirstStrictIndices, Finset.mem_union] at hstrict
  rcases hstrict with hlow | hhigh
  · have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hlow
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    exact ⟨hpData.1, hqData.1,
      by simpa [sectionSixZOne] using hpData.2.1,
      by simpa [sectionSixZOne] using hqData.2.1,
      hthreshold.1, hthreshold.2⟩
  · have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hhigh
    have hpData := mem_sievePrimeInterval.mp hdata.1
    have hqData := mem_sievePrimeInterval.mp hdata.2
    have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
      exact_mod_cast sectionSixFirst_direct_hXNat hlength
    have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
    have hthreshold :=
      (sectionSixFirst_direct_pairThreshold_iff hpData.1 hqData.1).1
        hqData.2.2
    exact ⟨hpData.1, hqData.1,
      by simpa [sectionSixZOne] using
        (horder.1.trans horder.2.1 |>.trans hpData.2.1),
      by simpa [sectionSixZOne] using hqData.2.1,
      hthreshold.1, hthreshold.2⟩

private theorem sectionSixFirstDirectPair_term_lower
    {C : Real} (hrough :
      ∀ Y y u : Real, 0 < Y -> 2 <= y -> 1 <= u -> u <= 400 ->
        u = Real.log Y / Real.log y ->
        (maynardStrictRoughCount Y y : Real) <=
          buchstabFunction u * Y / Real.log y +
            C * (Y / Real.log Y ^ 2))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (digit : Fin 10)
    {piece : SectionSixFirstPairPiece}
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length piece) :
    let X : Real := ((10 ^ length : Nat) : Real);
    let densityMass : Real := (restrictedDigitDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real);
    (-densityMass *
        (buchstabFunction
              (Real.log (X / (sectionSixFirstPairProduct index : Real)) /
                Real.log (index.2 : Real)) /
            ((index.1 : Real) * (index.2 : Real) *
              Real.log (index.2 : Real)) +
          C / ((index.1 : Real) * (index.2 : Real) *
            Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2))) <=
      sectionSixStrictPrimeTerm digit length
        (Nat.toPNat' index.1) index.2 := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1
  let q : Nat := index.2
  let d : PNat := Nat.toPNat' p * Nat.toPNat' q
  let Y : Real := X / ((p * q : Nat) : Real)
  let u : Real := Real.log Y / Real.log (q : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  let lambda : Real := densityMass / X
  have hdata := sectionSixFirstDirectPair_finiteIndexData
    hepsilon hepsilonSmall hlength hindex
  have hpPrime : p.Prime := by simpa only [p] using hdata.1
  have hqPrime : q.Prime := by simpa only [q] using hdata.2.1
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
  have hqTwo : (2 : Real) <= q := by exact_mod_cast hqPrime.two_le
  have hXNat : 1 < XNat := by
    simpa only [XNat] using sectionSixFirst_direct_hXNat hlength
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogq : 0 < Real.log (q : Real) := Real.log_pos (by linarith)
  have hgap400 : 1 <= 400 * sectionSixThetaGap epsilon := by
    rw [sectionSixThetaGap_eq]
    linarith
  have hcapReal : (p : Real) * q * q <= X := by
    simpa only [X, XNat, p, q, Nat.cast_mul] using
      (show (((index.1 * index.2 * index.2 : Nat) : Real) <=
          ((10 ^ length : Nat) : Real)) by
        exact_mod_cast hdata.2.2.2.2.2)
  have hqY : (q : Real) <= Y := by
    dsimp only [Y]
    norm_num only [Nat.cast_mul]
    apply (le_div_iff₀ (mul_pos hpPos hqPos)).2
    nlinarith
  have hY : 0 < Y := hqPos.trans_le hqY
  have huOne : 1 <= u := by
    dsimp only [u]
    apply (le_div_iff₀ hlogq).2
    simpa only [one_mul] using Real.log_le_log hqPos hqY
  have hproductOne : (1 : Real) <= (p : Real) * q := by
    have hpOne : (1 : Real) <= p := by exact_mod_cast hpPrime.one_le
    have hqOne : (1 : Real) <= q := by exact_mod_cast hqPrime.one_le
    nlinarith
  have hYX : Y <= X := by
    dsimp only [Y]
    norm_num only [Nat.cast_mul]
    exact div_le_self (le_of_lt (zero_lt_one.trans hX)) hproductOne
  have hqLower : X ^ sectionSixThetaGap epsilon < (q : Real) := by
    simpa only [X, XNat, q] using hdata.2.2.2.1
  have hqLogb : sectionSixThetaGap epsilon < Real.logb X (q : Real) :=
    (Real.lt_logb_iff_rpow_lt hX hqPos).2 hqLower
  have hqLogLower : sectionSixThetaGap epsilon * Real.log X <=
      Real.log (q : Real) := by
    exact ((lt_div_iff₀ hlogX).1
      (by simpa only [Real.logb] using hqLogb)).le
  have huFourHundred : u <= 400 := by
    dsimp only [u]
    apply (div_le_iff₀ hlogq).2
    have hlogYX := Real.log_le_log hY hYX
    nlinarith
  have hroughAt := hrough Y (q : Real) u hY hqTwo huOne
    huFourHundred rfl
  have hd : (d : Real) = (p : Real) * q := by
    dsimp only [d]
    simp [PNat.mul_coe, Nat.toPNat'_coe, hpPrime.pos, hqPrime.pos,
      Nat.cast_mul]
  have hterm : sectionSixStrictPrimeTerm digit length
      (Nat.toPNat' p) q =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (q : Real)).card : Real) -
        lambda * (maynardStrictRoughCount Y (q : Real) : Real) := by
    rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
        (Nat.toPNat' p) hqPrime,
      sectionSixSiftedSum_eq_card_sub_density_mul_card,
      card_strictSiftedCarrier_sieveDilation_maynardAmbientCarrier d hqTwo]
    simp only [d, lambda, densityMass, X, XNat, div_eq_mul_inv, mul_assoc]
    rw [hd]
    congr 2
    dsimp only [Y, X, XNat]
    norm_num only [Nat.cast_mul]
    field_simp [hpPos.ne', hqPos.ne']
  have hdensity : (0 : Real) <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hlambda : 0 <= lambda := by
    dsimp only [lambda, densityMass, X]
    exact div_nonneg (mul_nonneg hdensity (by positivity)) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hroughAt hlambda
  have hmainScale : lambda *
      (buchstabFunction u * Y / Real.log (q : Real) +
        C * (Y / Real.log Y ^ 2)) =
      densityMass *
        (buchstabFunction u /
            ((p : Real) * q * Real.log (q : Real)) +
          C / ((p : Real) * q * Real.log Y ^ 2)) := by
    dsimp only [lambda, densityMass, Y, X]
    norm_num only [Nat.cast_mul]
    field_simp [hX.ne', hpPos.ne', hqPos.ne', hlogq.ne',
      (hlogq.trans_le (Real.log_le_log hqPos hqY)).ne']
  dsimp only [X, XNat, densityMass]
  simp only [sectionSixFirstPairProduct]
  rw [show sectionSixStrictPrimeTerm digit length
      (Nat.toPNat' index.1) index.2 =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (q : Real)).card : Real) -
        lambda * (maynardStrictRoughCount Y (q : Real) : Real) by
      simpa only [p, q] using hterm]
  have hrestricted : 0 <=
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (q : Real)).card : Real) := by positivity
  have hscaled' : lambda * (maynardStrictRoughCount Y (q : Real) : Real) <=
      densityMass *
        (buchstabFunction u /
            ((p : Real) * q * Real.log (q : Real)) +
          C / ((p : Real) * q * Real.log Y ^ 2)) := by
    rw [← hmainScale]
    exact hscaled
  dsimp only [u, Y, p, q] at hscaled' ⊢
  nlinarith

theorem exists_sectionSixFirstDirectPairFiniteLowerConstant :
    ∃ C : Real, 0 < C ∧
      ∀ (epsilon : Real), 0 < epsilon -> epsilon <= 1 / 64 ->
        ∀ {length : Nat}, 1 <= length -> ∀ (digit : Fin 10)
          (piece : SectionSixFirstPairPiece),
          IsSectionSixFirstDirectPairPiece piece ->
          let densityMass : Real :=
            (restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real);
          (-densityMass *
              (sectionSixFirstPairBuchstabMainSum epsilon length piece +
                C * sectionSixFirstPairRoughErrorSum epsilon length piece)) <=
            sectionSixFirstPairPieceSum epsilon digit length piece := by
  obtain ⟨C, hC, hrough⟩ :=
    exists_maynardStrictRoughCount_upper 400 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon hepsilonSmall length hlength digit piece _hpiece
  let X : Real := ((10 ^ length : Nat) : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  let indices := sectionSixFirstPairPieceIndices epsilon length piece
  have hpoint : ∀ index ∈ indices,
      -densityMass *
          (buchstabFunction
                (Real.log (X / (sectionSixFirstPairProduct index : Real)) /
                  Real.log (index.2 : Real)) /
              ((index.1 : Real) * (index.2 : Real) *
                Real.log (index.2 : Real)) +
            C / ((index.1 : Real) * (index.2 : Real) *
              Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2)) <=
        sectionSixStrictPrimeTerm digit length
          (Nat.toPNat' index.1) index.2 := by
    intro index hindex
    simpa only [densityMass, X, indices] using
      sectionSixFirstDirectPair_term_lower hrough hepsilon hepsilonSmall
        hlength digit hindex
  have hsumC :
      (∑ index ∈ indices,
        C / ((index.1 : Real) * (index.2 : Real) *
          Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2)) =
        C * (∑ index ∈ indices,
          1 / ((index.1 : Real) * (index.2 : Real) *
            Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index hindex
    ring
  dsimp only
  unfold sectionSixFirstPairBuchstabMainSum
    sectionSixFirstPairRoughErrorSum sectionSixFirstPairPieceSum
  change -densityMass *
      ((∑ index ∈ indices,
          buchstabFunction
              (Real.log (X / (sectionSixFirstPairProduct index : Real)) /
                Real.log (index.2 : Real)) /
            ((index.1 : Real) * (index.2 : Real) *
              Real.log (index.2 : Real))) +
        C * (∑ index ∈ indices,
          1 / ((index.1 : Real) * (index.2 : Real) *
            Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2))) <=
      ∑ index ∈ indices,
        sectionSixStrictPrimeTerm digit length
          (Nat.toPNat' index.1) index.2
  calc
    _ = ∑ index ∈ indices,
        -densityMass *
          (buchstabFunction
                (Real.log (X / (sectionSixFirstPairProduct index : Real)) /
                  Real.log (index.2 : Real)) /
              ((index.1 : Real) * (index.2 : Real) *
                Real.log (index.2 : Real)) +
            C / ((index.1 : Real) * (index.2 : Real) *
              Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsumC]
    _ <= _ := Finset.sum_le_sum fun index hindex => hpoint index hindex

end

end PrimesRestrictedDigits
