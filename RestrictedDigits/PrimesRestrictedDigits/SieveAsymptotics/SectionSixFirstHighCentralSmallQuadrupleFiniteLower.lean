import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleBuchstab
import PrimesRestrictedDigits.SieveDecomposition.RoughBridge
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstHighCentralSmallLedger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite lower bound for the high central-small quadruple term

The outer prime `s` is the strict roughness threshold after the fourth prime role. The full
strict sifted carrier, including its unit cofactor, is retained; only its nonnegative
restricted cardinality is discarded in the lower bound.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 145--146, Eq. (6.16).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstHighCentralSmallQuadruple_finiteIndexData
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstHighCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices
      epsilon length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    index.1.1.1.Prime ∧ index.1.1.2.Prime ∧ index.1.2.Prime ∧
      index.2.Prime ∧
      X ^ sectionSixThetaGap epsilon < (index.1.1.1 : Real) ∧
      X ^ sectionSixThetaGap epsilon < (index.1.1.2 : Real) ∧
      X ^ sectionSixThetaGap epsilon < (index.1.2 : Real) ∧
      X ^ sectionSixThetaGap epsilon < (index.2 : Real) ∧
      index.1.1.1 * index.1.1.2 * index.1.2 * index.2 * index.2 <
        10 ^ length := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  have hquad := mem_sectionSixFirstHighCentralSmallQuadrupleIndices.mp hindex
  have htriple :=
    mem_sectionSixFirstHighCentralSmallTripleIndices.mp hquad.1
  have hsData := mem_sievePrimeInterval.mp hquad.2
  have hrData := mem_sievePrimeInterval.mp htriple.2
  have hpairFiltered := Finset.mem_filter.mp htriple.1
  have hpiece :
      index.1.1 ∈ sectionSixFirstHighStrictIndices epsilon length ∧
        sectionSixZThree epsilon X <
            (sectionSixFirstPairProduct index.1.1 : Real) ∧
          (sectionSixFirstPairProduct index.1.1 : Real) <
              sectionSixZFive epsilon X ∧
            (sectionSixFirstPairSquareProduct index.1.1 : Real) <
              sectionSixZSix epsilon X := by
    simpa only [sectionSixFirstPairMem, X] using hpairFiltered.2
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hpData := mem_sievePrimeInterval.mp hpqData.1
  have hqData := mem_sievePrimeInterval.mp hpqData.2
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hcutoffs := sectionSix_cutoffs_strict
    hepsilon hepsilonSmall hX
  have hpLower : X ^ sectionSixThetaGap epsilon <
      (index.1.1.1 : Real) := by
    simpa only [sectionSixZOne, X] using
      (hcutoffs.1.trans hcutoffs.2.1).trans hpData.2.1
  have hcap :=
    (sectionSixFirstHighCentralSmall_quadruple_order_and_caps
      hepsilon hepsilonSmall hlength hindex).2.2.2.2
  exact ⟨hpData.1, hqData.1, hrData.1, hsData.1, hpLower,
    by simpa only [sectionSixZOne, X] using hqData.2.1,
    by simpa only [sectionSixZOne, X] using hrData.2.1,
    by simpa only [sectionSixZOne, X] using hsData.2.1, hcap⟩

private theorem
    sectionSixFirstHighCentralSmallQuadruple_buchstabParameter_bounds
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstHighCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices
      epsilon length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let Y : Real := X /
      ((sectionSixFirstHighCentralSmallTripleProduct index.1 * index.2 : Nat) :
        Real)
    let tau : Real := Real.log Y / Real.log (index.2 : Real)
    0 < Y ∧ (2 : Real) <= index.2 ∧ 1 <= tau ∧ tau <= 400 := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1.1.1
  let q : Nat := index.1.1.2
  let r : Nat := index.1.2
  let s : Nat := index.2
  let Y : Real := X /
    ((sectionSixFirstHighCentralSmallTripleProduct index.1 * s : Nat) : Real)
  let tau : Real := Real.log Y / Real.log (s : Real)
  rcases sectionSixFirstHighCentralSmallQuadruple_finiteIndexData
      hepsilon hepsilonSmall hlength hindex with
    ⟨hp, hq, hr, hs, _hpLower, _hqLower, _hrLower, hsLower, hcap⟩
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hq.pos
  have hrPos : (0 : Real) < r := by exact_mod_cast hr.pos
  have hsPos : (0 : Real) < s := by exact_mod_cast hs.pos
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hsTwo : (2 : Real) <= s := by exact_mod_cast hs.two_le
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hcapReal : (p : Real) * q * r * s * s < X := by
    dsimp only [X, XNat, p, q, r, s]
    exact_mod_cast hcap
  have hsY : (s : Real) < Y := by
    dsimp only [Y]
    simp only [sectionSixFirstHighCentralSmallTripleProduct,
      sectionSixFirstPairProduct]
    norm_num only [Nat.cast_mul]
    apply (lt_div_iff₀
      (mul_pos (mul_pos (mul_pos hpPos hqPos) hrPos) hsPos)).2
    nlinarith
  have hY : 0 < Y := hsPos.trans hsY
  have hlogs : 0 < Real.log (s : Real) :=
    Real.log_pos (by exact_mod_cast hs.one_lt)
  have htauOne : 1 <= tau := by
    dsimp only [tau]
    apply (le_div_iff₀ hlogs).2
    simpa only [one_mul] using Real.log_le_log hsPos hsY.le
  have hproductOne : (1 : Real) <= (p : Real) * q * r * s := by
    have hpOne : (1 : Real) <= p := by exact_mod_cast hp.one_le
    have hqOne : (1 : Real) <= q := by exact_mod_cast hq.one_le
    have hrOne : (1 : Real) <= r := by exact_mod_cast hr.one_le
    have hsOne : (1 : Real) <= s := by exact_mod_cast hs.one_le
    calc
      (1 : Real) = 1 * 1 * 1 * 1 := by norm_num
      _ <= (p : Real) * q * r * s := by gcongr
  have hYX : Y <= X := by
    dsimp only [Y]
    simp only [sectionSixFirstHighCentralSmallTripleProduct,
      sectionSixFirstPairProduct]
    norm_num only [Nat.cast_mul]
    exact div_le_self (le_of_lt (zero_lt_one.trans hX)) hproductOne
  have hsLogb : sectionSixThetaGap epsilon < Real.logb X (s : Real) :=
    (Real.lt_logb_iff_rpow_lt hX hsPos).2
      (by simpa only [X, XNat, s] using hsLower)
  have hsLogLower : sectionSixThetaGap epsilon * Real.log X <=
      Real.log (s : Real) :=
    ((lt_div_iff₀ hlogX).1
      (by simpa only [Real.logb] using hsLogb)).le
  have hgapFourHundred : 1 <= 400 * sectionSixThetaGap epsilon := by
    rw [sectionSixThetaGap_eq]
    linarith
  have htauFourHundred : tau <= 400 := by
    dsimp only [tau]
    apply (div_le_iff₀ hlogs).2
    have hlogYX := Real.log_le_log hY hYX
    nlinarith
  exact ⟨hY, by simpa only [s] using hsTwo, htauOne, htauFourHundred⟩

private theorem sectionSixFirstHighCentralSmallQuadruple_term_lower
    {C : Real} (hrough :
      ∀ Y y tau : Real, 0 < Y -> 2 <= y -> 1 <= tau -> tau <= 400 ->
        tau = Real.log Y / Real.log y ->
        (maynardStrictRoughCount Y y : Real) <=
          buchstabFunction tau * Y / Real.log y +
            C * (Y / Real.log Y ^ 2))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (digit : Fin 10)
    {index : SectionSixFirstHighCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices
      epsilon length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let densityMass : Real := (restrictedDigitDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real)
    (-densityMass *
        (buchstabFunction
              (Real.log (X /
                ((sectionSixFirstHighCentralSmallTripleProduct index.1 *
                  index.2 : Nat) : Real)) / Real.log (index.2 : Real)) /
            ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
              (index.1.2 : Real) * (index.2 : Real) *
                Real.log (index.2 : Real)) +
          C / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
            (index.1.2 : Real) * (index.2 : Real) *
            Real.log (X /
              ((sectionSixFirstHighCentralSmallTripleProduct index.1 *
                index.2 : Nat) : Real)) ^ 2))) <=
      sectionSixStrictPrimeTerm digit length
        (sectionSixFirstHighCentralSmallTripleModulus index.1) index.2 := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let p : Nat := index.1.1.1
  let q : Nat := index.1.1.2
  let r : Nat := index.1.2
  let s : Nat := index.2
  let tripleD : PNat := sectionSixFirstHighCentralSmallTripleModulus index.1
  let d : PNat := tripleD * Nat.toPNat' s
  let Y : Real := X /
    ((sectionSixFirstHighCentralSmallTripleProduct index.1 * s : Nat) : Real)
  let tau : Real := Real.log Y / Real.log (s : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  let lambda : Real := densityMass / X
  rcases sectionSixFirstHighCentralSmallQuadruple_finiteIndexData
      hepsilon hepsilonSmall hlength hindex with
    ⟨hp, hq, hr, hs, _hpLower, _hqLower, _hrLower, _hsLower, _hcap⟩
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hq.pos
  have hrPos : (0 : Real) < r := by exact_mod_cast hr.pos
  have hsPos : (0 : Real) < s := by exact_mod_cast hs.pos
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hparameter :=
    sectionSixFirstHighCentralSmallQuadruple_buchstabParameter_bounds
      hepsilon hepsilonSmall hlength hindex
  have hY : 0 < Y := by
    simpa only [X, XNat, Y, s] using hparameter.1
  have hsTwo : (2 : Real) <= s := by
    simpa only [s] using hparameter.2.1
  have htauOne : 1 <= tau := by
    simpa only [X, XNat, Y, s, tau] using hparameter.2.2.1
  have htauFourHundred : tau <= 400 := by
    simpa only [X, XNat, Y, s, tau] using hparameter.2.2.2
  have hlogs : 0 < Real.log (s : Real) :=
    Real.log_pos (by exact_mod_cast hs.one_lt)
  have hlogY : 0 < Real.log Y := by
    have hlog := (le_div_iff₀ hlogs).1 htauOne
    linarith
  have hroughAt := hrough Y (s : Real) tau hY hsTwo htauOne
    htauFourHundred rfl
  have hd : (d : Real) = (p : Real) * q * r * s := by
    dsimp only [d, tripleD]
    simp only [PNat.mul_coe, Nat.toPNat'_coe,
      sectionSixFirstHighCentralSmallTripleModulus,
      sectionSixFirstPairModulus, Nat.cast_mul]
    dsimp only [p, q, r, s]
    rw [if_pos hp.pos, if_pos hq.pos, if_pos hr.pos, if_pos hs.pos]
  have hYd : X / (d : Real) = Y := by
    rw [hd]
    dsimp only [Y]
    simp only [sectionSixFirstHighCentralSmallTripleProduct,
      sectionSixFirstPairProduct, Nat.cast_mul]
    dsimp only [p, q, r, s]
  have hYprod : Y = X / ((p : Real) * q * r * s) := by
    rw [← hYd, hd]
  have hterm : sectionSixStrictPrimeTerm digit length tripleD s =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (s : Real)).card : Real) -
        lambda * (maynardStrictRoughCount Y (s : Real) : Real) := by
    rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length tripleD hs,
      sectionSixSiftedSum_eq_card_sub_density_mul_card,
      card_strictSiftedCarrier_sieveDilation_maynardAmbientCarrier d hsTwo]
    rw [hYd]
    simp only [lambda, densityMass, X, XNat, div_eq_mul_inv, mul_assoc]
    congr 2
  have hdensity : (0 : Real) <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hlambda : 0 <= lambda := by
    dsimp only [lambda, densityMass, X]
    exact div_nonneg (mul_nonneg hdensity (by positivity)) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hroughAt hlambda
  have hlogYprod :
      0 < Real.log (X / ((p : Real) * q * r * s)) := by
    rw [← hYprod]
    exact hlogY
  have hmainScale : lambda *
      (buchstabFunction tau * Y / Real.log (s : Real) +
        C * (Y / Real.log Y ^ 2)) =
      densityMass *
        (buchstabFunction tau /
            ((p : Real) * q * r * s * Real.log (s : Real)) +
          C / ((p : Real) * q * r * s * Real.log Y ^ 2)) := by
    rw [hYprod]
    dsimp only [lambda, densityMass]
    field_simp [hX.ne', hpPos.ne', hqPos.ne', hrPos.ne', hsPos.ne',
      hlogs.ne', hlogYprod.ne']
  dsimp only [X, XNat, densityMass]
  rw [show sectionSixStrictPrimeTerm digit length
      (sectionSixFirstHighCentralSmallTripleModulus index.1) index.2 =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (s : Real)).card : Real) -
        lambda * (maynardStrictRoughCount Y (s : Real) : Real) by
      simpa only [tripleD, s] using hterm]
  have hrestricted : 0 <=
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
          (s : Real)).card : Real) := by positivity
  have hscaled' : lambda * (maynardStrictRoughCount Y (s : Real) : Real) <=
      densityMass *
        (buchstabFunction tau /
            ((p : Real) * q * r * s * Real.log (s : Real)) +
          C / ((p : Real) * q * r * s * Real.log Y ^ 2)) := by
    rw [← hmainScale]
    exact hscaled
  dsimp only [tau, Y, p, q, r, s] at hscaled' ⊢
  nlinarith

theorem exists_sectionSixFirstHighCentralSmallQuadrupleFiniteLowerConstant :
    ∃ C : Real, 0 < C ∧
      ∀ (epsilon : Real), 0 < epsilon -> epsilon <= 1 / 64 ->
        ∀ {length : Nat}, 1 <= length -> ∀ digit : Fin 10,
          let densityMass : Real :=
            (restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real)
          (-densityMass *
              (sectionSixFirstHighCentralSmallQuadrupleBuchstabMainSum
                  epsilon length +
                C * sectionSixFirstHighCentralSmallQuadrupleRoughErrorSum
                  epsilon length)) <=
            sectionSixFirstHighCentralSmallStrictQuadrupleSum
              epsilon digit length := by
  obtain ⟨C, hC, hrough⟩ :=
    exists_maynardStrictRoughCount_upper 400 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon hepsilonSmall length hlength digit
  let X : Real := ((10 ^ length : Nat) : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  let indices := sectionSixFirstHighCentralSmallQuadrupleIndices epsilon length
  have hpoint : ∀ index ∈ indices,
      -densityMass *
          (buchstabFunction
                (Real.log (X /
                  ((sectionSixFirstHighCentralSmallTripleProduct index.1 *
                    index.2 : Nat) : Real)) / Real.log (index.2 : Real)) /
              ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
                (index.1.2 : Real) * (index.2 : Real) *
                  Real.log (index.2 : Real)) +
            C / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
              (index.1.2 : Real) * (index.2 : Real) *
              Real.log (X /
                ((sectionSixFirstHighCentralSmallTripleProduct index.1 *
                  index.2 : Nat) : Real)) ^ 2)) <=
        sectionSixStrictPrimeTerm digit length
          (sectionSixFirstHighCentralSmallTripleModulus index.1) index.2 := by
    intro index hindex
    simpa only [densityMass, X, indices] using
      sectionSixFirstHighCentralSmallQuadruple_term_lower hrough
        hepsilon hepsilonSmall hlength digit hindex
  dsimp only
  unfold sectionSixFirstHighCentralSmallQuadrupleBuchstabMainSum
    sectionSixFirstHighCentralSmallQuadrupleRoughErrorSum
    sectionSixFirstHighCentralSmallStrictQuadrupleSum
  change -densityMass *
      ((∑ index ∈ indices,
        buchstabFunction
            (Real.log (X /
              ((sectionSixFirstHighCentralSmallTripleProduct index.1 *
                index.2 : Nat) : Real)) / Real.log (index.2 : Real)) /
          ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
            (index.1.2 : Real) * (index.2 : Real) *
              Real.log (index.2 : Real))) +
      C * (∑ index ∈ indices,
        1 / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
          (index.1.2 : Real) * (index.2 : Real) *
          Real.log (X /
            ((sectionSixFirstHighCentralSmallTripleProduct index.1 *
              index.2 : Nat) : Real)) ^ 2))) <=
    ∑ index ∈ indices,
      sectionSixStrictPrimeTerm digit length
        (sectionSixFirstHighCentralSmallTripleModulus index.1) index.2
  calc
    _ = ∑ index ∈ indices,
        -densityMass *
          (buchstabFunction
                (Real.log (X /
                  ((sectionSixFirstHighCentralSmallTripleProduct index.1 *
                    index.2 : Nat) : Real)) / Real.log (index.2 : Real)) /
              ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
                (index.1.2 : Real) * (index.2 : Real) *
                  Real.log (index.2 : Real)) +
            C / ((index.1.1.1 : Real) * (index.1.1.2 : Real) *
              (index.1.2 : Real) * (index.2 : Real) *
              Real.log (X /
                ((sectionSixFirstHighCentralSmallTripleProduct index.1 *
                  index.2 : Nat) : Real)) ^ 2)) := by
      rw [← Finset.mul_sum]
      apply congrArg (fun value : Real => -densityMass * value)
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro index _hindex
      ring
    _ <= _ := Finset.sum_le_sum fun index hindex => hpoint index hindex

end

end PrimesRestrictedDigits
