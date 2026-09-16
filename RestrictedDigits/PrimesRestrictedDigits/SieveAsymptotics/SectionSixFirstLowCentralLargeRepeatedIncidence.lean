import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeIndices
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstRepeatedIncidence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Low central-large repeated-continuation incidence

The complete repeated keys over the low central-large continuation are injective, and their
represented carriers are bounded by one divisor-candidate factor times the common quarter-tie
carrier.

Source: MAYNARD-PRD-PUBLISHED, Section 6, pp. 141--142, after Eq. (6.8).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The complete key `(p * q) * r^2` attached to a low central-large
continuation state. -/
def sectionSixFirstLowCentralLargeRepeatedKey
    (index : SectionSixFirstPairContinuationIndex) : Nat :=
  sectionSixFirstRepeatedKey
    (sectionSixFirstPairModulus index.1) index.2

/-- Values represented by the repeated correction at one low central-large
continuation state. -/
noncomputable def sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier
    (C : Finset Nat)
    (index : SectionSixFirstPairContinuationIndex) : Finset Nat :=
  sectionSixFirstRepeatedRepresentedCarrier C
    (sectionSixFirstPairModulus index.1) index.2

private theorem sectionSixFirstLowCentralLarge_repeatedContinuationData
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationIndices epsilon length) :
    index.1.1.Prime ∧ index.1.2.Prime ∧ index.2.Prime ∧
      sectionSixZOne epsilon ((10 ^ length : Nat) : Real) <
        (index.1.2 : Real) ∧
      index.1.2 <= index.1.1 ∧ index.1.2 < index.2 ∧
      (index.2 : Real) <=
        sectionSixFirstPairTerminalThreshold length index.1 := by
  have hmain :=
    mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hindex
  have hfiltered :
      index.1 ∈ sectionSixFirstStrictIndices epsilon length ∧
        sectionSixFirstPairMem epsilon length .lowCentralLarge index.1 := by
    classical
    simpa [sectionSixFirstPairPieceIndices] using hmain.1
  have hpiece :
      index.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
        sectionSixZThree epsilon (((10 ^ length : Nat) : Real)) <
          (sectionSixFirstPairProduct index.1 : Real) ∧
        (sectionSixFirstPairProduct index.1 : Real) <
          sectionSixZFive epsilon (((10 ^ length : Nat) : Real)) ∧
        sectionSixZSix epsilon (((10 ^ length : Nat) : Real)) <=
          (sectionSixFirstPairSquareProduct index.1 : Real) := by
    simpa [sectionSixFirstPairMem] using hfiltered.2
  have hpq := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hp := mem_sievePrimeInterval.mp hpq.1
  have hq := mem_sievePrimeInterval.mp hpq.2
  have hr := mem_sievePrimeInterval.mp hmain.2
  have hqp : index.1.2 <= index.1.1 := by
    have hthreshold : sectionSixFirstFactorThreshold length index.1.1 <=
        (index.1.1 : Real) := min_le_left _ _
    exact_mod_cast hq.2.2.trans hthreshold
  exact ⟨hp.1, hq.1, hr.1, hq.2.1, hqp,
    by exact_mod_cast hr.2.1, hr.2.2⟩

private theorem sectionSixFirstLowCentralLargeRepeatedKey_eq
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationIndices epsilon length) :
    sectionSixFirstLowCentralLargeRepeatedKey index =
      sectionSixFirstPairProduct index.1 * index.2 * index.2 := by
  have hdata :=
    sectionSixFirstLowCentralLarge_repeatedContinuationData hindex
  unfold sectionSixFirstLowCentralLargeRepeatedKey
  rw [sectionSixFirstRepeatedKey_eq
      (sectionSixFirstPairModulus index.1) hdata.2.2.1,
    sectionSixFirstPairModulus_coe hdata.1 hdata.2.1]

private theorem sectionSixFirstLowCentralLarge_repeatedPrime_le_half
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationIndices epsilon length) :
    (index.2 : Real) <=
      ((10 ^ length : Nat) : Real) ^ (1 / 2 : Real) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hdata :=
    sectionSixFirstLowCentralLarge_repeatedContinuationData hindex
  have hproductOne :
      (1 : Real) <= (sectionSixFirstPairProduct index.1 : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hdata.1.ne_zero hdata.2.1.ne_zero))
  have hquot : X / (sectionSixFirstPairProduct index.1 : Real) <= X :=
    div_le_self (by positivity) hproductOne
  have hsqrt := Real.sqrt_le_sqrt hquot
  rw [sectionSixFirstPairTerminalThreshold] at hdata
  change (index.2 : Real) <= X ^ (1 / 2 : Real)
  rw [← Real.sqrt_eq_rpow]
  exact hdata.2.2.2.2.2.2.trans hsqrt

private theorem sectionSixFirstLowCentralLarge_pairModulus_rough
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationIndices epsilon length) :
    weakRoughPredicate
      (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
      (sectionSixFirstPairModulus index.1 : Nat) := by
  have hdata :=
    sectionSixFirstLowCentralLarge_repeatedContinuationData hindex
  rw [sectionSixFirstPairModulus_coe hdata.1 hdata.2.1]
  intro s hs hsdvd
  rcases hs.dvd_mul.mp hsdvd with hsp | hsq
  · have hspeq : s = index.1.1 :=
      (Nat.prime_dvd_prime_iff_eq hs hdata.1).mp hsp
    subst s
    exact hdata.2.2.2.1.le.trans
      (by exact_mod_cast hdata.2.2.2.2.1)
  · have hsqeq : s = index.1.2 :=
      (Nat.prime_dvd_prime_iff_eq hs hdata.2.1).mp hsq
    simpa only [hsqeq] using hdata.2.2.2.1.le

private def sectionSixFirstLowCentralLarge_repeatedPrimeTuple
    (index : SectionSixFirstPairContinuationIndex) : Fin 4 -> Nat :=
  if index.2 <= index.1.1 then
    ![index.1.2, index.2, index.2, index.1.1]
  else
    ![index.1.2, index.1.1, index.2, index.2]

private theorem sectionSixFirstLowCentralLarge_repeatedPrimeTuple_prime
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationIndices epsilon length) :
    ∀ i, (sectionSixFirstLowCentralLarge_repeatedPrimeTuple index i).Prime := by
  have hdata :=
    sectionSixFirstLowCentralLarge_repeatedContinuationData hindex
  intro i
  by_cases hrp : index.2 <= index.1.1 <;>
    fin_cases i <;>
      simp [sectionSixFirstLowCentralLarge_repeatedPrimeTuple, hrp,
        hdata.1, hdata.2.1, hdata.2.2.1]

private theorem sectionSixFirstLowCentralLarge_repeatedPrimeTuple_monotone
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationIndices epsilon length) :
    Monotone (sectionSixFirstLowCentralLarge_repeatedPrimeTuple index) := by
  have hdata :=
    sectionSixFirstLowCentralLarge_repeatedContinuationData hindex
  by_cases hrp : index.2 <= index.1.1
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [sectionSixFirstLowCentralLarge_repeatedPrimeTuple, hrp] at hij ⊢ <;>
        omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [sectionSixFirstLowCentralLarge_repeatedPrimeTuple, hrp] at hij ⊢ <;>
        omega

private theorem sectionSixFirstLowCentralLarge_repeatedPrimeTuple_product
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationIndices epsilon length) :
    primeTupleProduct
      (sectionSixFirstLowCentralLarge_repeatedPrimeTuple index) =
        sectionSixFirstLowCentralLargeRepeatedKey index := by
  rw [sectionSixFirstLowCentralLargeRepeatedKey_eq hindex]
  by_cases hrp : index.2 <= index.1.1 <;>
    simp [sectionSixFirstLowCentralLarge_repeatedPrimeTuple, hrp,
      primeTupleProduct, Fin.prod_univ_succ, sectionSixFirstPairProduct] <;>
    ring

/-- The complete repeated key is injective on the full low central-large
continuation, including the tie `r = p`. -/
theorem sectionSixFirstLowCentralLargeRepeatedKey_injOn
    (epsilon : Real) (length : Nat) :
    Set.InjOn sectionSixFirstLowCentralLargeRepeatedKey
      (sectionSixFirstLowCentralLargeContinuationIndices epsilon length :
        Set SectionSixFirstPairContinuationIndex) := by
  intro i hi j hj hkey
  have hproduct :
      primeTupleProduct
          (sectionSixFirstLowCentralLarge_repeatedPrimeTuple i) =
        primeTupleProduct
          (sectionSixFirstLowCentralLarge_repeatedPrimeTuple j) := by
    rw [sectionSixFirstLowCentralLarge_repeatedPrimeTuple_product hi,
      sectionSixFirstLowCentralLarge_repeatedPrimeTuple_product hj, hkey]
  have htuple := eq_of_monotone_primeTupleProduct_eq
    (sectionSixFirstLowCentralLarge_repeatedPrimeTuple_prime hi)
    (sectionSixFirstLowCentralLarge_repeatedPrimeTuple_prime hj)
    (sectionSixFirstLowCentralLarge_repeatedPrimeTuple_monotone hi)
    (sectionSixFirstLowCentralLarge_repeatedPrimeTuple_monotone hj)
    hproduct
  have hq : i.1.2 = j.1.2 := by
    have h := congrFun htuple (0 : Fin 4)
    by_cases hiOrder : i.2 <= i.1.1 <;>
      by_cases hjOrder : j.2 <= j.1.1 <;>
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
  by_cases hiOrder : i.2 <= i.1.1
  · by_cases hjOrder : j.2 <= j.1.1
    · have hr : i.2 = j.2 := by
        have h := congrFun htuple (1 : Fin 4)
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
      have hp : i.1.1 = j.1.1 := by
        have h := congrFun htuple (3 : Fin 4)
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
      rcases i with ⟨⟨ip, iq⟩, ir⟩
      rcases j with ⟨⟨jp, jq⟩, jr⟩
      simp only at hp hq hr
      subst jp
      subst jq
      subst jr
      rfl
    · have hirEqJp : i.2 = j.1.1 := by
        have h := congrFun htuple (1 : Fin 4)
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
      have hirEqJr : i.2 = j.2 := by
        have h := congrFun htuple (2 : Fin 4)
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
      exact False.elim (hjOrder (by omega))
  · by_cases hjOrder : j.2 <= j.1.1
    · have hipEqJr : i.1.1 = j.2 := by
        have h := congrFun htuple (1 : Fin 4)
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
      have hirEqJr : i.2 = j.2 := by
        have h := congrFun htuple (2 : Fin 4)
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
      exact False.elim (hiOrder (by omega))
    · have hp : i.1.1 = j.1.1 := by
        have h := congrFun htuple (1 : Fin 4)
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
      have hr : i.2 = j.2 := by
        have h := congrFun htuple (2 : Fin 4)
        simpa [sectionSixFirstLowCentralLarge_repeatedPrimeTuple,
          hiOrder, hjOrder] using h
      rcases i with ⟨⟨ip, iq⟩, ir⟩
      rcases j with ⟨⟨jp, jq⟩, jr⟩
      simp only at hp hq hr
      subst jp
      subst jq
      subst jr
      rfl

/-- The represented continuation carriers incur exactly one
divisor-candidate factor when charged to the common quarter-tie carrier. -/
theorem
    sum_card_sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier_le_quarterTie
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length : Nat} (hlength : 1 <= length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let gap : Real := sectionSixThetaGap epsilon
    let K : Nat := 2 ^ Nat.ceil (1 / gap)
    (∑ index ∈
        sectionSixFirstLowCentralLargeContinuationIndices epsilon length,
      ((sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier
        C index).card : Real)) <=
      (K : Real) *
        ((sectionSixDirectQuarterTieCarrier C X gap).card : Real) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let states :=
    sectionSixFirstLowCentralLargeContinuationIndices epsilon length
  let carrier : SectionSixFirstPairContinuationIndex -> Finset Nat :=
    sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier C
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hgap : 0 < gap :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hfamilyData : ∀ index ∈ states,
      index.2.Prime ∧ X ^ gap < (index.2 : Real) ∧
        (index.2 : Real) <= X ^ (1 / 2 : Real) ∧
        weakRoughPredicate (X ^ gap)
          (sectionSixFirstPairModulus index.1 : Nat) := by
    intro index hindex
    have hdata :=
      sectionSixFirstLowCentralLarge_repeatedContinuationData hindex
    have hqr : (index.1.2 : Real) < (index.2 : Real) := by
      exact_mod_cast hdata.2.2.2.2.2.1
    have hrLower : X ^ gap < (index.2 : Real) := by
      have hqLower : X ^ gap < (index.1.2 : Real) := by
        simpa only [X, gap, sectionSixZOne] using hdata.2.2.2.1
      exact hqLower.trans hqr
    exact ⟨hdata.2.2.1, hrLower,
      sectionSixFirstLowCentralLarge_repeatedPrime_le_half hindex,
      by simpa only [X, gap, sectionSixZOne] using
        sectionSixFirstLowCentralLarge_pairModulus_rough hindex⟩
  have hsub : ∀ index ∈ states, carrier index ⊆
      sectionSixDirectQuarterTieCarrier C X gap := by
    intro index hindex
    have hdata := hfamilyData index hindex
    simpa only [carrier,
      sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier] using
      (sectionSixFirstRepeatedRepresentedCarrier_subset_quarterTie
        (by simpa only [X, gap] using hfive)
        hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2)
  have hfiber : ∀ n, n ∈ sectionSixDirectQuarterTieCarrier C X gap ->
      (states.filter fun index => n ∈ carrier index).card <=
        2 ^ Nat.ceil (1 / gap) := by
    intro n _hn
    apply sectionSixFirstRepeatedCarrierFiber_le states
      sectionSixFirstLowCentralLargeRepeatedKey carrier hX hgap C hC
    · intro index hindex n hn
      have hfamily := hfamilyData index hindex
      have hnData := sectionSixFirstRepeatedRepresentedCarrier_mem_data
        (by simpa only [X, gap] using hfive)
        hfamily.1 hfamily.2.1 hfamily.2.2.2
        (by simpa only [carrier,
          sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier] using hn)
      exact ⟨hnData.1, hnData.2.1,
        by simpa only [sectionSixFirstLowCentralLargeRepeatedKey] using
          hnData.2.2.1,
        hnData.2.2.2.2⟩
    · exact sectionSixFirstLowCentralLargeRepeatedKey_injOn epsilon length
  simpa only [states, carrier, X, gap] using
    (sum_card_le_of_element_fiber_card_real states
      (sectionSixDirectQuarterTieCarrier C X gap) carrier
      (2 ^ Nat.ceil (1 / gap)) hsub hfiber)

end

end PrimesRestrictedDigits
