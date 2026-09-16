import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralSmallLedger
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstRepeatedFiniteBound
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Low central-small second repeated bound

The complete second repeated key on the raw reduced quadruple carrier is charged, with
familywise multiplicity, to the common quarter-tie carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def secondKey
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) : Nat :=
  sectionSixFirstRepeatedKey
    (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2

private def secondTuple
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) : Fin 5 -> Nat :=
  ![index.2, index.2, index.1.2, index.1.1.2, index.1.1.1]

private theorem lowSmallPairData
    {epsilon : Real} {length : Nat} {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralSmall) :
    index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
        (sectionSixFirstPairProduct index : Real) ∧
      (sectionSixFirstPairProduct index : Real) <
        sectionSixZFive epsilon ((10 ^ length : Nat) : Real) ∧
      (sectionSixFirstPairSquareProduct index : Real) <
        sectionSixZSix epsilon ((10 ^ length : Nat) : Real) := by
  classical
  have hpiece := (Finset.mem_filter.mp hindex).2
  simpa only [sectionSixFirstPairMem] using hpiece

private theorem secondData
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices
      epsilon length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    index.1.1.1.Prime ∧ index.1.1.2.Prime ∧ index.1.2.Prime ∧
      index.2.Prime ∧
      X ^ sectionSixThetaGap epsilon < (index.2 : Real) ∧
      index.2 <= index.1.2 ∧ index.1.2 <= index.1.1.2 ∧
      index.1.1.2 <= index.1.1.1 ∧
      (index.2 : Real) <= X ^ (1 / 2 : Real) ∧
      weakRoughPredicate (X ^ sectionSixThetaGap epsilon)
        (sectionSixFirstLowCentralSmallTripleModulus index.1 : Nat) ∧
      sectionSixFirstLowCentralSmallTripleProduct index.1 * index.2 *
          index.2 <= 10 ^ length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hquad := mem_sectionSixFirstLowCentralSmallRawQuadrupleIndices.mp hindex
  have htriple := mem_sectionSixFirstLowCentralSmallTripleIndices.mp hquad.1
  have hpiece := lowSmallPairData htriple.1
  have hpq := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hp := mem_sievePrimeInterval.mp hpq.1
  have hq := mem_sievePrimeInterval.mp hpq.2
  have hr := mem_sievePrimeInterval.mp htriple.2
  have hs := mem_sievePrimeInterval.mp hquad.2
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hcutoffs := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  have hsr : index.2 <= index.1.2 := by
    exact_mod_cast hs.2.2.trans (min_le_left _ _)
  have hrq : index.1.2 <= index.1.1.2 := by
    exact_mod_cast hr.2.2
  have hqp : index.1.1.2 <= index.1.1.1 := by
    exact_mod_cast hq.2.2.trans (min_le_left _ _)
  have hsHalf : (index.2 : Real) <= X ^ (1 / 2 : Real) := by
    exact (calc
      (index.2 : Real) <= index.1.2 := by exact_mod_cast hsr
      _ <= index.1.1.2 := by exact_mod_cast hrq
      _ <= index.1.1.1 := by exact_mod_cast hqp
      _ <= sectionSixZTwo epsilon X := by simpa only [X] using hp.2.2
      _ < sectionSixZThree epsilon X := hcutoffs.2.1
      _ < sectionSixZFour X := hcutoffs.2.2.1
      _ = X ^ (1 / 2 : Real) := sectionSixZFour_eq_rpow X).le
  have hdRough : weakRoughPredicate (X ^ sectionSixThetaGap epsilon)
      (sectionSixFirstLowCentralSmallTripleModulus index.1 : Nat) := by
    rw [sectionSixFirstLowCentralSmallTripleModulus_coe hp.1 hq.1 hr.1]
    simp only [sectionSixFirstLowCentralSmallTripleProduct,
      sectionSixFirstPairProduct]
    intro a ha hadvd
    rcases ha.dvd_mul.mp hadvd with hapq | har
    · rcases ha.dvd_mul.mp hapq with hap | haq
      · have haEq := (Nat.prime_dvd_prime_iff_eq ha hp.1).mp hap
        subst a
        simpa only [X, sectionSixZOne] using hp.2.1.le
      · have haEq := (Nat.prime_dvd_prime_iff_eq ha hq.1).mp haq
        subst a
        simpa only [X, sectionSixZOne] using hq.2.1.le
    · have haEq := (Nat.prime_dvd_prime_iff_eq ha hr.1).mp har
      subst a
      simpa only [X, sectionSixZOne] using hr.2.1.le
  have hcap := (sectionSixFirstLowCentralSmall_le_tripleTerminalThreshold_iff
    hp.1 hq.1 hr.1 hs.1).mp (hs.2.2.trans (min_le_right _ _))
  exact ⟨hp.1, hq.1, hr.1, hs.1,
    by simpa only [X, sectionSixZOne] using hs.2.1,
    hsr, hrq, hqp, hsHalf, hdRough, hcap⟩

private theorem secondKey_eq
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices
      epsilon length) :
    secondKey index =
      index.1.1.1 * index.1.1.2 * index.1.2 * index.2 * index.2 := by
  have h := secondData hepsilon hepsilonSmall hlength hindex
  unfold secondKey
  rw [sectionSixFirstRepeatedKey_eq _ h.2.2.2.1,
    sectionSixFirstLowCentralSmallTripleModulus_coe h.1 h.2.1 h.2.2.1]
  simp only [sectionSixFirstLowCentralSmallTripleProduct,
    sectionSixFirstPairProduct]

private theorem secondTuple_prime
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices
      epsilon length) : ∀ i, (secondTuple index i).Prime := by
  have h := secondData hepsilon hepsilonSmall hlength hindex
  intro i
  fin_cases i <;>
    simp [secondTuple, h.1, h.2.1, h.2.2.1, h.2.2.2.1]

private theorem secondTuple_monotone
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices
      epsilon length) : Monotone (secondTuple index) := by
  have h := secondData hepsilon hepsilonSmall hlength hindex
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [secondTuple] at hij ⊢ <;> omega

private theorem secondTuple_product
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices
      epsilon length) :
    primeTupleProduct (secondTuple index) = secondKey index := by
  rw [secondKey_eq hepsilon hepsilonSmall hlength hindex]
  simp [secondTuple, primeTupleProduct, Fin.prod_univ_succ]
  ring

private theorem secondKey_injOn
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (length : Nat) (hlength : 1 <= length) :
    Set.InjOn secondKey
      (sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length :
        Set SectionSixFirstLowCentralSmallQuadrupleIndex) := by
  intro i hi j hj hkey
  have hproduct : primeTupleProduct (secondTuple i) =
      primeTupleProduct (secondTuple j) := by
    rw [secondTuple_product hepsilon hepsilonSmall hlength hi,
      secondTuple_product hepsilon hepsilonSmall hlength hj, hkey]
  have htuple := eq_of_monotone_primeTupleProduct_eq
    (secondTuple_prime hepsilon hepsilonSmall hlength hi)
    (secondTuple_prime hepsilon hepsilonSmall hlength hj)
    (secondTuple_monotone hepsilon hepsilonSmall hlength hi)
    (secondTuple_monotone hepsilon hepsilonSmall hlength hj) hproduct
  have hs : i.2 = j.2 := by
    simpa [secondTuple] using congrFun htuple (0 : Fin 5)
  have hr : i.1.2 = j.1.2 := by
    simpa [secondTuple] using congrFun htuple (2 : Fin 5)
  have hq : i.1.1.2 = j.1.1.2 := by
    simpa [secondTuple] using congrFun htuple (3 : Fin 5)
  have hp : i.1.1.1 = j.1.1.1 := by
    simpa [secondTuple] using congrFun htuple (4 : Fin 5)
  rcases i with ⟨⟨⟨ip, iq⟩, ir⟩, is⟩
  rcases j with ⟨⟨⟨jp, jq⟩, jr⟩, js⟩
  simp only at hp hq hr hs
  subst jp
  subst jq
  subst jr
  subst js
  rfl

private theorem sum_second_le
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length : Nat} (hlength : 1 <= length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfive : 5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let gap : Real := sectionSixThetaGap epsilon
    let K : Nat := 2 ^ Nat.ceil (1 / gap)
    (∑ index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length,
      ((sectionSixFirstRepeatedRepresentedCarrier C
        (sectionSixFirstLowCentralSmallTripleModulus index.1)
        index.2).card : Real)) <=
      (K : Real) *
        ((sectionSixDirectQuarterTieCarrier C X gap).card : Real) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let states := sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length
  let carrier : SectionSixFirstLowCentralSmallQuadrupleIndex -> Finset Nat :=
    fun index => sectionSixFirstRepeatedRepresentedCarrier C
      (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hgap : 0 < gap :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hfamily : ∀ index ∈ states,
      index.2.Prime ∧ X ^ gap < (index.2 : Real) ∧
      (index.2 : Real) <= X ^ (1 / 2 : Real) ∧
      weakRoughPredicate (X ^ gap)
        (sectionSixFirstLowCentralSmallTripleModulus index.1 : Nat) := by
    intro index hindex
    have h := secondData hepsilon hepsilonSmall hlength
      (by simpa only [states] using hindex)
    exact ⟨h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩
  have hsub : ∀ index ∈ states, carrier index ⊆
      sectionSixDirectQuarterTieCarrier C X gap := by
    intro index hindex
    have h := hfamily index hindex
    exact sectionSixFirstRepeatedRepresentedCarrier_subset_quarterTie
      (by simpa only [X, gap] using hfive) h.1 h.2.1 h.2.2.1 h.2.2.2
  have hfiber : ∀ n, n ∈ sectionSixDirectQuarterTieCarrier C X gap ->
      (states.filter fun index => n ∈ carrier index).card <=
        2 ^ Nat.ceil (1 / gap) := by
    intro n _hn
    apply sectionSixFirstRepeatedCarrierFiber_le states secondKey carrier
      hX hgap C hC
    · intro index hindex n hn
      have h := hfamily index hindex
      have hnData := sectionSixFirstRepeatedRepresentedCarrier_mem_data
        (by simpa only [X, gap] using hfive) h.1 h.2.1 h.2.2.2
        (by simpa only [carrier] using hn)
      exact ⟨hnData.1, hnData.2.1,
        by simpa only [secondKey] using hnData.2.2.1,
        hnData.2.2.2.2⟩
    · exact secondKey_injOn epsilon hepsilon hepsilonSmall length hlength
  simpa only [states, carrier, X, gap] using
    (sum_card_le_of_element_fiber_card_real states
      (sectionSixDirectQuarterTieCarrier C X gap) carrier
      (2 ^ Nat.ceil (1 / gap)) hsub hfiber)

/-- The low central-small second repeated family costs one divisor-candidate
factor times the common quarter-tie charge. -/
theorem abs_sectionSixFirstLowCentralSmallSecondRepeatedSum_le_quarterTieCharge
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let K : Nat := 2 ^ Nat.ceil (1 / sectionSixThetaGap epsilon)
    abs (sectionSixFirstLowCentralSmallSecondRepeatedSum
      epsilon digit length) <=
      (K : Real) *
        sectionSixDirectQuarterTieCharge digit length
          (sectionSixThetaGap epsilon) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let K : Nat := 2 ^ Nat.ceil (1 / gap)
  let states := sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length
  have hrestricted := sum_second_le epsilon hepsilon hepsilonSmall
    (paddedRestrictedNumbers digit length) hlength
    (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length) hfive
  have hambient := sum_second_le epsilon hepsilon hepsilonSmall
    (maynardAmbientCarrier X) hlength (fun _ hn => hn) hfive
  unfold sectionSixFirstLowCentralSmallSecondRepeatedSum
  apply abs_sectionSixFirstRepeatedIndexSum_le_quarterTieCharge
    digit length gap K states
      (fun index => sectionSixFirstLowCentralSmallTripleModulus index.1)
      (fun index => index.2)
  · intro index hindex
    exact (mem_sievePrimeInterval.mp
      (mem_sectionSixFirstLowCentralSmallRawQuadrupleIndices.mp hindex).2).1
  · simpa only [states, X, gap, K] using hrestricted
  · simpa only [states, X, gap, K] using hambient

end

end PrimesRestrictedDigits
