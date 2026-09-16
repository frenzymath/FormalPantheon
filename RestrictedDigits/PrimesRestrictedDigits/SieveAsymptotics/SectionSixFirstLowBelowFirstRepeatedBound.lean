import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowBelowLedger
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstRepeatedFiniteBound
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# First low-below repeated-prime bound

The first repeated residual is controlled familywise by the direct quarter-tie charge. Its
complete key is `p * q * r ^ 2`, represented by the ordered prime tuple `[r, r, q, p]`.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, repeated displays immediately before
and through Eq. (6.13).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem lowBelowPairData
    {epsilon : Real} {length : Nat} {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowBelow) :
    index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      sectionSixZOne epsilon ((10 ^ length : Nat) : Real) <
        (sectionSixFirstPairProduct index : Real) ∧
      (sectionSixFirstPairProduct index : Real) <
        sectionSixZTwo epsilon ((10 ^ length : Nat) : Real) := by
  classical
  have hpiece := (Finset.mem_filter.mp hindex).2
  simpa only [sectionSixFirstPairMem] using hpiece

private def firstRepeatedKey
    (index : SectionSixFirstLowBelowTripleIndex) : Nat :=
  sectionSixFirstRepeatedKey (sectionSixFirstPairModulus index.1) index.2

private def firstRepeatedPrimeTuple
    (index : SectionSixFirstLowBelowTripleIndex) : Fin 4 -> Nat :=
  ![index.2, index.2, index.1.2, index.1.1]

private theorem firstRepeatedData
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowBelowTripleIndex}
    (hindex : index ∈ sectionSixFirstLowBelowTripleIndices
      epsilon length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    index.1.1.Prime ∧ index.1.2.Prime ∧ index.2.Prime ∧
      X ^ sectionSixThetaGap epsilon < (index.2 : Real) ∧
      index.2 <= index.1.2 ∧ index.1.2 <= index.1.1 ∧
      (index.2 : Real) <= X ^ (1 / 2 : Real) ∧
      weakRoughPredicate (X ^ sectionSixThetaGap epsilon)
        (sectionSixFirstPairModulus index.1 : Nat) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have htriple := mem_sectionSixFirstLowBelowTripleIndices.mp hindex
  have hpiece := lowBelowPairData htriple.1
  have hpq := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hp := mem_sievePrimeInterval.mp hpq.1
  have hq := mem_sievePrimeInterval.mp hpq.2
  have hr := mem_sievePrimeInterval.mp htriple.2
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hcutoffs := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  have hrq : index.2 <= index.1.2 := by exact_mod_cast hr.2.2
  have hqp : index.1.2 <= index.1.1 := by
    exact_mod_cast hq.2.2.trans (min_le_left _ _)
  have hrHalf : (index.2 : Real) <= X ^ (1 / 2 : Real) := by
    exact (calc
      (index.2 : Real) <= index.1.2 := by exact_mod_cast hrq
      _ <= index.1.1 := by exact_mod_cast hqp
      _ <= sectionSixZTwo epsilon X := by simpa only [X] using hp.2.2
      _ < sectionSixZThree epsilon X := hcutoffs.2.1
      _ < sectionSixZFour X := hcutoffs.2.2.1
      _ = X ^ (1 / 2 : Real) := sectionSixZFour_eq_rpow X).le
  have hdRough : weakRoughPredicate (X ^ sectionSixThetaGap epsilon)
      (sectionSixFirstPairModulus index.1 : Nat) := by
    rw [sectionSixFirstPairModulus_coe hp.1 hq.1]
    intro a ha hadvd
    rcases ha.dvd_mul.mp hadvd with hap | haq
    · have haEq : a = index.1.1 :=
        (Nat.prime_dvd_prime_iff_eq ha hp.1).mp hap
      subst a
      simpa only [X, sectionSixZOne] using hp.2.1.le
    · have haEq : a = index.1.2 :=
        (Nat.prime_dvd_prime_iff_eq ha hq.1).mp haq
      subst a
      simpa only [X, sectionSixZOne] using hq.2.1.le
  exact ⟨hp.1, hq.1, hr.1,
    by simpa only [X, sectionSixZOne] using hr.2.1,
    hrq, hqp, hrHalf, hdRough⟩

private theorem firstRepeatedKey_eq
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowBelowTripleIndex}
    (hindex : index ∈ sectionSixFirstLowBelowTripleIndices
      epsilon length) :
    firstRepeatedKey index = index.1.1 * index.1.2 * index.2 * index.2 := by
  have h := firstRepeatedData hepsilon hepsilonSmall hlength hindex
  unfold firstRepeatedKey
  rw [sectionSixFirstRepeatedKey_eq _ h.2.2.1,
    sectionSixFirstPairModulus_coe h.1 h.2.1]
  simp only [sectionSixFirstPairProduct]

private theorem firstRepeatedPrimeTuple_prime
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowBelowTripleIndex}
    (hindex : index ∈ sectionSixFirstLowBelowTripleIndices
      epsilon length) :
    ∀ i, (firstRepeatedPrimeTuple index i).Prime := by
  have h := firstRepeatedData hepsilon hepsilonSmall hlength hindex
  intro i
  fin_cases i <;>
    simp [firstRepeatedPrimeTuple, h.1, h.2.1, h.2.2.1]

private theorem firstRepeatedPrimeTuple_monotone
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowBelowTripleIndex}
    (hindex : index ∈ sectionSixFirstLowBelowTripleIndices
      epsilon length) :
    Monotone (firstRepeatedPrimeTuple index) := by
  have h := firstRepeatedData hepsilon hepsilonSmall hlength hindex
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [firstRepeatedPrimeTuple] at hij ⊢ <;> omega

private theorem firstRepeatedPrimeTuple_product
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstLowBelowTripleIndex}
    (hindex : index ∈ sectionSixFirstLowBelowTripleIndices
      epsilon length) :
    primeTupleProduct (firstRepeatedPrimeTuple index) =
      firstRepeatedKey index := by
  rw [firstRepeatedKey_eq hepsilon hepsilonSmall hlength hindex]
  simp [firstRepeatedPrimeTuple, primeTupleProduct, Fin.prod_univ_succ]
  ring

private theorem firstRepeatedKey_injOn
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (length : Nat) (hlength : 1 <= length) :
    Set.InjOn firstRepeatedKey
      (sectionSixFirstLowBelowTripleIndices epsilon length :
        Set SectionSixFirstLowBelowTripleIndex) := by
  intro i hi j hj hkey
  have hproduct : primeTupleProduct (firstRepeatedPrimeTuple i) =
      primeTupleProduct (firstRepeatedPrimeTuple j) := by
    rw [firstRepeatedPrimeTuple_product hepsilon hepsilonSmall hlength hi,
      firstRepeatedPrimeTuple_product hepsilon hepsilonSmall hlength hj,
      hkey]
  have htuple := eq_of_monotone_primeTupleProduct_eq
    (firstRepeatedPrimeTuple_prime hepsilon hepsilonSmall hlength hi)
    (firstRepeatedPrimeTuple_prime hepsilon hepsilonSmall hlength hj)
    (firstRepeatedPrimeTuple_monotone hepsilon hepsilonSmall hlength hi)
    (firstRepeatedPrimeTuple_monotone hepsilon hepsilonSmall hlength hj)
    hproduct
  have hr : i.2 = j.2 := by
    simpa [firstRepeatedPrimeTuple] using congrFun htuple (0 : Fin 4)
  have hq : i.1.2 = j.1.2 := by
    simpa [firstRepeatedPrimeTuple] using congrFun htuple (2 : Fin 4)
  have hp : i.1.1 = j.1.1 := by
    simpa [firstRepeatedPrimeTuple] using congrFun htuple (3 : Fin 4)
  rcases i with ⟨⟨ip, iq⟩, ir⟩
  rcases j with ⟨⟨jp, jq⟩, jr⟩
  simp only at hp hq hr
  subst jp
  subst jq
  subst jr
  rfl

private theorem sum_firstRepeatedRepresentedCarrier_le_quarterTie
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length : Nat} (hlength : 1 <= length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let gap : Real := sectionSixThetaGap epsilon
    let K : Nat := 2 ^ Nat.ceil (1 / gap)
    (∑ index ∈ sectionSixFirstLowBelowTripleIndices epsilon length,
      ((sectionSixFirstRepeatedRepresentedCarrier C
        (sectionSixFirstPairModulus index.1) index.2).card : Real)) <=
      (K : Real) *
        ((sectionSixDirectQuarterTieCarrier C X gap).card : Real) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let states := sectionSixFirstLowBelowTripleIndices epsilon length
  let carrier : SectionSixFirstLowBelowTripleIndex -> Finset Nat :=
    fun index => sectionSixFirstRepeatedRepresentedCarrier C
      (sectionSixFirstPairModulus index.1) index.2
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
        (sectionSixFirstPairModulus index.1 : Nat) := by
    intro index hindex
    have h := firstRepeatedData hepsilon hepsilonSmall hlength
      (by simpa only [states] using hindex)
    exact ⟨h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
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
    apply sectionSixFirstRepeatedCarrierFiber_le
      states firstRepeatedKey carrier hX hgap C hC
    · intro index hindex n hn
      have h := hfamily index hindex
      have hnData := sectionSixFirstRepeatedRepresentedCarrier_mem_data
        (by simpa only [X, gap] using hfive) h.1 h.2.1 h.2.2.2
        (by simpa only [carrier] using hn)
      exact ⟨hnData.1, hnData.2.1,
        by simpa only [firstRepeatedKey] using hnData.2.2.1,
        hnData.2.2.2.2⟩
    · exact firstRepeatedKey_injOn
        epsilon hepsilon hepsilonSmall length hlength
  simpa only [states, carrier, X, gap] using
    (sum_card_le_of_element_fiber_card_real states
      (sectionSixDirectQuarterTieCarrier C X gap) carrier
      (2 ^ Nat.ceil (1 / gap)) hsub hfiber)

/-- The first low-below repeated residual is absorbed familywise by
the direct quarter-tie charge with multiplicity `2 ^ ceil (1 / gap)`. -/
theorem abs_sectionSixFirstLowBelowFirstRepeatedSum_le_quarterTieCharge
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let K : Nat := 2 ^ Nat.ceil (1 / sectionSixThetaGap epsilon)
    abs (sectionSixFirstLowBelowFirstRepeatedSum epsilon digit length) <=
      (K : Real) *
        sectionSixDirectQuarterTieCharge digit length
          (sectionSixThetaGap epsilon) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let K : Nat := 2 ^ Nat.ceil (1 / gap)
  let states := sectionSixFirstLowBelowTripleIndices epsilon length
  have hrestricted := sum_firstRepeatedRepresentedCarrier_le_quarterTie
    epsilon hepsilon hepsilonSmall
    (paddedRestrictedNumbers digit length) hlength
    (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length) hfive
  have hambient := sum_firstRepeatedRepresentedCarrier_le_quarterTie
    epsilon hepsilon hepsilonSmall
    (maynardAmbientCarrier X) hlength (fun _ hn => hn) hfive
  unfold sectionSixFirstLowBelowFirstRepeatedSum
  apply abs_sectionSixFirstRepeatedIndexSum_le_quarterTieCharge
    digit length gap K states
      (fun index => sectionSixFirstPairModulus index.1) (fun index => index.2)
  · intro index hindex
    exact (mem_sievePrimeInterval.mp
      (mem_sectionSixFirstLowBelowTripleIndices.mp hindex).2).1
  · simpa only [states, X, gap, K] using hrestricted
  · simpa only [states, X, gap, K] using hambient

end

end PrimesRestrictedDigits
