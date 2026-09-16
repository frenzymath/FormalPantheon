import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectRepeatedCarrier
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixCoprimeSquarefulCarrier
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDivisorIncidence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixIncidenceAggregation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIPrimeTupleMultiplicity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Incidence bounds for direct repeated Section 6 terms

Represented integers retain the complete key `d*q^2`, while the common carriers remember only
the repeated square. Injectivity of the complete key and the divisor-candidate bound give
exactly one factor `2^ceil(1/delta)`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixDirectRepeatedKey_weakRough
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell}
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    weakRoughPredicate
      (((10 ^ length : Nat) : Real) ^ delta)
      (sectionSixDirectRepeatedKey index) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  have hpData := (mem_propositionSixOnePrimeTuples.mp htuple).2
  have houter : strictRoughPredicate (X ^ delta)
      (primeTupleProduct index.1) := by
    apply strictRoughPredicate_primeTupleProduct hpData.1
    intro i
    exact (Real.rpow_lt_rpow_of_exponent_lt hX hdeltaGapStrict).trans_le
      (by simpa only [X] using hpData.2.2.1 i)
  have hqData := mem_sievePrimeInterval.mp hindexData.2
  have hqLower : X ^ delta < (index.2 : Real) := by
    simpa only [X] using hqData.2.1
  intro r hr hrKey
  rw [sectionSixDirectRepeatedKey_eq hindex] at hrKey
  rcases hr.dvd_mul.mp hrKey with hrOuterQ | hrQ
  · rcases hr.dvd_mul.mp hrOuterQ with hrOuter | hrQ
    · exact (houter r hr hrOuter).le
    · have hrEq : r = index.2 :=
        (Nat.prime_dvd_prime_iff_eq hr hqData.1).mp hrQ
      simpa only [hrEq] using hqLower.le
  · have hrEq : r = index.2 :=
      (Nat.prime_dvd_prime_iff_eq hr hqData.1).mp hrQ
    simpa only [hrEq] using hqLower.le

/-- A represented member retains its source carrier, positivity, complete-key
divisibility, repeated square, and weak roughness at the source scale. -/
theorem sectionSixDirectRepeatedRepresentedCarrier_mem_data
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell} {C : Finset Nat} {n : Nat}
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band)
    (hn : n ∈ sectionSixDirectRepeatedRepresentedCarrier C index) :
    n ∈ C ∧ 0 < n ∧ sectionSixDirectRepeatedKey index ∣ n ∧
      index.2 * index.2 ∣ n ∧
        weakRoughPredicate
          (((10 ^ length : Nat) : Real) ^ delta) n := by
  rcases mem_sectionSixDirectRepeatedRepresentedCarrier.mp hn with
    ⟨m, hm, hmn⟩
  have hmData : m ∈ sieveDilation C (sectionSixDirectRepeatedModulus index) ∧
      weakRoughPredicate (index.2 : Real) m := by
    simpa [sectionSixDirectRepeatedCofactorCarrier] using
      (mem_weakSiftedCarrier.mp hm)
  have hmCarrier : m * sectionSixDirectRepeatedKey index ∈ C := by
    simpa [sectionSixDirectRepeatedKey] using
      (mem_sieveDilation.mp hmData.1)
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have hqData := mem_sievePrimeInterval.mp hindexData.2
  have hqLower : ((10 ^ length : Nat) : Real) ^ delta <
      (index.2 : Real) := hqData.2.1
  have hmPos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hmZero
    subst m
    have hzero := weakRoughPredicate_zero.mp hmData.2
    linarith
  have hkeyPos : 0 < sectionSixDirectRepeatedKey index := by
    exact (sectionSixDirectRepeatedModulus index).pos
  have hkeyDvd : sectionSixDirectRepeatedKey index ∣ n := by
    refine ⟨m, ?_⟩
    simpa [Nat.mul_comm] using hmn.symm
  have hqSqKey : index.2 * index.2 ∣
      sectionSixDirectRepeatedKey index := by
    refine ⟨primeTupleProduct index.1, ?_⟩
    rw [sectionSixDirectRepeatedKey_eq hindex]
    ring
  have hmRough : weakRoughPredicate
      (((10 ^ length : Nat) : Real) ^ delta) m := by
    intro r hr hrm
    exact hqLower.le.trans (hmData.2 r hr hrm)
  have hkeyRough := sectionSixDirectRepeatedKey_weakRough
    hlength hdeltaGapStrict hindex
  have hnRough : weakRoughPredicate
      (((10 ^ length : Nat) : Real) ^ delta) n := by
    intro r hr hrn
    rw [← hmn] at hrn
    rcases hr.dvd_mul.mp hrn with hrm | hrKey
    · exact hmRough r hr hrm
    · exact hkeyRough r hr hrKey
  refine ⟨?_, ?_, hkeyDvd, hqSqKey.trans hkeyDvd, hnRough⟩
  · simpa only [hmn] using hmCarrier
  · rw [← hmn]
    exact Nat.mul_pos hmPos hkeyPos

/-- The represented carrier lies in the common coprime squareful carrier.
Strictness above five is used only for decimal coprimality. -/
theorem sectionSixDirectRepeatedRepresentedCarrier_subset_coprimeSquareful
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell} {C : Finset Nat}
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    sectionSixDirectRepeatedRepresentedCarrier C index ⊆
      sectionSixRepeatedCoprimeSquarefulCarrier C
        ((10 ^ length : Nat) : Real) delta
          (sectionSixThetaGap epsilon) := by
  intro n hn
  have hnData := sectionSixDirectRepeatedRepresentedCarrier_mem_data
    hlength hdeltaGapStrict hy hindex hn
  have hq := (mem_sectionSixDirectRepeatedIndices.mp hindex).2
  have hnTen := weakRoughPredicate_coprime_ten_of_five_lt
    hy hnData.2.2.2.2
  exact mem_sectionSixRepeatedCoprimeSquarefulCarrier.mpr
    ⟨hnData.1, hnTen, index.2, hq, hnData.2.2.2.1⟩

/-- The same represented carrier lies in the positive squareful carrier used
for the ambient contribution. -/
theorem sectionSixDirectRepeatedRepresentedCarrier_subset_squareful
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell} {C : Finset Nat}
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    sectionSixDirectRepeatedRepresentedCarrier C index ⊆
      sectionSixRepeatedSquarefulCarrier C
        ((10 ^ length : Nat) : Real) delta
          (sectionSixThetaGap epsilon) := by
  intro n hn
  have hnData := sectionSixDirectRepeatedRepresentedCarrier_mem_data
    hlength hdeltaGapStrict hy hindex hn
  have hq := (mem_sectionSixDirectRepeatedIndices.mp hindex).2
  exact mem_sectionSixRepeatedSquarefulCarrier.mpr
    ⟨hnData.1, hnData.2.1, index.2, hq, hnData.2.2.2.1⟩

/--
At one represented integer, complete-key injectivity and give the exact direct-index incidence
coefficient `2^ceil(1/delta)`.
-/
theorem card_sectionSixDirectRepeatedRepresentedCarrier_fiber_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (n : Nat) :
    ((sectionSixDirectRepeatedIndices epsilon delta ell region length band).filter
      (fun index => n ∈
        sectionSixDirectRepeatedRepresentedCarrier C index)).card <=
      2 ^ Nat.ceil (1 / delta) := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  let states := sectionSixDirectRepeatedIndices
    epsilon delta ell region length band
  let selected := states.filter fun index =>
    n ∈ sectionSixDirectRepeatedRepresentedCarrier C index
  change selected.card <= _
  by_cases hselected : selected = ∅
  · simp [hselected]
  · obtain ⟨witness, hwitness⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hselected
    have hwitnessData := Finset.mem_filter.mp hwitness
    have hnData := sectionSixDirectRepeatedRepresentedCarrier_mem_data
      hlength hdeltaGapStrict hy hwitnessData.1 hwitnessData.2
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hnX : (n : Real) <= X := by
      exact (mem_maynardAmbientCarrier.mp (hC hnData.1)).le
    have hcandidates :=
      card_sectionSixDivisorCandidates_le_two_pow_ceil_inv_delta
        hX hdelta (Nat.ne_of_gt hnData.2.1) hnX hnData.2.2.2.2
    have hmaps : Set.MapsTo sectionSixDirectRepeatedKey
        (selected : Set (SectionSixDirectRepeatedIndex ell))
        (sectionSixDivisorCandidates n : Set Nat) := by
      intro index hindex
      have hindexData := Finset.mem_filter.mp hindex
      have hrepresented := sectionSixDirectRepeatedRepresentedCarrier_mem_data
        hlength hdeltaGapStrict hy hindexData.1 hindexData.2
      exact mem_sectionSixDivisorCandidates_of_dvd
        (Nat.ne_of_gt hnData.2.1) hrepresented.2.2.1
    have hinj : Set.InjOn sectionSixDirectRepeatedKey
        (selected : Set (SectionSixDirectRepeatedIndex ell)) := by
      intro i hi j hj hij
      exact sectionSixDirectRepeatedKey_injOn
        epsilon delta ell length region band
        (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
    exact (Finset.card_le_card_of_injOn
      sectionSixDirectRepeatedKey hmaps hinj).trans hcandidates

/--
applied to the exact direct represented carriers and the common coprime squareful carrier.
-/
theorem sum_card_sectionSixDirectRepeatedRepresentedCarrier_coprime_real_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ index ∈ sectionSixDirectRepeatedIndices
        epsilon delta ell region length band,
      ((sectionSixDirectRepeatedRepresentedCarrier C index).card : Real)) <=
      ((2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        ((sectionSixRepeatedCoprimeSquarefulCarrier C
          ((10 ^ length : Nat) : Real) delta
            (sectionSixThetaGap epsilon)).card : Real) := by
  classical
  apply sum_card_le_of_element_fiber_card_real
  · intro index hindex
    exact sectionSixDirectRepeatedRepresentedCarrier_subset_coprimeSquareful
      hlength hdeltaGapStrict hy hindex
  · intro n hn
    exact card_sectionSixDirectRepeatedRepresentedCarrier_fiber_le
      region hlength hdelta hdeltaGapStrict band C hC hy n

/--
applied to the exact direct represented carriers and the common positive squareful carrier.
-/
theorem sum_card_sectionSixDirectRepeatedRepresentedCarrier_ambient_real_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ index ∈ sectionSixDirectRepeatedIndices
        epsilon delta ell region length band,
      ((sectionSixDirectRepeatedRepresentedCarrier C index).card : Real)) <=
      ((2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        ((sectionSixRepeatedSquarefulCarrier C
          ((10 ^ length : Nat) : Real) delta
            (sectionSixThetaGap epsilon)).card : Real) := by
  classical
  apply sum_card_le_of_element_fiber_card_real
  · intro index hindex
    exact sectionSixDirectRepeatedRepresentedCarrier_subset_squareful
      hlength hdeltaGapStrict hy hindex
  · intro n hn
    exact card_sectionSixDirectRepeatedRepresentedCarrier_fiber_le
      region hlength hdelta hdeltaGapStrict band C hC hy n

end

end PrimesRestrictedDigits
