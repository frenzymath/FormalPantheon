import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStrictCarrier
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDivisorIncidence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixIncidenceAggregation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIPrimeTupleMultiplicity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Incidence bounds for direct strict Section 6 terms

The strict represented carrier keeps the complete `d*q` key. Its key is injective on the
accepted direct index set, so the fixed source-scale rough factor bound gives one
`2^ceil(1/delta)` incidence coefficient. The final lemmas retain an arbitrary near Finset for
the later composition.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixDirectStrictKey_weakRough
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    weakRoughPredicate
      (((10 ^ length : Nat) : Real) ^ delta)
      (sectionSixDirectStrictKey index) := by
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
  rw [sectionSixDirectStrictKey_eq hindex] at hrKey
  rcases hr.dvd_mul.mp hrKey with hrOuter | hrQ
  · exact (houter r hr hrOuter).le
  · have hrEq : r = index.2 :=
      (Nat.prime_dvd_prime_iff_eq hr hqData.1).mp hrQ
    simpa only [hrEq] using hqLower.le

/-- Every represented strict member retains its carrier membership, positivity,
complete-key divisibility, and weak roughness at the fixed source scale. -/
theorem sectionSixDirectStrictRepresentedCarrier_mem_data
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell} {C : Finset Nat} {n : Nat}
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band)
    (hn : n ∈ sectionSixDirectStrictRepresentedCarrier C index) :
    n ∈ C ∧ 0 < n ∧ sectionSixDirectStrictKey index ∣ n ∧
      weakRoughPredicate (((10 ^ length : Nat) : Real) ^ delta) n := by
  rcases mem_sectionSixDirectStrictRepresentedCarrier.mp hn with
    ⟨m, hm, hmn⟩
  have hmData : m ∈ sieveDilation C (sectionSixDirectStrictModulus index) ∧
      strictRoughPredicate (index.2 : Real) m := by
    simpa [sectionSixDirectStrictCofactorCarrier] using
      (mem_strictSiftedCarrier.mp hm)
  have hmCarrier : m * sectionSixDirectStrictKey index ∈ C := by
    simpa [sectionSixDirectStrictKey] using (mem_sieveDilation.mp hmData.1)
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have hqData := mem_sievePrimeInterval.mp hindexData.2
  have hqLower : ((10 ^ length : Nat) : Real) ^ delta <
      (index.2 : Real) := hqData.2.1
  have hmPos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hmZero
    subst m
    have hzero := strictRoughPredicate_zero.mp hmData.2
    linarith
  have hkeyPos : 0 < sectionSixDirectStrictKey index := by
    exact (sectionSixDirectStrictModulus index).pos
  have hkeyDvd : sectionSixDirectStrictKey index ∣ n := by
    refine ⟨m, ?_⟩
    simpa [Nat.mul_comm] using hmn.symm
  have hmRough : weakRoughPredicate
      (((10 ^ length : Nat) : Real) ^ delta) m := by
    intro r hr hrm
    exact (hqLower.le.trans_lt (hmData.2 r hr hrm)).le
  have hkeyRough := sectionSixDirectStrictKey_weakRough
    hlength hdeltaGapStrict hindex
  have hnRough : weakRoughPredicate
      (((10 ^ length : Nat) : Real) ^ delta) n := by
    intro r hr hrn
    rw [← hmn] at hrn
    rcases hr.dvd_mul.mp hrn with hrm | hrKey
    · exact hmRough r hr hrm
    · exact hkeyRough r hr hrKey
  refine ⟨?_, ?_, hkeyDvd, hnRough⟩
  · simpa only [hmn] using hmCarrier
  · rw [← hmn]
    exact Nat.mul_pos hmPos hkeyPos

/-- At one represented natural, accepted strict indices have at most the
source-scale divisor-candidate multiplicity. -/
theorem card_sectionSixDirectStrictRepresentedCarrier_fiber_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (n : Nat) :
    ((sectionSixDirectRepeatedIndices epsilon delta ell region length band).filter
      (fun index => n ∈ sectionSixDirectStrictRepresentedCarrier C index)).card ≤
      2 ^ Nat.ceil (1 / delta) := by
  classical
  let states := sectionSixDirectRepeatedIndices
    epsilon delta ell region length band
  let selected := states.filter fun index =>
    n ∈ sectionSixDirectStrictRepresentedCarrier C index
  change selected.card ≤ _
  by_cases hselected : selected = ∅
  · simp [hselected]
  · obtain ⟨witness, hwitness⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hselected
    have hwitnessData := Finset.mem_filter.mp hwitness
    have hnData := sectionSixDirectStrictRepresentedCarrier_mem_data
      hlength hdeltaGapStrict hy hwitnessData.1 hwitnessData.2
    let X : Real := ((10 ^ length : Nat) : Real)
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hnX : (n : Real) <= X := by
      exact (mem_maynardAmbientCarrier.mp (hC hnData.1)).le
    have hcandidates :=
      card_sectionSixDivisorCandidates_le_two_pow_ceil_inv_delta
        hX hdelta (Nat.ne_of_gt hnData.2.1) hnX hnData.2.2.2
    have hmaps : Set.MapsTo sectionSixDirectStrictKey
        (selected : Set (SectionSixDirectStrictIndex ell))
        (sectionSixDivisorCandidates n : Set Nat) := by
      intro index hindex
      have hindexData := Finset.mem_filter.mp hindex
      have hrepresented := sectionSixDirectStrictRepresentedCarrier_mem_data
        hlength hdeltaGapStrict hy hindexData.1 hindexData.2
      exact mem_sectionSixDivisorCandidates_of_dvd
        (Nat.ne_of_gt hnData.2.1) hrepresented.2.2.1
    have hinj : Set.InjOn sectionSixDirectStrictKey
        (selected : Set (SectionSixDirectStrictIndex ell)) := by
      intro i hi j hj hij
      exact sectionSixDirectStrictKey_injOn
        epsilon delta ell length region band
        (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
    exact (Finset.card_le_card_of_injOn
      sectionSixDirectStrictKey hmaps hinj).trans hcandidates

private theorem sectionSixDirectStrictRepresentedCarrier_sdiff_subset
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell} {C near : Finset Nat}
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    sectionSixDirectStrictRepresentedCarrier C index \ near ⊆ C \ near := by
  intro n hn
  have hdata := sectionSixDirectStrictRepresentedCarrier_mem_data
    hlength hdeltaGapStrict hy hindex (Finset.mem_sdiff.mp hn).1
  exact Finset.mem_sdiff.mpr ⟨hdata.1, (Finset.mem_sdiff.mp hn).2⟩

private theorem card_sectionSixDirectStrictRepresentedCarrier_sdiff_fiber_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixDirectBand) (C near : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (n : Nat) :
    ((sectionSixDirectRepeatedIndices epsilon delta ell region length band).filter
      (fun index =>
        n ∈ sectionSixDirectStrictRepresentedCarrier C index \ near)).card ≤
      2 ^ Nat.ceil (1 / delta) := by
  apply (Finset.card_le_card ?_).trans
    (card_sectionSixDirectStrictRepresentedCarrier_fiber_le
      region hlength hdelta hdeltaGapStrict band C hC hy n)
  intro index hindex
  have hdata := Finset.mem_filter.mp hindex
  exact Finset.mem_filter.mpr ⟨hdata.1, (Finset.mem_sdiff.mp hdata.2).1⟩

/-- Natural-cardinality aggregation for an arbitrary near carrier. -/
theorem sum_card_sectionSixDirectStrictRepresentedCarrier_sdiff_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixDirectBand) (C near : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ index ∈ sectionSixDirectRepeatedIndices
        epsilon delta ell region length band,
      (sectionSixDirectStrictRepresentedCarrier C index \ near).card) ≤
      2 ^ Nat.ceil (1 / delta) * (C \ near).card := by
  apply sum_card_le_of_element_fiber_card
    (sectionSixDirectRepeatedIndices epsilon delta ell region length band)
    (C \ near)
    (fun index => sectionSixDirectStrictRepresentedCarrier C index \ near)
    (2 ^ Nat.ceil (1 / delta))
  · intro index hindex n hn
    exact sectionSixDirectStrictRepresentedCarrier_sdiff_subset
      hlength hdeltaGapStrict hy hindex hn
  · intro n hn
    exact card_sectionSixDirectStrictRepresentedCarrier_sdiff_fiber_le
      region hlength hdelta hdeltaGapStrict band C near hC hy n

/-- Real-cardinality aggregation for an arbitrary near carrier. -/
theorem sum_card_sectionSixDirectStrictRepresentedCarrier_sdiff_real_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixDirectBand) (C near : Finset Nat)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta) :
    (∑ index ∈ sectionSixDirectRepeatedIndices
        epsilon delta ell region length band,
      ((sectionSixDirectStrictRepresentedCarrier C index \ near).card : Real)) ≤
      ((2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        ((C \ near).card : Real) := by
  apply sum_card_le_of_element_fiber_card_real
    (sectionSixDirectRepeatedIndices epsilon delta ell region length band)
    (C \ near)
    (fun index => sectionSixDirectStrictRepresentedCarrier C index \ near)
    (2 ^ Nat.ceil (1 / delta))
  · intro index hindex n hn
    exact sectionSixDirectStrictRepresentedCarrier_sdiff_subset
      hlength hdeltaGapStrict hy hindex hn
  · intro n hn
    exact card_sectionSixDirectStrictRepresentedCarrier_sdiff_fiber_le
      region hlength hdelta hdeltaGapStrict band C near hC hy n

end

end PrimesRestrictedDigits
