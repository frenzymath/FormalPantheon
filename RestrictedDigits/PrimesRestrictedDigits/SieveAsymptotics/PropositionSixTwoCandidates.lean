import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoContract
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite candidates for Proposition 6.2

This module contains only the exact Sigma occurrence carrier and its finite
cardinality/discrepancy identities. Stable factorization and analytic transfer are downstream.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The positive displayed modulus used by the strict cofactor dilation. -/
def propositionSixTwoModulus {ell : Nat} (p : Fin ell -> Nat) : PNat :=
  (primeTupleProduct p).toPNat'

/-- Strict rough cofactors for one displayed tuple. -/
noncomputable def propositionSixTwoCofactorCarrier
    (C : Finset Nat) {ell : Nat} (j : Fin ell) (p : Fin ell -> Nat) :
    Finset Nat :=
  strictSiftedCarrier (sieveDilation C (propositionSixTwoModulus p))
    (p j : Real)

/-- An outer tuple together with one strict rough cofactor. -/
abbrev PropositionSixTwoCandidate (ell : Nat) :=
  Sigma fun _ : (Fin ell -> Nat) => Nat

namespace PropositionSixTwoCandidate

/-- The represented integer of one candidate occurrence. -/
def value {ell : Nat} (candidate : PropositionSixTwoCandidate ell) : Nat :=
  candidate.2 * (propositionSixTwoModulus candidate.1 : Nat)

end PropositionSixTwoCandidate

/-- All strict Proposition 6.2 occurrences over one finite carrier. -/
noncomputable def propositionSixTwoCandidates
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    Finset (PropositionSixTwoCandidate ell) :=
  (propositionSixTwoPrimeTuples epsilon ell I j region length band).sigma
    (fun p => propositionSixTwoCofactorCarrier C j p)

/-- Strict occurrences whose represented value is near the cutoff. -/
noncomputable def propositionSixTwoNearCandidates
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (rho : Real) (C : Finset Nat) :
    Finset (PropositionSixTwoCandidate ell) :=
  (propositionSixTwoCandidates epsilon ell I j region length band C).filter
    (fun candidate =>
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho)

/-- Strict occurrences outside the near cutoff carrier. -/
noncomputable def propositionSixTwoOutsideNearCandidates
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (rho : Real) (C : Finset Nat) :
    Finset (PropositionSixTwoCandidate ell) :=
  (propositionSixTwoCandidates epsilon ell I j region length band C).filter
    (fun candidate =>
      candidate.value ∉ typeIINearXCarrier (10 ^ length) rho)

@[simp] theorem mem_propositionSixTwoCofactorCarrier
    {C : Finset Nat} {ell : Nat} {j : Fin ell}
    {p : Fin ell -> Nat} {m : Nat} :
    m ∈ propositionSixTwoCofactorCarrier C j p <->
      m ∈ sieveDilation C (propositionSixTwoModulus p) ∧
        strictRoughPredicate (p j : Real) m := by
  simp [propositionSixTwoCofactorCarrier]

@[simp] theorem mem_propositionSixTwoCandidates
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell} :
    candidate ∈ propositionSixTwoCandidates epsilon ell I j region length band C <->
      candidate.1 ∈ propositionSixTwoPrimeTuples epsilon ell I j region length
        band ∧
      candidate.2 ∈ propositionSixTwoCofactorCarrier C j candidate.1 := by
  simp [propositionSixTwoCandidates]

@[simp] theorem mem_propositionSixTwoNearCandidates
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell} :
    candidate ∈ propositionSixTwoNearCandidates epsilon ell I j region length
        band rho C <->
      candidate ∈ propositionSixTwoCandidates epsilon ell I j region length
        band C ∧
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho := by
  simp [propositionSixTwoNearCandidates]

@[simp] theorem mem_propositionSixTwoOutsideNearCandidates
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell} :
    candidate ∈ propositionSixTwoOutsideNearCandidates epsilon ell I j region
        length band rho C <->
      candidate ∈ propositionSixTwoCandidates epsilon ell I j region length
        band C ∧
      candidate.value ∉ typeIINearXCarrier (10 ^ length) rho := by
  simp [propositionSixTwoOutsideNearCandidates]

/-- The positive modulus is the literal displayed product on accepted tuples. -/
theorem coe_propositionSixTwoModulus_eq_primeTupleProduct_of_mem
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {p : Fin ell -> Nat}
    (hp : p ∈ propositionSixTwoPrimeTuples
      epsilon ell I j region length band) :
    (propositionSixTwoModulus p : Nat) = primeTupleProduct p :=
  coe_toPNat'_primeTupleProduct_of_mem_propositionSixTwoPrimeTuples hp

/-- Candidate values are literal `m*d` on the accepted outer carrier. -/
theorem PropositionSixTwoCandidate.value_eq_mul_primeTupleProduct_of_mem
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hcandidate : candidate ∈ propositionSixTwoCandidates
      epsilon ell I j region length band C) :
    candidate.value = candidate.2 * primeTupleProduct candidate.1 := by
  rw [PropositionSixTwoCandidate.value,
    coe_propositionSixTwoModulus_eq_primeTupleProduct_of_mem
      (mem_propositionSixTwoCandidates.mp hcandidate).1]

/-- Restricting the represented carrier changes only dilation membership. -/
theorem mem_propositionSixTwoCofactorCarrier_iff_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    {ell : Nat} {j : Fin ell} {p : Fin ell -> Nat} {m : Nat} :
    m ∈ propositionSixTwoCofactorCarrier C j p <->
      m ∈ propositionSixTwoCofactorCarrier B j p ∧
        m * (propositionSixTwoModulus p : Nat) ∈ C := by
  simp only [mem_propositionSixTwoCofactorCarrier, mem_sieveDilation]
  constructor
  · rintro ⟨hmC, hmRough⟩
    exact ⟨⟨hCB hmC, hmRough⟩, hmC⟩
  · rintro ⟨⟨_hmB, hmRough⟩, hmC⟩
    exact ⟨hmC, hmRough⟩

/-- Zero cannot be a strict cofactor at an accepted prime threshold. -/
theorem zero_not_mem_propositionSixTwoCofactorCarrier_of_outer_mem
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat} {p : Fin ell -> Nat}
    (hp : p ∈ propositionSixTwoPrimeTuples
      epsilon ell I j region length band) :
    0 ∉ propositionSixTwoCofactorCarrier C j p := by
  intro hzero
  have hrough := (mem_propositionSixTwoCofactorCarrier.mp hzero).2
  have hlt : (p j : Real) < 2 :=
    strictRoughPredicate_zero.mp hrough
  have hpData := mem_propositionSixTwoPrimeTuples_iff_source.mp hp
  dsimp [IsPropositionSixTwoPrimeTuple] at hpData
  have htwo : (2 : Real) <= (p j : Real) := by
    exact_mod_cast (hpData.1 j).two_le
  exact (not_lt_of_ge htwo) hlt

/-- The unit cofactor is present exactly when the displayed modulus is. -/
@[simp] theorem one_mem_propositionSixTwoCofactorCarrier
    (C : Finset Nat) {ell : Nat} (j : Fin ell) (p : Fin ell -> Nat) :
    1 ∈ propositionSixTwoCofactorCarrier C j p <->
      (propositionSixTwoModulus p : Nat) ∈ C := by
  simp [propositionSixTwoCofactorCarrier]

/-- Sigma occurrences have the sum of their exact cofactor cardinalities. -/
theorem card_propositionSixTwoCandidates_eq_sum_cofactorCard
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    (propositionSixTwoCandidates epsilon ell I j region length band C).card =
      ∑ p ∈ propositionSixTwoPrimeTuples epsilon ell I j region length band,
        (propositionSixTwoCofactorCarrier C j p).card := by
  exact Finset.card_sigma _ _

/-- Restricting the represented carrier is exactly a candidate-value filter. -/
theorem propositionSixTwoCandidates_eq_filter_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) :
    propositionSixTwoCandidates epsilon ell I j region length band C =
      (propositionSixTwoCandidates epsilon ell I j region length band B).filter
        (fun candidate => candidate.value ∈ C) := by
  ext candidate
  simp only [mem_propositionSixTwoCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hm⟩
    have hmData := mem_propositionSixTwoCofactorCarrier.mp hm
    refine ⟨⟨hp, mem_propositionSixTwoCofactorCarrier.mpr
      ⟨mem_sieveDilation.mpr (hCB (mem_sieveDilation.mp hmData.1)), hmData.2⟩⟩, ?_⟩
    exact mem_sieveDilation.mp hmData.1
  · rintro ⟨⟨hp, hm⟩, hvalue⟩
    exact ⟨hp, mem_propositionSixTwoCofactorCarrier.mpr
      ⟨mem_sieveDilation.mpr hvalue,
        (mem_propositionSixTwoCofactorCarrier.mp hm).2⟩⟩

/-- Near filtering commutes with restriction to a requested carrier. -/
theorem propositionSixTwoNearCandidates_eq_filter_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) :
    propositionSixTwoNearCandidates epsilon ell I j region length band rho C =
      (propositionSixTwoNearCandidates epsilon ell I j region length band rho
        B).filter (fun candidate => candidate.value ∈ C) := by
  rw [propositionSixTwoNearCandidates, propositionSixTwoNearCandidates,
    propositionSixTwoCandidates_eq_filter_of_subset hCB]
  ext candidate
  simp only [Finset.mem_filter]
  tauto

/-- Outside-near filtering commutes with restriction to a requested carrier. -/
theorem propositionSixTwoOutsideNearCandidates_eq_filter_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) :
    propositionSixTwoOutsideNearCandidates epsilon ell I j region length band
        rho C =
      (propositionSixTwoOutsideNearCandidates epsilon ell I j region length
        band rho B).filter (fun candidate => candidate.value ∈ C) := by
  rw [propositionSixTwoOutsideNearCandidates,
    propositionSixTwoOutsideNearCandidates,
    propositionSixTwoCandidates_eq_filter_of_subset hCB]
  ext candidate
  simp only [Finset.mem_filter]
  tauto

/-- The complete candidate card is the sum of its near and outside cards. -/
theorem card_propositionSixTwoCandidates_eq_near_add_outside
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    (propositionSixTwoCandidates epsilon ell I j region length band C).card =
      (propositionSixTwoNearCandidates epsilon ell I j region length band rho
        C).card +
      (propositionSixTwoOutsideNearCandidates epsilon ell I j region length
        band rho C).card := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := propositionSixTwoCandidates epsilon ell I j region length band C)
    (fun candidate =>
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho)
  simpa only [propositionSixTwoNearCandidates,
    propositionSixTwoOutsideNearCandidates] using hpartition.symm

/-- The literal strict band sum is its exact candidate-card discrepancy. -/
theorem propositionSixTwoBandSum_eq_candidateCardDiscrepancy
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (digit : Fin 10) (length : Nat)
    (band : SectionSixDirectBand) :
    propositionSixTwoBandSum epsilon ell I j region digit length band =
      ((propositionSixTwoCandidates epsilon ell I j region length band
        (paddedRestrictedNumbers digit length)).card : Real) -
      ((restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real)) *
      ((propositionSixTwoCandidates epsilon ell I j region length band
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real))).card : Real) := by
  let P := propositionSixTwoPrimeTuples epsilon ell I j region length band
  let A := paddedRestrictedNumbers digit length
  let B := maynardAmbientCarrier ((10 ^ length : Nat) : Real)
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / ((10 ^ length : Nat) : Real))
  have hA := card_propositionSixTwoCandidates_eq_sum_cofactorCard
    epsilon ell I j region length band A
  have hB := card_propositionSixTwoCandidates_eq_sum_cofactorCard
    epsilon ell I j region length band B
  have hAReal :
      ((propositionSixTwoCandidates epsilon ell I j region length band
        A).card : Real) =
      ∑ p ∈ P, ((propositionSixTwoCofactorCarrier A j p).card : Real) := by
    exact_mod_cast hA
  have hBReal :
      ((propositionSixTwoCandidates epsilon ell I j region length band
        B).card : Real) =
      ∑ p ∈ P, ((propositionSixTwoCofactorCarrier B j p).card : Real) := by
    exact_mod_cast hB
  unfold propositionSixTwoBandSum
  change (∑ p ∈ P, sectionSixSiftedSum digit length
    (propositionSixTwoModulus p) (p j : Real)) = _
  calc
    (∑ p ∈ P, sectionSixSiftedSum digit length
        (propositionSixTwoModulus p) (p j : Real)) =
        ∑ p ∈ P,
          (((propositionSixTwoCofactorCarrier A j p).card : Real) -
            lambda *
              ((propositionSixTwoCofactorCarrier B j p).card : Real)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [sectionSixSiftedSum_eq_card_sub_density_mul_card]
      rfl
    _ = (∑ p ∈ P,
          ((propositionSixTwoCofactorCarrier A j p).card : Real)) -
        lambda * (∑ p ∈ P,
          ((propositionSixTwoCofactorCarrier B j p).card : Real)) := by
      simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = ((propositionSixTwoCandidates epsilon ell I j region length band
          A).card : Real) -
        lambda * ((propositionSixTwoCandidates epsilon ell I j region length
          band B).card : Real) := by
      rw [← hAReal, ← hBReal]
    _ = _ := by
      dsimp only [A, B, lambda]
      ring

/-- The exact discrepancy is the sum of its near and outside discrepancies. -/
theorem propositionSixTwoBandSum_eq_near_add_outsideDiscrepancy
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (digit : Fin 10) (length : Nat)
    (band : SectionSixDirectBand) :
    propositionSixTwoBandSum epsilon ell I j region digit length band =
      (((propositionSixTwoNearCandidates epsilon ell I j region length band rho
        (paddedRestrictedNumbers digit length)).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
        ((propositionSixTwoNearCandidates epsilon ell I j region length band rho
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real))).card : Real)) +
      (((propositionSixTwoOutsideNearCandidates epsilon ell I j region length
        band rho (paddedRestrictedNumbers digit length)).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
        ((propositionSixTwoOutsideNearCandidates epsilon ell I j region length
          band rho
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real))).card : Real)) := by
  rw [propositionSixTwoBandSum_eq_candidateCardDiscrepancy,
    card_propositionSixTwoCandidates_eq_near_add_outside
      epsilon rho ell I j region length band
      (paddedRestrictedNumbers digit length),
    card_propositionSixTwoCandidates_eq_near_add_outside
      epsilon rho ell I j region length band
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real))]
  push_cast
  ring

end

end PrimesRestrictedDigits
