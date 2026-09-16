import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStrictCarrier
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Direct strict near candidates

Direct strict occurrences retain both their accepted `(p, q)` index and their cofactor. This
file proves the exact restricted-to-ambient filtering and the cardinal bridges needed before
any stable-pattern reindexing.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A direct occurrence consists of its accepted strict index and cofactor. -/
abbrev SectionSixDirectCandidate (ell : Nat) :=
  Sigma fun _ : SectionSixDirectStrictIndex ell => Nat

namespace SectionSixDirectCandidate

/-- The represented natural attached to a direct occurrence. -/
def value {ell : Nat} (candidate : SectionSixDirectCandidate ell) : Nat :=
  candidate.2 * sectionSixDirectStrictKey candidate.1

end SectionSixDirectCandidate

/-- All direct strict occurrences over one finite carrier. -/
noncomputable def sectionSixDirectCandidates
    (epsilon delta : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    Finset (SectionSixDirectCandidate ell) :=
  (sectionSixDirectRepeatedIndices epsilon delta ell region length band).sigma
    fun index => sectionSixDirectStrictCofactorCarrier C index

/-- Direct strict occurrences whose represented value is near the cutoff. -/
noncomputable def sectionSixDirectNearCandidates
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    Finset (SectionSixDirectCandidate ell) :=
  (sectionSixDirectCandidates epsilon delta ell region length band C).filter
    fun candidate =>
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho

/-- Direct strict occurrences outside the near-cutoff carrier. -/
noncomputable def sectionSixDirectOutsideNearCandidates
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    Finset (SectionSixDirectCandidate ell) :=
  (sectionSixDirectCandidates epsilon delta ell region length band C).filter
    fun candidate =>
      candidate.value ∉ typeIINearXCarrier (10 ^ length) rho

@[simp] theorem mem_sectionSixDirectCandidates
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {candidate : SectionSixDirectCandidate ell} :
    candidate ∈ sectionSixDirectCandidates epsilon delta ell region length
        band C <->
      candidate.1 ∈ sectionSixDirectRepeatedIndices epsilon delta ell region
          length band ∧
      candidate.2 ∈ sectionSixDirectStrictCofactorCarrier C candidate.1 := by
  simp [sectionSixDirectCandidates]

@[simp] theorem mem_sectionSixDirectNearCandidates
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {candidate : SectionSixDirectCandidate ell} :
    candidate ∈ sectionSixDirectNearCandidates epsilon delta rho ell region
        length band C <->
      candidate ∈ sectionSixDirectCandidates epsilon delta ell region length
          band C ∧
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho := by
  simp [sectionSixDirectNearCandidates]

@[simp] theorem mem_sectionSixDirectOutsideNearCandidates
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {candidate : SectionSixDirectCandidate ell} :
    candidate ∈ sectionSixDirectOutsideNearCandidates epsilon delta rho ell
        region length band C <->
      candidate ∈ sectionSixDirectCandidates epsilon delta ell region length
          band C ∧
      candidate.value ∉ typeIINearXCarrier (10 ^ length) rho := by
  simp [sectionSixDirectOutsideNearCandidates]

/-- Restricting the represented carrier changes only dilation membership;
the strict roughness condition is unchanged. -/
theorem mem_sectionSixDirectStrictCofactorCarrier_iff_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    {ell : Nat} {index : SectionSixDirectStrictIndex ell} {m : Nat} :
    m ∈ sectionSixDirectStrictCofactorCarrier C index <->
      m ∈ sectionSixDirectStrictCofactorCarrier B index ∧
        m * sectionSixDirectStrictKey index ∈ C := by
  simp only [sectionSixDirectStrictCofactorCarrier,
    mem_strictSiftedCarrier, mem_sieveDilation,
    sectionSixDirectStrictKey]
  constructor
  · rintro ⟨hmC, hmRough⟩
    exact ⟨⟨hCB hmC, hmRough⟩, hmC⟩
  · rintro ⟨⟨_hmB, hmRough⟩, hmC⟩
    exact ⟨hmC, hmRough⟩

/-- At one fixed index, represented restricted values are the ambient values
filtered by the restricted carrier. -/
theorem sectionSixDirectStrictRepresentedCarrier_eq_filter_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    {ell : Nat} (index : SectionSixDirectStrictIndex ell) :
    sectionSixDirectStrictRepresentedCarrier C index =
      (sectionSixDirectStrictRepresentedCarrier B index).filter
        (fun n => n ∈ C) := by
  ext n
  simp only [mem_sectionSixDirectStrictRepresentedCarrier,
    Finset.mem_filter]
  constructor
  · rintro ⟨m, hmC, rfl⟩
    have hmData :=
      (mem_sectionSixDirectStrictCofactorCarrier_iff_of_subset hCB).mp hmC
    exact ⟨⟨m, hmData.1, rfl⟩, hmData.2⟩
  · rintro ⟨⟨m, hmB, hmn⟩, hnC⟩
    refine ⟨m, ?_, hmn⟩
    apply (mem_sectionSixDirectStrictCofactorCarrier_iff_of_subset hCB).mpr
    refine ⟨hmB, ?_⟩
    simpa only [hmn] using hnC

/-- The restricted occurrence set is the ambient occurrence set filtered by
its represented value. -/
theorem sectionSixDirectCandidates_eq_filter_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon delta : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) :
    sectionSixDirectCandidates epsilon delta ell region length band C =
      (sectionSixDirectCandidates epsilon delta ell region length band B).filter
        (fun candidate => candidate.value ∈ C) := by
  ext candidate
  simp only [mem_sectionSixDirectCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hindex, hmC⟩
    have hmData :=
      (mem_sectionSixDirectStrictCofactorCarrier_iff_of_subset hCB).mp hmC
    exact ⟨⟨hindex, hmData.1⟩, hmData.2⟩
  · rintro ⟨⟨hindex, hmB⟩, hmC⟩
    exact ⟨hindex,
      (mem_sectionSixDirectStrictCofactorCarrier_iff_of_subset hCB).mpr
        ⟨hmB, hmC⟩⟩

/-- Near filtering commutes with the exact restricted-to-ambient filter. -/
theorem sectionSixDirectNearCandidates_eq_filter_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) :
    sectionSixDirectNearCandidates epsilon delta rho ell region length band C =
      (sectionSixDirectNearCandidates epsilon delta rho ell region length
        band B).filter (fun candidate => candidate.value ∈ C) := by
  rw [sectionSixDirectNearCandidates, sectionSixDirectNearCandidates,
    sectionSixDirectCandidates_eq_filter_of_subset hCB]
  ext candidate
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hcandidate, hmC⟩, hnear⟩
    exact ⟨⟨hcandidate, hnear⟩, hmC⟩
  · rintro ⟨⟨hcandidate, hnear⟩, hmC⟩
    exact ⟨⟨hcandidate, hmC⟩, hnear⟩

/-- Sigma occurrences have the sum of the exact cofactor cardinalities. -/
theorem card_sectionSixDirectCandidates_eq_sum_cofactorCard
    (epsilon delta : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    (sectionSixDirectCandidates epsilon delta ell region length band C).card =
      ∑ index ∈ sectionSixDirectRepeatedIndices epsilon delta ell region length
          band,
        (sectionSixDirectStrictCofactorCarrier C index).card := by
  exact Finset.card_sigma _ _

/-- Outside-near occurrences have the existing fixed-index represented
carrier difference cardinality. -/
theorem card_sectionSixDirectOutsideNearCandidates_eq_sum_represented_sdiff
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    (sectionSixDirectOutsideNearCandidates epsilon delta rho ell region length
        band C).card =
      ∑ index ∈ sectionSixDirectRepeatedIndices epsilon delta ell region length
          band,
        (sectionSixDirectStrictRepresentedCarrier C index \
          typeIINearXCarrier (10 ^ length) rho).card := by
  rw [sectionSixDirectOutsideNearCandidates, sectionSixDirectCandidates,
    Finset.filter_sigma, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro index hindex
  let near := typeIINearXCarrier (10 ^ length) rho
  let embedding := sectionSixDirectStrictRepresentedEmbedding index
  change ((sectionSixDirectStrictCofactorCarrier C index).filter
      (fun m => embedding m ∉ near)).card =
    (sectionSixDirectStrictRepresentedCarrier C index \ near).card
  have hmap :
      ((sectionSixDirectStrictCofactorCarrier C index).filter
          (fun m => embedding m ∉ near)).map embedding =
        sectionSixDirectStrictRepresentedCarrier C index \ near := by
    rw [Finset.sdiff_eq_filter, sectionSixDirectStrictRepresentedCarrier]
    change ((sectionSixDirectStrictCofactorCarrier C index).filter
        (fun m => embedding m ∉ near)).map embedding =
      ((sectionSixDirectStrictCofactorCarrier C index).map embedding).filter
        (fun n => n ∉ near)
    exact (Finset.filter_map
      (s := sectionSixDirectStrictCofactorCarrier C index)
      (f := embedding) (p := fun n => n ∉ near)).symm
  calc
    ((sectionSixDirectStrictCofactorCarrier C index).filter
        (fun m => embedding m ∉ near)).card =
        (((sectionSixDirectStrictCofactorCarrier C index).filter
          (fun m => embedding m ∉ near)).map
            embedding).card := (Finset.card_map embedding).symm
    _ = (sectionSixDirectStrictRepresentedCarrier C index \ near).card := by
      rw [hmap]

end

end PrimesRestrictedDigits
