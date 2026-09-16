import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStrictRoughFactorArity

/-!
# Complete stable-pattern coverage for Proposition 6.2

Complete candidates below the decimal cutoff have bounded total prime-factor arity and
therefore carry the same canonical stable tags as near candidates.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Every complete candidate retains membership of its represented value in
the carrier used by its cofactor dilation. -/
theorem propositionSixTwoCandidate_value_mem_carrier
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hcandidate : candidate ∈ propositionSixTwoCandidates epsilon ell I j
      region length band C) :
    candidate.value ∈ C := by
  have hcandidateData := mem_propositionSixTwoCandidates.mp hcandidate
  have hcofactor :=
    mem_propositionSixTwoCofactorCarrier.mp hcandidateData.2
  have hcarrier := mem_sieveDilation.mp hcofactor.1
  simpa only [PropositionSixTwoCandidate.value] using hcarrier

/-- A strict represented-value cutoff is the exact extra input needed to
extend the complete factor-arity bound from near to arbitrary candidates. -/
theorem propositionSixTwoCandidate_totalArity_le_two_div_of_value_lt
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hgap : 0 < sectionSixThetaGap epsilon)
    (hcandidate : candidate ∈ propositionSixTwoCandidates epsilon ell I j
      region length band C)
    (hvalueUpper : candidate.value < 10 ^ length) :
    (((ell + candidate.2.primeFactorsList.length : Nat) : Real) <=
      2 / sectionSixThetaGap epsilon) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hcandidateData := mem_propositionSixTwoCandidates.mp hcandidate
  have hpFinsetData := mem_propositionSixTwoPrimeTuples.mp hcandidateData.1
  have hpJData := Nat.mem_primesLE.mp (hpFinsetData.1 j)
  have hXNat : 1 < XNat := (hpJData.2.one_lt).trans_le hpJData.1
  have hpData :=
    mem_propositionSixTwoPrimeTuples_iff_source.mp hcandidateData.1
  dsimp [IsPropositionSixTwoPrimeTuple] at hpData
  have hmZero : candidate.2 ≠ 0 := by
    intro hm
    apply zero_not_mem_propositionSixTwoCofactorCarrier_of_outer_mem
      hcandidateData.1
    simpa only [← hm] using hcandidateData.2
  have hroughData :=
    (mem_propositionSixTwoCofactorCarrier.mp hcandidateData.2).2
  have hrough : strictRoughPredicate
      (X ^ sectionSixThetaGap epsilon) candidate.2 := by
    intro q hqPrime hqDvd
    have hq := hroughData q hqPrime hqDvd
    exact (hpData.2.2.1 j).trans_lt (by simpa only [X, XNat] using hq)
  have hproduct :
      primeTupleProduct candidate.1 * candidate.2 < XNat := by
    rw [PropositionSixTwoCandidate.value_eq_mul_primeTupleProduct_of_mem
      hcandidate] at hvalueUpper
    simpa only [XNat, Nat.mul_comm] using hvalueUpper
  apply typeIIStableFactorArity_le_two_div_eta hXNat hgap hmZero hpData.1
  · simpa only [X, XNat] using hpData.2.2.1
  · exact hrough
  · exact hproduct

/-- Ambient carrier containment turns complete-candidate value membership into
the strict cutoff needed for the canonical residual-arity ceiling. -/
theorem
    propositionSixTwoCandidate_residualLength_le_ceil_two_div_of_subset_ambient
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hgap : 0 < sectionSixThetaGap epsilon)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hcandidate : candidate ∈ propositionSixTwoCandidates epsilon ell I j
      region length band C) :
    candidate.2.primeFactorsList.length <=
      Nat.ceil (2 / sectionSixThetaGap epsilon) := by
  have hvalueUpperReal : (candidate.value : Real) <
      ((10 ^ length : Nat) : Real) :=
    mem_maynardAmbientCarrier.mp
      (hC (propositionSixTwoCandidate_value_mem_carrier hcandidate))
  have hvalueUpper : candidate.value < 10 ^ length := by
    exact_mod_cast hvalueUpperReal
  have htotal := propositionSixTwoCandidate_totalArity_le_two_div_of_value_lt
    hgap hcandidate hvalueUpper
  have hcomplete : ell + candidate.2.primeFactorsList.length <=
      Nat.ceil (2 / sectionSixThetaGap epsilon) := by
    exact_mod_cast htotal.trans
      (Nat.le_ceil (2 / sectionSixThetaGap epsilon))
  omega

/-- Every complete candidate in an ambient-bounded carrier has a concrete tag
at the canonical Proposition 6.2 ceiling. -/
theorem exists_propositionSixTwoStablePattern_of_mem_candidates_of_subset_ambient
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hgap : 0 < sectionSixThetaGap epsilon)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hcandidate : candidate ∈ propositionSixTwoCandidates epsilon ell I j
      region length band C) :
    ∃ pattern : PropositionSixTwoStablePattern ell
        (Nat.ceil (2 / sectionSixThetaGap epsilon)),
      candidate.stablePatternTag
        (Nat.ceil (2 / sectionSixThetaGap epsilon)) = some pattern := by
  have hbound :=
    propositionSixTwoCandidate_residualLength_le_ceil_two_div_of_subset_ambient
      hgap hC hcandidate
  unfold PropositionSixTwoCandidate.stablePatternTag
  rw [dif_pos hbound]
  exact ⟨_, rfl⟩

end

end PrimesRestrictedDigits
