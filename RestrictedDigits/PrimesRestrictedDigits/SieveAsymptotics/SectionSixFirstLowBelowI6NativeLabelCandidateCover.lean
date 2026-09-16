import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelBranchPruning
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelCandidateSubset

/-!
# Candidate-indexed exact-region cover

This is a one-way reindexing of the existing exact-region over-cover. Every witness label is
filtered through the necessary predicates; no cardinality, target nonemptiness, tree,
integral, or cap statement is made.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowBelowI6_candidateLabel_exactRegion_subset_iUnion_nativeTarget :
    sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ⊆
      ⋃ label : {label : i6D691Label // label ∈ i6D731CandidateLabels},
        i6D691NativeTarget label.1 := by
  intro x hx
  obtain ⟨label, hlabel⟩ := Set.mem_iUnion.1
    (i6D691_exactRegion_subset_iUnion_nativeTarget hx)
  have hpruned :=
    sectionSixFirstLowBelowI6_native_membership_branchPruned label hlabel
  have hcandidates := i6D731_active_mem_candidates label hpruned
  exact Set.mem_iUnion.2 ⟨⟨label, hcandidates⟩, hlabel⟩

end

end PrimesRestrictedDigits
