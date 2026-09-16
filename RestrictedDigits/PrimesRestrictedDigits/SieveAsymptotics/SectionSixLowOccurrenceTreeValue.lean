import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowOccurrenceTree
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Signed values for the occurrence-preserving Section 6 tree

The fold uses the root-relative path length for signs. The complete modulus, not the active
family tag, controls the numerical strict or repeated term.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixLowActiveOccurrenceValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) : Real :=
  sectionSixStateStrictTerm digit length occurrence.target.state.2
    occurrence.target.upper

def sectionSixLowTOccurrenceValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowTOccurrence root) : Real :=
  sectionSixStateStrictTerm digit length occurrence.state.2 y

def sectionSixLowVOccurrenceValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowVOccurrence root) : Real :=
  sectionSixStrictPrimeTerm digit length
    (sectionSixStateModulusPNat occurrence.parent.target.state.2)
    occurrence.q

def sectionSixLowRUOccurrenceValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRUOccurrence root) : Real :=
  sectionSixRepeatedPrimeTerm digit length
    (sectionSixStateModulusPNat occurrence.parent.target.state.2)
    occurrence.q

def sectionSixLowRVOccurrenceValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowRVOccurrence root) : Real :=
  sectionSixRepeatedPrimeTerm digit length
    (sectionSixStateModulusPNat occurrence.parent.target.state.2)
    occurrence.q

theorem sectionSixLowTOccurrenceValue_eq_parent_lowerTerm
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowTOccurrence root) :
    sectionSixLowTOccurrenceValue digit length occurrence =
      sectionSixStateStrictTerm digit length occurrence.parent.target.state.2 y := by
  unfold sectionSixLowTOccurrenceValue SectionSixLowTOccurrence.state
    sectionSixStateStrictTerm
  congr 1

theorem sectionSixLowUOccurrences_sum_truncatedValue
    (digit : Fin 10) (length fuel : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowUOccurrences occurrence).map fun branch =>
        sectionSixLowTruncatedValue digit length fuel
          branch.child.target).sum =
      ∑ q ∈ sectionSixStateLowPrimeInterval occurrence.target.state R y
          occurrence.target.upper,
        if hq : q ∈ sectionSixStateLowPrimeInterval
            occurrence.target.state R y occurrence.target.upper then
          sectionSixLowTruncatedValue digit length fuel
            (sectionSixLowActiveChild occurrence.target q hq)
        else 0 := by
  unfold sectionSixLowUOccurrences
  rw [List.map_map]
  change
    (((sectionSixStateLowPrimeInterval occurrence.target.state R y
      occurrence.target.upper).attach.toList).map fun
        q : {q // q ∈ sectionSixStateLowPrimeInterval
          occurrence.target.state R y occurrence.target.upper} =>
        sectionSixLowTruncatedValue digit length fuel
          (sectionSixLowActiveChild occurrence.target q.1 q.2)).sum = _
  rw [Finset.sum_map_toList]
  conv_rhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [dif_pos q.2]

theorem SectionSixLowUOccurrence.child_steps_length_of_mem
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    (branch : SectionSixLowUOccurrence root)
    (hbranch : branch ∈ sectionSixLowUOccurrences occurrence) :
    branch.child.steps.length = occurrence.steps.length + 1 := by
  unfold sectionSixLowUOccurrences at hbranch
  rcases List.mem_map.mp hbranch with ⟨q, hq, rfl⟩
  simp

theorem sectionSixLowVOccurrences_sum_value
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowVOccurrences occurrence).map
        (sectionSixLowVOccurrenceValue digit length)).sum =
      ∑ q ∈ sectionSixStateHighPrimeInterval occurrence.target.state R y
          occurrence.target.upper,
        sectionSixStrictPrimeTerm digit length
          (sectionSixStateModulusPNat occurrence.target.state.2) q := by
  unfold sectionSixLowVOccurrences
  rw [List.map_map]
  change
    (((sectionSixStateHighPrimeInterval occurrence.target.state R y
      occurrence.target.upper).attach.toList).map fun
        q : {q // q ∈ sectionSixStateHighPrimeInterval
          occurrence.target.state R y occurrence.target.upper} =>
        sectionSixStrictPrimeTerm digit length
          (sectionSixStateModulusPNat occurrence.target.state.2) q.1).sum = _
  rw [Finset.sum_map_toList, Finset.sum_attach]

theorem sectionSixLowRUOccurrences_sum_value
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowRUOccurrences occurrence).map
        (sectionSixLowRUOccurrenceValue digit length)).sum =
      ∑ q ∈ sectionSixStateLowPrimeInterval occurrence.target.state R y
          occurrence.target.upper,
        sectionSixRepeatedPrimeTerm digit length
          (sectionSixStateModulusPNat occurrence.target.state.2) q := by
  unfold sectionSixLowRUOccurrences
  rw [List.map_map]
  change
    (((sectionSixStateLowPrimeInterval occurrence.target.state R y
      occurrence.target.upper).attach.toList).map fun
        q : {q // q ∈ sectionSixStateLowPrimeInterval
          occurrence.target.state R y occurrence.target.upper} =>
        sectionSixRepeatedPrimeTerm digit length
          (sectionSixStateModulusPNat occurrence.target.state.2) q.1).sum = _
  rw [Finset.sum_map_toList, Finset.sum_attach]

theorem sectionSixLowRVOccurrences_sum_value
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowRVOccurrences occurrence).map
        (sectionSixLowRVOccurrenceValue digit length)).sum =
      ∑ q ∈ sectionSixStateHighPrimeInterval occurrence.target.state R y
          occurrence.target.upper,
        sectionSixRepeatedPrimeTerm digit length
          (sectionSixStateModulusPNat occurrence.target.state.2) q := by
  unfold sectionSixLowRVOccurrences
  rw [List.map_map]
  change
    (((sectionSixStateHighPrimeInterval occurrence.target.state R y
      occurrence.target.upper).attach.toList).map fun
        q : {q // q ∈ sectionSixStateHighPrimeInterval
          occurrence.target.state R y occurrence.target.upper} =>
        sectionSixRepeatedPrimeTerm digit length
          (sectionSixStateModulusPNat occurrence.target.state.2) q.1).sum = _
  rw [Finset.sum_map_toList, Finset.sum_attach]

def sectionSixLowOccurrenceTreeSignedValue
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    SectionSixLowOccurrenceTree root → Real
  | .residualActive residual =>
      (-1 : Real) ^ residual.steps.length *
        sectionSixLowActiveOccurrenceValue digit length residual
  | .expanded base branches vLeaves ruLeaves rvLeaves =>
      (-1 : Real) ^ base.parent.steps.length *
          sectionSixLowTOccurrenceValue digit length base +
        (branches.map fun branch =>
          sectionSixLowOccurrenceTreeSignedValue digit length branch.2).sum +
        (-1 : Real) ^ (base.parent.steps.length + 1) *
          ((vLeaves.map (sectionSixLowVOccurrenceValue digit length)).sum +
            (ruLeaves.map (sectionSixLowRUOccurrenceValue digit length)).sum +
            (rvLeaves.map (sectionSixLowRVOccurrenceValue digit length)).sum)
termination_by tree => sizeOf tree
decreasing_by
  have hbranch : sizeOf branch < sizeOf branches :=
    List.sizeOf_lt_of_mem (by assumption)
  rcases branch with ⟨edge, subtree⟩
  have hsnd : sizeOf subtree < sizeOf (edge, subtree) := by
    change sizeOf subtree < 1 + sizeOf edge + sizeOf subtree
    omega
  simp_wf
  omega

theorem sectionSixLowOccurrenceTreeSignedValue_ofFuel_eq
    (digit : Fin 10) (length fuel : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    sectionSixLowOccurrenceTreeSignedValue digit length
        (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence) =
      (-1 : Real) ^ occurrence.steps.length *
        sectionSixLowTruncatedValue digit length fuel occurrence.target := by
  induction fuel generalizing occurrence with
  | zero =>
      simp only [sectionSixLowOccurrenceTreeOfFuel,
        sectionSixLowOccurrenceTreeSignedValue.eq_1,
        sectionSixLowActiveOccurrenceValue, sectionSixLowTruncatedValue]
  | succ fuel ih =>
      rw [sectionSixLowOccurrenceTreeOfFuel,
        sectionSixLowOccurrenceTreeSignedValue.eq_2,
        sectionSixLowTOccurrenceValue_eq_parent_lowerTerm]
      have hbranches :
          ((((sectionSixLowUOccurrences occurrence).map fun branch =>
              (branch, sectionSixLowOccurrenceTreeOfFuel root fuel
                branch.child)).map fun branch =>
              sectionSixLowOccurrenceTreeSignedValue digit length
                branch.2).sum) =
            (-1 : Real) ^ (occurrence.steps.length + 1) *
              ((sectionSixLowUOccurrences occurrence).map fun branch =>
                sectionSixLowTruncatedValue digit length fuel
                  branch.child.target).sum := by
        rw [List.map_map]
        calc
          ((sectionSixLowUOccurrences occurrence).map fun branch =>
              sectionSixLowOccurrenceTreeSignedValue digit length
                (sectionSixLowOccurrenceTreeOfFuel root fuel
                  branch.child)).sum =
              ((sectionSixLowUOccurrences occurrence).map fun branch =>
                (-1 : Real) ^ branch.child.steps.length *
                  sectionSixLowTruncatedValue digit length fuel
                    branch.child.target).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro branch hbranch
            exact ih branch.child
          _ = ((sectionSixLowUOccurrences occurrence).map fun branch =>
                (-1 : Real) ^ (occurrence.steps.length + 1) *
                  sectionSixLowTruncatedValue digit length fuel
                    branch.child.target).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro branch hbranch
            rw [branch.child_steps_length_of_mem occurrence hbranch]
          _ = (-1 : Real) ^ (occurrence.steps.length + 1) *
              ((sectionSixLowUOccurrences occurrence).map fun branch =>
                sectionSixLowTruncatedValue digit length fuel
                  branch.child.target).sum := by
            rw [List.sum_map_mul_left]
      rw [hbranches,
        sectionSixLowUOccurrences_sum_truncatedValue,
        sectionSixLowVOccurrences_sum_value,
        sectionSixLowRUOccurrences_sum_value,
        sectionSixLowRVOccurrences_sum_value]
      simp only [sectionSixLowTOccurrenceOfActive]
      conv_rhs => rw [sectionSixLowTruncatedValue]
      rw [pow_succ]
      ring

theorem sectionSixLowOccurrenceTreeSignedValue_root_eq_stateStrictTerm
    (digit : Fin 10) (length fuel : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell) :
    sectionSixLowOccurrenceTreeSignedValue digit length
        (sectionSixLowOccurrenceTreeOfFuel root fuel
          (sectionSixLowRootOccurrence root)) =
      sectionSixStateStrictTerm digit length root.state.2 root.upper := by
  rw [sectionSixLowOccurrenceTreeSignedValue_ofFuel_eq]
  simpa [sectionSixLowRootOccurrence] using
    sectionSixLowTruncatedValue_eq_stateStrictTerm digit length fuel root

theorem sectionSixSourceBandRoot_occurrenceTreeSignedValue_eq_sourceTerm
    {epsilon : Real} {length ell : Nat}
    (hlength : 1 ≤ length)
    {region : Set (Fin ell → Real)}
    (band : SectionSixStateBand)
    (p : Fin ell → Nat)
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (delta : Real)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hband : sectionSixSourceBandMembership band
      ((10 ^ length : Nat) : Real)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real))
    (hcutoff_le_X :
      sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ≤
        ((10 ^ length : Nat) : Real))
    (digit : Fin 10) (fuel : Nat) :
    sectionSixLowOccurrenceTreeSignedValue digit length
        (sectionSixLowOccurrenceTreeOfFuel
          (sectionSixSourceBandRoot hlength band p hp delta hdeltaGap
            hband hcutoff_le_X)
          fuel
          (sectionSixLowRootOccurrence
            (sectionSixSourceBandRoot hlength band p hp delta hdeltaGap
              hband hcutoff_le_X))) =
      sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
  rw [sectionSixLowOccurrenceTreeSignedValue_ofFuel_eq]
  simpa [sectionSixLowRootOccurrence] using
    sectionSixSourceBandRoot_truncatedValue_eq_sourceTerm hlength band p hp
      delta hdeltaGap hband hcutoff_le_X digit fuel

theorem sectionSixSourceBandRoot_occurrenceTree_residualFree
    {epsilon : Real} {length ell : Nat}
    (hlength : 1 ≤ length)
    {region : Set (Fin ell → Real)}
    (band : SectionSixStateBand)
    (p : Fin ell → Nat)
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (delta : Real)
    (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hband : sectionSixSourceBandMembership band
      ((10 ^ length : Nat) : Real)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real))
    (hcutoff_le_X :
      sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ≤
        ((10 ^ length : Nat) : Real)) :
    (sectionSixLowOccurrenceTreeOfFuel
      (sectionSixSourceBandRoot hlength band p hp delta hdeltaGap
        hband hcutoff_le_X)
      (Nat.ceil (1 / delta) + 1)
      (sectionSixLowRootOccurrence
        (sectionSixSourceBandRoot hlength band p hp delta hdeltaGap
          hband hcutoff_le_X))).ResidualFree := by
  apply sectionSixLowOccurrenceTreeOfFuel_root_residualFree
  · have hXNat : 1 < 10 ^ length :=
      Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
    exact_mod_cast hXNat
  · exact hdelta

end

end PrimesRestrictedDigits
