import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowTerminalFlatten

/-!
# Path completeness of the Section 6 low occurrence tree

Every admissible low path followed by a strict-high prime occurs in the canonical fuel-built
tree. This is completeness of the finite recurrence enumerator, not an additional analytic
estimate.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixLowUOccurrence_mk_mem
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root) {q : Nat}
    (hq : q ∈ sectionSixStateLowPrimeInterval
      parent.target.state R y parent.target.upper) :
    ({ parent := parent
       q := q
       primeMem := hq } : SectionSixLowUOccurrence root) ∈
      sectionSixLowUOccurrences parent := by
  unfold sectionSixLowUOccurrences
  apply List.mem_map.mpr
  refine ⟨⟨q, hq⟩, ?_, rfl⟩
  simp

private theorem sectionSixLowVOccurrence_mk_mem
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root) {q : Nat}
    (hq : q ∈ sectionSixStateHighPrimeInterval
      parent.target.state R y parent.target.upper) :
    ({ parent := parent
       q := q
       primeMem := hq } : SectionSixLowVOccurrence root) ∈
      sectionSixLowVOccurrences parent := by
  unfold sectionSixLowVOccurrences
  apply List.mem_map.mpr
  refine ⟨⟨q, hq⟩, ?_, rfl⟩
  simp

theorem exists_sectionSixLowStrictHigh_terminalOccurrence_from_path
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (start : SectionSixLowActiveOccurrence root)
    {parent : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat} {q fuel : Nat}
    (path : SectionSixLowStrictPath start.target parent steps)
    (hq : q ∈ sectionSixStateHighPrimeInterval
      parent.state R y parent.upper)
    (hfuel : steps.length < fuel) :
    ∃ leaf : SectionSixLowVOccurrence root,
      leaf.parent.target = parent ∧
        leaf.parent.steps = start.steps ++ steps ∧
        leaf.q = q ∧
        SectionSixLowTerminalOccurrence.strictHigh leaf ∈
          sectionSixLowTerminalOccurrences
            (sectionSixLowOccurrenceTreeOfFuel root fuel start) := by
  induction steps generalizing start parent fuel with
  | nil =>
      cases path
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          let leaf : SectionSixLowVOccurrence root :=
            { parent := start
              q := q
              primeMem := hq }
          have hleaf : leaf ∈ sectionSixLowVOccurrences start :=
            sectionSixLowVOccurrence_mk_mem start hq
          refine ⟨leaf, rfl, by simp [leaf], rfl, ?_⟩
          simp only [sectionSixLowOccurrenceTreeOfFuel,
            sectionSixLowTerminalOccurrences, List.mem_append,
            List.mem_cons]
          exact Or.inl (Or.inl (Or.inr
            (List.mem_map.mpr ⟨leaf, hleaf, rfl⟩)))
  | cons p rest ih =>
      cases path with
      | cons hp tail =>
          cases fuel with
          | zero => simp at hfuel
          | succ fuel =>
              have hrest : rest.length < fuel := by
                simpa only [List.length_cons, Nat.add_lt_add_iff_right] using
                  hfuel
              let edge : SectionSixLowUOccurrence root :=
                { parent := start
                  q := p
                  primeMem := hp }
              have hedge : edge ∈ sectionSixLowUOccurrences start :=
                sectionSixLowUOccurrence_mk_mem start hp
              obtain ⟨leaf, htarget, hsteps, hqeq, hterminal⟩ :=
                ih edge.child tail hq hrest
              refine ⟨leaf, htarget, ?_, hqeq, ?_⟩
              · calc
                  leaf.parent.steps = edge.child.steps ++ rest := hsteps
                  _ = start.steps ++ (p :: rest) := by
                    simp [edge, SectionSixLowUOccurrence.child,
                      List.append_assoc]
              · have hbranch :
                    (edge, sectionSixLowOccurrenceTreeOfFuel root fuel
                        edge.child) ∈
                      (sectionSixLowUOccurrences start).map fun branch =>
                        (branch, sectionSixLowOccurrenceTreeOfFuel root fuel
                          branch.child) :=
                  List.mem_map.mpr ⟨edge, hedge, rfl⟩
                have hflat :
                    SectionSixLowTerminalOccurrence.strictHigh leaf ∈
                      (((sectionSixLowUOccurrences start).map fun branch =>
                        (branch, sectionSixLowOccurrenceTreeOfFuel root fuel
                          branch.child)).flatMap fun branch =>
                            sectionSixLowTerminalOccurrences branch.2) :=
                  List.mem_flatMap.mpr
                    ⟨(edge, sectionSixLowOccurrenceTreeOfFuel root fuel
                      edge.child), hbranch, hterminal⟩
                simp only [sectionSixLowOccurrenceTreeOfFuel,
                  sectionSixLowTerminalOccurrences, List.mem_append,
                  List.mem_cons]
                exact Or.inl (Or.inl (Or.inl (Or.inr hflat)))

theorem exists_sectionSixLowStrictHigh_terminalOccurrence_from_root_path
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell)
    {parent : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat} {q fuel : Nat}
    (path : SectionSixLowStrictPath root parent steps)
    (hq : q ∈ sectionSixStateHighPrimeInterval
      parent.state R y parent.upper)
    (hfuel : steps.length < fuel) :
    ∃ leaf : SectionSixLowVOccurrence root,
      leaf.parent.target = parent ∧
        leaf.parent.steps = steps ∧
        leaf.q = q ∧
        SectionSixLowTerminalOccurrence.strictHigh leaf ∈
          sectionSixLowTerminalOccurrences
            (sectionSixLowOccurrenceTreeOfFuel root fuel
              (sectionSixLowRootOccurrence root)) := by
  simpa [sectionSixLowRootOccurrence] using
    exists_sectionSixLowStrictHigh_terminalOccurrence_from_path
      (sectionSixLowRootOccurrence root) path hq hfuel

theorem exists_sectionSixLowStrictHigh_terminalOccurrence_canonicalFuel
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (root : SectionSixLowActiveNode X delta theta R y band ell)
    {parent : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat} {q : Nat}
    (hX : 1 < X) (hdelta : 0 < delta)
    (path : SectionSixLowStrictPath root parent steps)
    (hq : q ∈ sectionSixStateHighPrimeInterval
      parent.state R y parent.upper) :
    ∃ leaf : SectionSixLowVOccurrence root,
      leaf.parent.target = parent ∧
        leaf.parent.steps = steps ∧
        leaf.q = q ∧
        SectionSixLowTerminalOccurrence.strictHigh leaf ∈
          sectionSixLowTerminalOccurrences
            (sectionSixLowOccurrenceTreeOfFuel root
              (Nat.ceil (1 / delta) + 1)
              (sectionSixLowRootOccurrence root)) := by
  apply exists_sectionSixLowStrictHigh_terminalOccurrence_from_root_path
    root path hq
  have hlength := sectionSixLowStrictPath_length_le_ceil_inv_delta
    hX hdelta path
  omega

end

end PrimesRestrictedDigits
