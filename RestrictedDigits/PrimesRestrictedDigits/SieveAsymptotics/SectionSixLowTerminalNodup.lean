import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowTerminalFlatten
import Mathlib.Data.List.Nodup

/-!
# Duplicate-free canonical Section 6 terminal lists

Canonical fuel-built trees have no repeated terminal occurrences, and their projected
terminal-state lists are duplicate-free.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixLowStrictPath_target_outer
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (path : SectionSixLowStrictPath start target steps) :
    target.state.2.outer = start.state.2.outer := by
  induction path with
  | nil node => rfl
  | @cons node target rest q hq tail ih =>
      rw [ih]
      rfl

private abbrev TerminalCode := SectionSixStateKind × List Nat

private def terminalCode
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell} :
    SectionSixLowTerminalOccurrence root → TerminalCode
  | .base occurrence => (.T, occurrence.parent.steps)
  | .strictHigh occurrence =>
      (.V, occurrence.parent.steps ++ [occurrence.q])
  | .repeatedLow occurrence =>
      (.RU, occurrence.parent.steps ++ [occurrence.q])
  | .repeatedHigh occurrence =>
      (.RV, occurrence.parent.steps ++ [occurrence.q])

private theorem uQ_nodup
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowUOccurrences occurrence).map (fun branch => branch.q)).Nodup := by
  unfold sectionSixLowUOccurrences
  rw [List.map_map]
  change (((sectionSixStateLowPrimeInterval occurrence.target.state R y
    occurrence.target.upper).attach.toList).map (fun q => q.1)).Nodup
  exact (Finset.nodup_toList _).map Subtype.val_injective

private theorem uParent_eq_of_mem
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (parent : SectionSixLowActiveOccurrence root)
    (edge : SectionSixLowUOccurrence root)
    (hedge : edge ∈ sectionSixLowUOccurrences parent) :
    edge.parent = parent := by
  unfold sectionSixLowUOccurrences at hedge
  rcases List.mem_map.mp hedge with ⟨q, hq, rfl⟩
  rfl

private theorem terminalCode_path_prefix_ofFuel
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell fuel : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    (term : SectionSixLowTerminalOccurrence root)
    (hterm : term ∈ sectionSixLowTerminalOccurrences
      (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence)) :
    ∃ suffix, (terminalCode term).2 = occurrence.steps ++ suffix := by
  induction fuel generalizing occurrence term with
  | zero =>
      simp [sectionSixLowOccurrenceTreeOfFuel,
        sectionSixLowTerminalOccurrences] at hterm
  | succ fuel ih =>
      simp only [sectionSixLowOccurrenceTreeOfFuel,
        sectionSixLowTerminalOccurrences, List.mem_cons,
        List.mem_append] at hterm
      rcases hterm with (((hbase | hbranch) | hv) | hru) | hrv
      · subst term
        exact ⟨[], by simp [terminalCode, sectionSixLowTOccurrenceOfActive]⟩
      · rcases List.mem_flatMap.mp hbranch with ⟨branch, hbranch, hterm⟩
        rcases List.mem_map.mp hbranch with ⟨edge, hedge, rfl⟩
        rcases ih edge.child term hterm with ⟨suffix, hsuffix⟩
        have hparent := uParent_eq_of_mem occurrence edge hedge
        refine ⟨[edge.q] ++ suffix, ?_⟩
        rw [hsuffix]
        simp [SectionSixLowUOccurrence.child, List.append_assoc, hparent]
      · rcases List.mem_map.mp hv with ⟨leaf, hleaf, rfl⟩
        have hparent := leaf.parent_eq_of_mem occurrence hleaf
        exact ⟨[leaf.q], by simp [terminalCode, hparent]⟩
      · rcases List.mem_map.mp hru with ⟨leaf, hleaf, rfl⟩
        have hparent := leaf.parent_eq_of_mem occurrence hleaf
        exact ⟨[leaf.q], by simp [terminalCode, hparent]⟩
      · rcases List.mem_map.mp hrv with ⟨leaf, hleaf, rfl⟩
        have hparent := leaf.parent_eq_of_mem occurrence hleaf
        exact ⟨[leaf.q], by simp [terminalCode, hparent]⟩

private theorem terminalCode_path_strictPrefix_ofFuel
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell fuel : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    (term : SectionSixLowTerminalOccurrence root)
    (hterm : term ∈ sectionSixLowTerminalOccurrences
      (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence))
    (hkind : (terminalCode term).1 ≠ SectionSixStateKind.T) :
    ∃ q suffix, (terminalCode term).2 = occurrence.steps ++ q :: suffix := by
  induction fuel generalizing occurrence term with
  | zero =>
      simp [sectionSixLowOccurrenceTreeOfFuel,
        sectionSixLowTerminalOccurrences] at hterm
  | succ fuel ih =>
      simp only [sectionSixLowOccurrenceTreeOfFuel,
        sectionSixLowTerminalOccurrences, List.mem_cons,
        List.mem_append] at hterm
      rcases hterm with (((hbase | hbranch) | hv) | hru) | hrv
      · subst term
        simp [terminalCode] at hkind
      · rcases List.mem_flatMap.mp hbranch with ⟨branch, hbranch, hterm⟩
        rcases List.mem_map.mp hbranch with ⟨edge, hedge, rfl⟩
        rcases terminalCode_path_prefix_ofFuel edge.child term hterm with
          ⟨suffix, hsuffix⟩
        have hparent := uParent_eq_of_mem occurrence edge hedge
        refine ⟨edge.q, suffix, ?_⟩
        rw [hsuffix]
        simp [SectionSixLowUOccurrence.child, List.append_assoc, hparent]
      · rcases List.mem_map.mp hv with ⟨leaf, hleaf, rfl⟩
        have hparent := leaf.parent_eq_of_mem occurrence hleaf
        exact ⟨leaf.q, [], by simp [terminalCode, hparent]⟩
      · rcases List.mem_map.mp hru with ⟨leaf, hleaf, rfl⟩
        have hparent := leaf.parent_eq_of_mem occurrence hleaf
        exact ⟨leaf.q, [], by simp [terminalCode, hparent]⟩
      · rcases List.mem_map.mp hrv with ⟨leaf, hleaf, rfl⟩
        have hparent := leaf.parent_eq_of_mem occurrence hleaf
        exact ⟨leaf.q, [], by simp [terminalCode, hparent]⟩

private def terminalCodesOfFuel
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (fuel : Nat) (occurrence : SectionSixLowActiveOccurrence root) :
    List TerminalCode :=
  (sectionSixLowTerminalOccurrences
    (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence)).map terminalCode

private theorem childCodeLists_disjoint_of_q_ne
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell fuel : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    (edgeOne edgeTwo : SectionSixLowUOccurrence root)
    (hedgeOne : edgeOne ∈ sectionSixLowUOccurrences occurrence)
    (hedgeTwo : edgeTwo ∈ sectionSixLowUOccurrences occurrence)
    (hq : edgeOne.q ≠ edgeTwo.q) :
    List.Disjoint (terminalCodesOfFuel fuel edgeOne.child)
      (terminalCodesOfFuel fuel edgeTwo.child) := by
  rw [List.disjoint_left]
  intro code hcodeOne hcodeTwo
  rcases List.mem_map.mp hcodeOne with ⟨termOne, htermOne, hcodeOneEq⟩
  rcases List.mem_map.mp hcodeTwo with ⟨termTwo, htermTwo, hcodeTwoEq⟩
  have hparentOne := uParent_eq_of_mem occurrence edgeOne hedgeOne
  have hparentTwo := uParent_eq_of_mem occurrence edgeTwo hedgeTwo
  rcases terminalCode_path_prefix_ofFuel edgeOne.child termOne htermOne with
    ⟨suffixOne, hsuffixOne⟩
  rcases terminalCode_path_prefix_ofFuel edgeTwo.child termTwo htermTwo with
    ⟨suffixTwo, hsuffixTwo⟩
  have hpath : (terminalCode termOne).2 = (terminalCode termTwo).2 := by
    rw [hcodeOneEq, hcodeTwoEq]
  rw [hsuffixOne, hsuffixTwo] at hpath
  simp only [SectionSixLowUOccurrence.child, hparentOne, hparentTwo,
    List.append_assoc] at hpath
  have htail : [edgeOne.q] ++ suffixOne = [edgeTwo.q] ++ suffixTwo :=
    List.append_right_injective occurrence.steps hpath
  exact hq (List.cons.inj htail).1

private theorem attachedTerminalCodes_nodup
    (kind : SectionSixStateKind) (history : List Nat) (primes : Finset Nat) :
    ((primes.attach.toList).map fun q : {q // q ∈ primes} =>
      (kind, history ++ [q.1])).Nodup := by
  apply (Finset.nodup_toList primes.attach).map
  intro q r hcode
  apply Subtype.ext
  have hpath : history ++ [q.1] = history ++ [r.1] :=
    congrArg Prod.snd hcode
  have hsingleton : [q.1] = [r.1] :=
    List.append_right_injective history hpath
  exact (List.cons.inj hsingleton).1

private theorem childCodeLists_pairwise_disjoint
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell fuel : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    List.Pairwise
      (fun edgeOne edgeTwo : SectionSixLowUOccurrence root =>
        List.Disjoint (terminalCodesOfFuel fuel edgeOne.child)
          (terminalCodesOfFuel fuel edgeTwo.child))
      (sectionSixLowUOccurrences occurrence) := by
  have hqPairwise : List.Pairwise
      (fun edgeOne edgeTwo : SectionSixLowUOccurrence root =>
        edgeOne.q ≠ edgeTwo.q)
      (sectionSixLowUOccurrences occurrence) := by
    rw [← List.pairwise_map]
    exact List.nodup_iff_pairwise_ne.mp (uQ_nodup occurrence)
  apply (List.Pairwise.and_mem.mp hqPairwise).imp
  intro edgeOne edgeTwo hdata
  exact childCodeLists_disjoint_of_q_ne occurrence edgeOne edgeTwo
    hdata.1 hdata.2.1 hdata.2.2

private def branchCodes
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (fuel : Nat) (occurrence : SectionSixLowActiveOccurrence root) :
    List TerminalCode :=
  (sectionSixLowUOccurrences occurrence).flatMap fun edge =>
    terminalCodesOfFuel fuel edge.child

private def vCodes
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) : List TerminalCode :=
  (sectionSixLowVOccurrences occurrence).map fun leaf =>
    terminalCode (.strictHigh leaf)

private def ruCodes
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) : List TerminalCode :=
  (sectionSixLowRUOccurrences occurrence).map fun leaf =>
    terminalCode (.repeatedLow leaf)

private def rvCodes
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) : List TerminalCode :=
  (sectionSixLowRVOccurrences occurrence).map fun leaf =>
    terminalCode (.repeatedHigh leaf)

private theorem terminalCodesOfFuel_succ
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell fuel : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    terminalCodesOfFuel (fuel + 1) occurrence =
      (SectionSixStateKind.T, occurrence.steps) ::
        (branchCodes fuel occurrence ++ vCodes occurrence ++
          ruCodes occurrence ++ rvCodes occurrence) := by
  unfold terminalCodesOfFuel branchCodes vCodes ruCodes rvCodes
  rw [sectionSixLowOccurrenceTreeOfFuel]
  simp only [sectionSixLowTerminalOccurrences, List.map_cons,
    List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
    terminalCode, sectionSixLowTOccurrenceOfActive]
  rw [List.flatMap_map]
  rfl

private theorem baseCode_not_mem_branchCodes
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell fuel : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root) :
    (SectionSixStateKind.T, occurrence.steps) ∉ branchCodes fuel occurrence := by
  intro hcode
  rcases List.mem_flatMap.mp hcode with ⟨edge, hedge, hcode⟩
  rcases List.mem_map.mp hcode with ⟨term, hterm, htermCode⟩
  rcases terminalCode_path_prefix_ofFuel edge.child term hterm with
    ⟨suffix, hsuffix⟩
  have hparent := uParent_eq_of_mem occurrence edge hedge
  have hpath : (terminalCode term).2 = occurrence.steps := by
    rw [htermCode]
  rw [hsuffix] at hpath
  have hlength := congrArg List.length hpath
  simp only [SectionSixLowUOccurrence.child_steps_length, hparent,
    List.length_append] at hlength
  omega

private theorem baseCode_not_mem_of_kind
    (history : List Nat) (codes : List TerminalCode)
    (kind : SectionSixStateKind) (hkind : kind ≠ .T)
    (hcodes : ∀ code ∈ codes, code.1 = kind) :
    (SectionSixStateKind.T, history) ∉ codes := by
  intro hcode
  exact hkind ((hcodes _ hcode).symm.trans rfl)

private theorem vCodes_mem_data
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    {code : TerminalCode} (hcode : code ∈ vCodes occurrence) :
    code.1 = .V ∧ code.2.length = occurrence.steps.length + 1 := by
  rcases List.mem_map.mp hcode with ⟨leaf, hleaf, rfl⟩
  have hparent := leaf.parent_eq_of_mem occurrence hleaf
  simp [terminalCode, hparent]

private theorem ruCodes_mem_data
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    {code : TerminalCode} (hcode : code ∈ ruCodes occurrence) :
    code.1 = .RU ∧ code.2.length = occurrence.steps.length + 1 := by
  rcases List.mem_map.mp hcode with ⟨leaf, hleaf, rfl⟩
  have hparent := leaf.parent_eq_of_mem occurrence hleaf
  simp [terminalCode, hparent]

private theorem rvCodes_mem_data
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    {code : TerminalCode} (hcode : code ∈ rvCodes occurrence) :
    code.1 = .RV ∧ code.2.length = occurrence.steps.length + 1 := by
  rcases List.mem_map.mp hcode with ⟨leaf, hleaf, rfl⟩
  have hparent := leaf.parent_eq_of_mem occurrence hleaf
  simp [terminalCode, hparent]

private theorem branchCodes_disjoint_local
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell fuel : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (occurrence : SectionSixLowActiveOccurrence root)
    (terminalList : List TerminalCode) (kind : SectionSixStateKind)
    (hkind : kind ≠ .T)
    (hlocal : ∀ code ∈ terminalList,
      code.1 = kind ∧ code.2.length = occurrence.steps.length + 1) :
    List.Disjoint (branchCodes fuel occurrence) terminalList := by
  rw [List.disjoint_left]
  intro code hbranch hlocalCode
  rcases List.mem_flatMap.mp hbranch with ⟨edge, hedge, hedgeCode⟩
  rcases List.mem_map.mp hedgeCode with ⟨term, hterm, htermCode⟩
  have hdata := hlocal code hlocalCode
  have htermKind : (terminalCode term).1 ≠ .T := by
    rw [htermCode, hdata.1]
    exact hkind
  rcases terminalCode_path_strictPrefix_ofFuel edge.child term hterm
      htermKind with ⟨q, suffix, hsuffix⟩
  have hparent := uParent_eq_of_mem occurrence edge hedge
  rw [htermCode] at hsuffix
  have hlength := congrArg List.length hsuffix
  simp only [SectionSixLowUOccurrence.child_steps_length, hparent,
    List.length_append, List.length_cons] at hlength
  omega

private theorem codeLists_disjoint_of_kind_ne
    (left right : List TerminalCode)
    (leftKind rightKind : SectionSixStateKind)
    (hleft : ∀ code ∈ left, code.1 = leftKind)
    (hright : ∀ code ∈ right, code.1 = rightKind)
    (hne : leftKind ≠ rightKind) : List.Disjoint left right := by
  rw [List.disjoint_left]
  intro code hcodeLeft hcodeRight
  exact hne ((hleft code hcodeLeft).symm.trans (hright code hcodeRight))

private theorem disjoint_append_left
    {alpha : Type*} {left middle right : List alpha}
    (hleft : List.Disjoint left right)
    (hmiddle : List.Disjoint middle right) :
    List.Disjoint (left ++ middle) right := by
  rw [List.disjoint_left]
  intro value hvalue hright
  rcases List.mem_append.mp hvalue with hleftValue | hmiddleValue
  · exact (List.disjoint_left.mp hleft) hleftValue hright
  · exact (List.disjoint_left.mp hmiddle) hmiddleValue hright

private theorem terminalCodesOfFuel_nodup
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (fuel : Nat) (occurrence : SectionSixLowActiveOccurrence root) :
    (terminalCodesOfFuel fuel occurrence).Nodup := by
  induction fuel generalizing occurrence with
  | zero =>
      simp [terminalCodesOfFuel, sectionSixLowOccurrenceTreeOfFuel,
        sectionSixLowTerminalOccurrences]
  | succ fuel ih =>
      rw [terminalCodesOfFuel_succ]
      apply List.nodup_cons.mpr
      have hbranchNodup : (branchCodes fuel occurrence).Nodup := by
        unfold branchCodes
        rw [List.nodup_flatMap]
        exact ⟨fun edge hedge => ih edge.child,
          childCodeLists_pairwise_disjoint occurrence⟩
      have hvNodup : (vCodes occurrence).Nodup := by
        unfold vCodes sectionSixLowVOccurrences
        rw [List.map_map]
        exact attachedTerminalCodes_nodup .V occurrence.steps _
      have hruNodup : (ruCodes occurrence).Nodup := by
        unfold ruCodes sectionSixLowRUOccurrences
        rw [List.map_map]
        exact attachedTerminalCodes_nodup .RU occurrence.steps _
      have hrvNodup : (rvCodes occurrence).Nodup := by
        unfold rvCodes sectionSixLowRVOccurrences
        rw [List.map_map]
        exact attachedTerminalCodes_nodup .RV occurrence.steps _
      have hbranchV : List.Disjoint (branchCodes fuel occurrence)
          (vCodes occurrence) :=
        branchCodes_disjoint_local occurrence _ .V (by decide)
          (fun code hcode => vCodes_mem_data occurrence hcode)
      have hbranchRU : List.Disjoint (branchCodes fuel occurrence)
          (ruCodes occurrence) :=
        branchCodes_disjoint_local occurrence _ .RU (by decide)
          (fun code hcode => ruCodes_mem_data occurrence hcode)
      have hbranchRV : List.Disjoint (branchCodes fuel occurrence)
          (rvCodes occurrence) :=
        branchCodes_disjoint_local occurrence _ .RV (by decide)
          (fun code hcode => rvCodes_mem_data occurrence hcode)
      have hvRU := codeLists_disjoint_of_kind_ne _ _ .V .RU
        (fun code hcode => (vCodes_mem_data occurrence hcode).1)
        (fun code hcode => (ruCodes_mem_data occurrence hcode).1) (by decide)
      have hvRV := codeLists_disjoint_of_kind_ne _ _ .V .RV
        (fun code hcode => (vCodes_mem_data occurrence hcode).1)
        (fun code hcode => (rvCodes_mem_data occurrence hcode).1) (by decide)
      have hruRV := codeLists_disjoint_of_kind_ne _ _ .RU .RV
        (fun code hcode => (ruCodes_mem_data occurrence hcode).1)
        (fun code hcode => (rvCodes_mem_data occurrence hcode).1) (by decide)
      have hbranchVNodup := hbranchNodup.append hvNodup hbranchV
      have hbranchVRUNodup := hbranchVNodup.append hruNodup
        (disjoint_append_left hbranchRU hvRU)
      have htailNodup := hbranchVRUNodup.append hrvNodup
        (disjoint_append_left (disjoint_append_left hbranchRV hvRV) hruRV)
      refine ⟨?_, htailNodup⟩
      intro hbase
      simp only [List.mem_append] at hbase
      rcases hbase with ((hbranch | hv) | hru) | hrv
      · exact baseCode_not_mem_branchCodes occurrence hbranch
      · exact baseCode_not_mem_of_kind occurrence.steps _ .V (by decide)
          (fun code hcode => (vCodes_mem_data occurrence hcode).1) hv
      · exact baseCode_not_mem_of_kind occurrence.steps _ .RU (by decide)
          (fun code hcode => (ruCodes_mem_data occurrence hcode).1) hru
      · exact baseCode_not_mem_of_kind occurrence.steps _ .RV (by decide)
          (fun code hcode => (rvCodes_mem_data occurrence hcode).1) hrv

theorem sectionSixLowTerminalOccurrences_nodup
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (fuel : Nat) (occurrence : SectionSixLowActiveOccurrence root) :
    (sectionSixLowTerminalOccurrences
      (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence)).Nodup := by
  exact List.Nodup.of_map terminalCode
    (terminalCodesOfFuel_nodup fuel occurrence)

theorem sectionSixLowTerminalOccurrences_state_nodup
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (fuel : Nat) (occurrence : SectionSixLowActiveOccurrence root) :
    ((sectionSixLowTerminalOccurrences
      (sectionSixLowOccurrenceTreeOfFuel root fuel occurrence)).map
        (SectionSixLowTerminalOccurrence.state (root := root))).Nodup := by
  exact (sectionSixLowTerminalOccurrences_nodup fuel occurrence).map
    sectionSixLowTerminalOccurrence_state_injective

end

end PrimesRestrictedDigits
