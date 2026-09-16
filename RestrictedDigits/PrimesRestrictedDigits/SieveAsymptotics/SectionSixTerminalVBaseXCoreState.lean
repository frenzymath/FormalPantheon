import PrimesRestrictedDigits.SieveAsymptotics.SectionSixNearScalarCaps
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSourceTerminalVConverse
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetRegion

/-!
# Decode a terminal-V base-X core to a canonical state

This reconstructs exactly the source-attached terminal-`V` recurrence state from the
successful base-`X` source/fixed-core branch. See the Lemma 7.3 geometry on pp. 149--152 and
the Proposition 6.1 recurrence on pp. 156--157 of `MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A prime tuple satisfying the base-`X` source and fixed terminal walls
determines an exact canonical source-attached state of kind `V`. -/
theorem sectionSixTerminalVBaseXCore_exists_source_state
    {epsilon delta : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    {pattern : SectionSixTerminalVStablePattern ell M}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (hinner : 0 < pattern.1.1)
    (hresidual : 0 < pattern.2.1.1)
    (factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat)
    (hprime : forall i, (factors i).Prime)
    (hmonotone : Monotone factors)
    (hembedding : StrictMono pattern.2.2)
    (hcoreX :
      (fun i => normalizedPrimeLog (10 ^ length) (factors i)) ∈
        typeIIAffineEmbeddingPreimageRegion
            pattern.sourcePositionEmbedding region ∩
          sectionSixTerminalVFixedRegion epsilon delta band pattern
            hinner hresidual) :
    let outer : Fin ell -> Nat :=
      fun i => factors (pattern.sourcePositionEmbedding i)
    let innerTuple : Fin pattern.1.1 -> Nat :=
      fun j => factors (pattern.innerPositionEmbedding j)
    let inner := List.ofFn innerTuple
    let displayed : Fin (pattern.1.1 + ell) -> Nat :=
      fun i => factors (pattern.2.2 i)
    exists source : {p // p ∈ sectionSixSourceBandPrimeTuples
        epsilon ell region length band},
      exists state : SectionSixAnyState band ell,
        state ∈ sectionSixSourceMemberTerminalStates hepsilon hepsilonSmall
            hlength hdeltaGap band source ∧
          IsSectionSixRecurrenceState ((10 ^ length : Nat) : Real) delta
            (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
            (sectionSixThetaTwo epsilon) state.2 ∧
          source.1 = outer ∧
          state.2.outer = source.1 ∧
          state.2.inner = inner ∧
          state.2.kind = .V ∧
          state.1 = primeTupleProduct displayed ∧
          ∃ hinnerLength : state.2.inner.length = pattern.1.1,
            (fun i => sectionSixTerminalVExplicitFactors state
              (Fin.cast (congrArg (fun n => n + ell) hinnerLength).symm i)) =
                displayed := by
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let outer : Fin ell -> Nat :=
    fun i => factors (pattern.sourcePositionEmbedding i)
  let innerTuple : Fin pattern.1.1 -> Nat :=
    fun j => factors (pattern.innerPositionEmbedding j)
  let inner := List.ofFn innerTuple
  let displayed : Fin (pattern.1.1 + ell) -> Nat :=
    fun i => factors (pattern.2.2 i)
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X, XNat]
    exact_mod_cast hXNat
  have hfixed := hcoreX.2
  have hsourceRegion :
      (fun i => normalizedPrimeLog XNat (outer i)) ∈ region := by
    change (fun i => normalizedPrimeLog (10 ^ length)
      (factors (pattern.sourcePositionEmbedding i))) ∈ region
    exact hcoreX.1
  have houterPrime : forall i, (outer i).Prime := fun i => hprime _
  have hinnerPrime : forall q, q ∈ inner -> q.Prime := by
    intro q hq
    change q ∈ List.ofFn innerTuple at hq
    rw [List.mem_ofFn] at hq
    obtain ⟨j, rfl⟩ := hq
    exact hprime _
  have houterMonotone : Monotone outer := by
    intro i j hij
    apply hmonotone
    exact hembedding.monotone (by
      simpa [SectionSixTerminalVStablePattern.sourcePositionEmbedding] using
        (Fin.strictMono_natAdd pattern.1.1).monotone hij)
  have hinnerTupleMonotone : Monotone innerTuple := by
    intro i j hij
    apply hmonotone
    exact hembedding.monotone (by
      simpa [SectionSixTerminalVStablePattern.innerPositionEmbedding] using
        (Fin.strictMono_castAdd ell).monotone hij)
  have hinnerSorted : inner.SortedLE :=
    hinnerTupleMonotone.sortedLE_ofFn
  have houterLower : forall i,
      X ^ sectionSixThetaGap epsilon <= (outer i : Real) := by
    intro i
    have hi := hfixed.2.1 i
    change sectionSixThetaGap epsilon <= Real.logb X (outer i : Real) at hi
    exact (Real.le_logb_iff_rpow_le hX (by
      exact_mod_cast (houterPrime i).pos)).mp hi
  have houterProductPos : (0 : Real) < (primeTupleProduct outer : Real) := by
    exact_mod_cast primeTupleProduct_pos (fun i => (houterPrime i).ne_zero)
  have hsourceSum :
      sectionSixTerminalVSourceSum pattern
          (fun i => normalizedPrimeLog XNat (factors i)) =
        normalizedPrimeLog XNat (primeTupleProduct outer) := by
    rw [sectionSixTerminalVSourceSum,
      sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
        (fun i => (houterPrime i).ne_zero)]
  have hband : sectionSixSourceBandMembership band X
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct outer : Real) := by
    cases band with
    | low =>
        have hs := hfixed.2.2.2.1
        rw [hsourceSum] at hs
        change Real.logb X (primeTupleProduct outer : Real) <
          sectionSixThetaOne epsilon at hs
        exact (Real.logb_lt_iff_lt_rpow hX houterProductPos).mp hs
    | high =>
        have hsLower := hfixed.2.2.2.1
        have hsUpper := hfixed.2.2.2.2.1
        rw [hsourceSum] at hsLower hsUpper
        change sectionSixThetaTwo epsilon <
          Real.logb X (primeTupleProduct outer : Real) at hsLower
        change Real.logb X (primeTupleProduct outer : Real) <
          1 - sectionSixThetaTwo epsilon at hsUpper
        exact ⟨
          (Real.lt_logb_iff_rpow_lt hX houterProductPos).mp hsLower,
          (Real.logb_lt_iff_lt_rpow hX houterProductPos).mp hsUpper⟩
  have houterCap : (primeTupleProduct outer : Real) <=
      X ^ (1 - sectionSixThetaOne epsilon) :=
    (sectionSixSourceBandMembership_cutoff_le hband).trans
      (sectionSixStateBandCutoff_le_sourceCap
        hepsilon hepsilonSmall hX band)
  have hp : IsPropositionSixOnePrimeTuple epsilon length region outer := by
    dsimp only [IsPropositionSixOnePrimeTuple]
    exact ⟨houterPrime, houterMonotone,
      by simpa only [X, XNat] using houterLower,
      by simpa only [X, XNat] using houterCap,
      by simpa only [XNat] using hsourceRegion⟩
  have houterMem : outer ∈ propositionSixOnePrimeTuples
      epsilon ell region length :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mpr hp
  have hsourceMem : outer ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band := by
    apply mem_sectionSixSourceBandPrimeTuples.mpr
    exact ⟨houterMem, by simpa only [X, XNat] using hband⟩
  let source : {p // p ∈ sectionSixSourceBandPrimeTuples
      epsilon ell region length band} := ⟨outer, hsourceMem⟩
  have hinnerRange : sectionSixStateInnerRange X delta
      (sectionSixThetaGap epsilon) inner := by
    intro q hq
    change q ∈ List.ofFn innerTuple at hq
    rw [List.mem_ofFn] at hq
    obtain ⟨j, rfl⟩ := hq
    have hupperLog := hfixed.1 j
    change Real.logb X (innerTuple j : Real) <=
      sectionSixThetaGap epsilon at hupperLog
    have hupper := (Real.logb_le_iff_le_rpow hX (by
      exact_mod_cast (hprime _).pos)).mp hupperLog
    have hfirstLog : delta < normalizedPrimeLog XNat
        (factors (pattern.firstInnerPosition hinner)) := by
      cases band with
      | low => exact hfixed.2.2.2.2.1
      | high => exact hfixed.2.2.2.2.2.1
    change delta < Real.logb X
      (factors (pattern.firstInnerPosition hinner) : Real) at hfirstLog
    have hfirstLower := (Real.lt_logb_iff_rpow_lt hX (by
      exact_mod_cast (hprime _).pos)).mp hfirstLog
    have hfirstLe :
        factors (pattern.firstInnerPosition hinner) <= innerTuple j := by
      apply hmonotone
      apply hembedding.monotone
      change (Fin.castAdd ell (⟨0, hinner⟩ : Fin pattern.1.1)).val <=
        (Fin.castAdd ell j).val
      simp
    exact ⟨hfirstLower.trans_le (by exact_mod_cast hfirstLe), hupper⟩
  have hdisplayedEq : displayed = Fin.append innerTuple outer := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [displayed, innerTuple,
        SectionSixTerminalVStablePattern.innerPositionEmbedding]
    · intro i
      simp [displayed, outer,
        SectionSixTerminalVStablePattern.sourcePositionEmbedding]
  have hinnerProd : inner.prod = primeTupleProduct innerTuple := by
    change (List.ofFn innerTuple).prod = primeTupleProduct innerTuple
    rw [List.prod_ofFn]
    rfl
  have hdisplayedProduct : primeTupleProduct displayed =
      primeTupleProduct outer * inner.prod := by
    rw [hdisplayedEq, primeTupleProduct, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    change primeTupleProduct innerTuple * primeTupleProduct outer =
      primeTupleProduct outer * inner.prod
    rw [hinnerProd]
    exact Nat.mul_comm _ _
  let stateData := sectionSixRecurrenceStateOfSourceTuple band .V outer inner hp
    hinnerPrime hinnerSorted
  let state : SectionSixAnyState band ell :=
    ⟨primeTupleProduct outer * inner.prod, stateData⟩
  have hstateOuter : state.2.outer = source.1 := rfl
  have hstateInner : state.2.inner = inner := rfl
  have hstateKind : state.2.kind = .V := rfl
  have hstateModulus : state.1 = primeTupleProduct displayed :=
    hdisplayedProduct.symm
  have hinnerNe : inner ≠ [] := by
    apply List.ne_nil_iff_length_pos.mpr
    change 0 < (List.ofFn innerTuple).length
    simpa only [List.length_ofFn] using hinner
  obtain ⟨q, rest, hinnerCons⟩ := List.exists_cons_of_ne_nil hinnerNe
  have hqMem : q ∈ inner := by rw [hinnerCons]; simp
  have hqPrime : q.Prime := hinnerPrime q hqMem
  have hqEq : q = innerTuple ⟨0, hinner⟩ := by
    have hget : inner[0]? = some q := by
      rw [hinnerCons]
      rfl
    simp [inner, hinner] at hget
    exact hget.symm
  have hqDvdInner : q ∣ inner.prod := List.dvd_prod hqMem
  have hqDvd : q ∣ state.1 := by
    change q ∣ primeTupleProduct outer * inner.prod
    exact dvd_mul_of_dvd_right hqDvdInner _
  have hdisplayedSum :
      sectionSixTerminalVDisplayedSum pattern
          (fun i => normalizedPrimeLog XNat (factors i)) =
        normalizedPrimeLog XNat (primeTupleProduct displayed) := by
    rw [sectionSixTerminalVDisplayedSum]
    calc
      sectionSixTerminalVSourceSum pattern
            (fun i => normalizedPrimeLog XNat (factors i)) +
          sectionSixTerminalVInnerSum pattern
            (fun i => normalizedPrimeLog XNat (factors i)) =
          (∑ j, normalizedPrimeLog XNat (innerTuple j)) +
            ∑ i, normalizedPrimeLog XNat (outer i) := by
              rw [add_comm]
              rfl
      _ = ∑ i, normalizedPrimeLog XNat ((Fin.append innerTuple outer) i) := by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
      _ = ∑ i, normalizedPrimeLog XNat (displayed i) := by rw [hdisplayedEq]
      _ = normalizedPrimeLog XNat (primeTupleProduct displayed) :=
        sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
          (fun i => (hprime _).ne_zero)
  have hstatePos : (0 : Real) < (state.1 : Real) := by
    rw [hstateModulus]
    exact_mod_cast primeTupleProduct_pos (fun i => (hprime _).ne_zero)
  have hqPos : (0 : Real) < (q : Real) := by exact_mod_cast hqPrime.pos
  have hcutoff : sectionSixStateCutoffPredicate .V
      (sectionSixStateBandCutoff band X (sectionSixThetaOne epsilon)
        (sectionSixThetaTwo epsilon)) state.1 inner := by
    refine ⟨q, rest, hinnerCons, hqDvd, ?_, ?_⟩
    · have hlowerLog : sectionSixTerminalVCutoffExponent epsilon band <
          sectionSixTerminalVDisplayedSum pattern
            (fun i => normalizedPrimeLog XNat (factors i)) := by
        cases band with
        | low =>
            simpa [sectionSixTerminalVCutoffExponent] using
              hfixed.2.2.2.2.2.1
        | high =>
            simpa [sectionSixTerminalVCutoffExponent] using
              hfixed.2.2.2.2.2.2.1
      rw [hdisplayedSum] at hlowerLog
      change sectionSixTerminalVCutoffExponent epsilon band <
        Real.logb X (primeTupleProduct displayed : Real) at hlowerLog
      have hlower := (Real.lt_logb_iff_rpow_lt hX (by
        rw [<- hstateModulus]
        exact hstatePos)).mp hlowerLog
      cases band <;> simpa [sectionSixTerminalVCutoffExponent,
        sectionSixStateBandCutoff, hstateModulus] using hlower
    · have hupperLog := hfixed.2.2.1
      rw [hdisplayedSum] at hupperLog
      change normalizedPrimeLog XNat (primeTupleProduct displayed) <=
        sectionSixTerminalVCutoffExponent epsilon band +
          normalizedPrimeLog XNat
            (factors (pattern.firstInnerPosition hinner)) at hupperLog
      have hqLog : normalizedPrimeLog XNat q =
          normalizedPrimeLog XNat
            (factors (pattern.firstInnerPosition hinner)) := by
        rw [hqEq]
        rfl
      rw [<- hqLog] at hupperLog
      change Real.logb X (primeTupleProduct displayed : Real) <=
        sectionSixTerminalVCutoffExponent epsilon band + Real.logb X (q : Real)
          at hupperLog
      have hupper := (Real.logb_le_iff_le_rpow hX (by
        rw [<- hstateModulus]
        exact hstatePos)).mp hupperLog
      rw [Real.rpow_add (zero_lt_one.trans hX),
        Real.rpow_logb (zero_lt_one.trans hX) hX.ne' hqPos] at hupper
      cases band <;> simpa [sectionSixTerminalVCutoffExponent,
        sectionSixStateBandCutoff, hstateModulus] using hupper
  have hexact : IsSectionSixRecurrenceState X delta
      (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
      (sectionSixThetaTwo epsilon) state.2 := by
    exact isSectionSixRecurrenceStateOfSourceTuple band .V outer inner hp
      hinnerPrime hinnerSorted hinnerRange hcutoff
  have hmember : state ∈ sectionSixSourceMemberTerminalStates hepsilon
      hepsilonSmall hlength hdeltaGap band source := by
    apply mem_sectionSixSourceMemberTerminalStates_of_exactVState
      hepsilon hepsilonSmall hlength hdelta hdeltaGap band source state
    · rfl
    · exact hstateKind
    · simpa only [X, XNat] using hexact
  have hinnerLength : state.2.inner.length = pattern.1.1 := by
    change (List.ofFn innerTuple).length = pattern.1.1
    exact List.length_ofFn
  have hexplicit :
      (fun i => sectionSixTerminalVExplicitFactors state
        (Fin.cast (congrArg (fun n => n + ell) hinnerLength).symm i)) =
          displayed := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      have hcast :
          Fin.cast (congrArg (fun n => n + ell) hinnerLength).symm
              (Fin.castAdd ell j) =
            Fin.castAdd ell (Fin.cast hinnerLength.symm j) := by
        apply Fin.ext
        rfl
      rw [hcast]
      simp [sectionSixTerminalVExplicitFactors, state, stateData, inner,
        sectionSixRecurrenceStateOfSourceTuple, innerTuple, displayed,
        SectionSixTerminalVStablePattern.innerPositionEmbedding]
      apply congrArg factors
      apply congrArg pattern.2.2
      apply Fin.ext
      rfl
    · intro i
      have hcast :
          Fin.cast (congrArg (fun n => n + ell) hinnerLength).symm
              (Fin.natAdd pattern.1.1 i) =
            Fin.natAdd state.2.inner.length i := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd]
        rw [hinnerLength]
      rw [hcast]
      simp [sectionSixTerminalVExplicitFactors, state, stateData, outer,
        sectionSixRecurrenceStateOfSourceTuple, displayed,
        SectionSixTerminalVStablePattern.sourcePositionEmbedding]
  exact ⟨source, state, hmember,
    by simpa only [X, XNat] using hexact,
    rfl, hstateOuter, hstateInner, hstateKind, hstateModulus,
    hinnerLength, hexplicit⟩

end

end PrimesRestrictedDigits
