import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwo
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralSmallLedger
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Proposition 6.2 cells for the low central-small band residual

The five overlapping closed-band events are organized into nonempty inclusion-exclusion cells.
Each cell selects its least event for Proposition 6.2 and stores the remaining events as weak
affine walls.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.2, pp. 137--138, and Section 6, p. 143, Eq.
(6.12).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Coordinate positions of the five nonautomatic pair-band events in role
order `[s,r,q,p]`. -/
def sectionSixFirstLowCentralSmallQuadrupleBandPairPositions
    (event : Fin 5) : Finset (Fin 4) :=
  ![
    ({1, 3} : Finset (Fin 4)),
    ({0, 3} : Finset (Fin 4)),
    ({1, 2} : Finset (Fin 4)),
    ({0, 2} : Finset (Fin 4)),
    ({0, 1} : Finset (Fin 4))] event

/-- Carrier-minimal affine region for one nonempty inclusion-exclusion cell.
The selected event is supplied separately by Proposition 6.2. -/
def sectionSixFirstLowCentralSmallQuadrupleBandCellRegion
    (epsilon : Real) (cell : Finset (Fin 5))
    (hcell : cell.Nonempty) : Set (Fin 4 -> Real) :=
  {x | sectionSixThetaGap epsilon < x 0 ∧
    sectionSixThetaTwo epsilon < x 3 + x 2 ∧
    x 3 + 2 * x 2 < 1 - sectionSixThetaOne epsilon ∧
    ∀ event ∈ cell.erase (cell.min' hcell),
      sectionSixThetaOne epsilon <=
          ∑ i ∈ sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event,
            x i ∧
        (∑ i ∈
            sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event,
            x i) <= sectionSixThetaTwo epsilon}

private def main005VBandPairNormal (event : Fin 5) : Fin 4 -> Real :=
  fun i => if i ∈
    sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event then 1 else 0

private theorem main005V_typeIIAffineValue_bandPairNormal
    (event : Fin 5) (x : Fin 4 -> Real) :
    typeIIAffineValue (main005VBandPairNormal event) x =
      ∑ i ∈ sectionSixFirstLowCentralSmallQuadrupleBandPairPositions event,
        x i := by
  classical
  simp [typeIIAffineValue, main005VBandPairNormal]

private noncomputable def main005VBandCellPresentation
    (epsilon : Real) (cell : Finset (Fin 5))
    (hcell : cell.Nonempty) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstLowCentralSmallQuadrupleBandCellRegion
        epsilon cell hcell) := by
  classical
  let remaining : Finset (Fin 5) := cell.erase (cell.min' hcell)
  let lowerNormal : Fin remaining.card -> Fin 4 -> Real := fun i =>
    -main005VBandPairNormal (remaining.orderIsoOfFin rfl i).1
  let upperNormal : Fin remaining.card -> Fin 4 -> Real := fun i =>
    main005VBandPairNormal (remaining.orderIsoOfFin rfl i).1
  refine
    { constraintCount := 3 + (remaining.card + remaining.card)
      normal := Fin.append
        ![![-(1 : Real), 0, 0, 0], ![0, 0, -1, -1], ![0, 0, 2, 1]]
        (Fin.append lowerNormal upperNormal)
      bound := Fin.append
        ![-sectionSixThetaGap epsilon, -sectionSixThetaTwo epsilon,
          1 - sectionSixThetaOne epsilon]
        (Fin.append (fun _ => -sectionSixThetaOne epsilon)
          (fun _ => sectionSixThetaTwo epsilon))
      isStrict := Fin.append ![true, true, true]
        (Fin.append (fun _ => false) (fun _ => false))
      mem_iff := ?_ }
  intro x
  change (_ ∧ _ ∧ _ ∧ _) ↔ ∀ c, if (Fin.append ![true, true, true]
    (Fin.append (fun _ : Fin remaining.card => false)
      (fun _ : Fin remaining.card => false))) c then
      typeIIAffineValue (Fin.append
        ![![-(1 : Real), 0, 0, 0], ![0, 0, -1, -1], ![0, 0, 2, 1]]
        (Fin.append lowerNormal upperNormal) c) x <
        (Fin.append
          ![-sectionSixThetaGap epsilon, -sectionSixThetaTwo epsilon,
            1 - sectionSixThetaOne epsilon]
          (Fin.append (fun _ => -sectionSixThetaOne epsilon)
            (fun _ => sectionSixThetaTwo epsilon))) c
    else
      typeIIAffineValue (Fin.append
        ![![-(1 : Real), 0, 0, 0], ![0, 0, -1, -1], ![0, 0, 2, 1]]
        (Fin.append lowerNormal upperNormal) c) x <=
        (Fin.append
          ![-sectionSixThetaGap epsilon, -sectionSixThetaTwo epsilon,
            1 - sectionSixThetaOne epsilon]
          (Fin.append (fun _ => -sectionSixThetaOne epsilon)
            (fun _ => sectionSixThetaTwo epsilon))) c
  rw [Fin.forall_fin_add]
  constructor
  · rintro ⟨hgap, hcentral, hsquare, hevents⟩
    constructor
    · intro i
      fin_cases i <;>
        simp [typeIIAffineValue, Fin.sum_univ_succ] <;> linarith
    · simp only [Fin.append_right]
      rw [Fin.forall_fin_add]
      simp only [Fin.append_left, Fin.append_right, Bool.false_eq_true,
        if_false]
      constructor
      · intro i
        let event : remaining := remaining.orderIsoOfFin rfl i
        have hevent : event.1 ∈ cell.erase (cell.min' hcell) := by
          simpa only [remaining] using event.2
        have hband := (hevents event.1 hevent).1
        simpa [lowerNormal, event, typeIIAffineValue_neg,
          main005V_typeIIAffineValue_bandPairNormal] using hband
      · intro i
        let event : remaining := remaining.orderIsoOfFin rfl i
        have hevent : event.1 ∈ cell.erase (cell.min' hcell) := by
          simpa only [remaining] using event.2
        have hband := (hevents event.1 hevent).2
        simpa [upperNormal, event,
          main005V_typeIIAffineValue_bandPairNormal] using hband
  · rintro ⟨hbase, hextra⟩
    simp only [Fin.append_right] at hextra
    rw [Fin.forall_fin_add] at hextra
    simp only [Fin.append_left, Fin.append_right, Bool.false_eq_true,
      if_false] at hextra
    have hgap := hbase (0 : Fin 3)
    have hcentral := hbase (1 : Fin 3)
    have hsquare := hbase (2 : Fin 3)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [typeIIAffineValue, Fin.sum_univ_succ] at hgap
      linarith
    · simp [typeIIAffineValue, Fin.sum_univ_succ] at hcentral
      linarith
    · simp [typeIIAffineValue, Fin.sum_univ_succ] at hsquare
      linarith
    · intro event hevent
      let event' : remaining := ⟨event, by simpa only [remaining] using hevent⟩
      let eventIndex : Fin remaining.card :=
        (remaining.orderIsoOfFin rfl).symm event'
      have hlower := hextra.1 eventIndex
      have hupper := hextra.2 eventIndex
      have heventRound : remaining.orderIsoOfFin rfl eventIndex = event' :=
        (remaining.orderIsoOfFin rfl).apply_symm_apply event'
      have heventValue :
          (remaining.orderIsoOfFin rfl eventIndex).1 = event := by
        exact congrArg Subtype.val heventRound
      constructor
      · simp [lowerNormal,
          typeIIAffineValue_neg,
          main005V_typeIIAffineValue_bandPairNormal] at hlower
        change sectionSixThetaOne epsilon <=
          ∑ i ∈ sectionSixFirstLowCentralSmallQuadrupleBandPairPositions
            (remaining.orderIsoOfFin rfl eventIndex).1, x i at hlower
        rw [heventValue] at hlower
        exact hlower
      · simp [upperNormal,
          main005V_typeIIAffineValue_bandPairNormal] at hupper
        change (∑ i ∈
          sectionSixFirstLowCentralSmallQuadrupleBandPairPositions
            (remaining.orderIsoOfFin rfl eventIndex).1, x i) <=
              sectionSixThetaTwo epsilon at hupper
        rw [heventValue] at hupper
        exact hupper

private theorem main005VBandCellPresentation_constraintCount
    (epsilon : Real) (cell : Finset (Fin 5)) (hcell : cell.Nonempty) :
    (main005VBandCellPresentation epsilon cell hcell).constraintCount =
      2 * cell.card + 1 := by
  change 3 + ((cell.erase (cell.min' hcell)).card +
    (cell.erase (cell.min' hcell)).card) = 2 * cell.card + 1
  rw [Finset.card_erase_of_mem (cell.min'_mem hcell)]
  have hcard : 0 < cell.card := Finset.card_pos.mpr hcell
  omega

private theorem main005VCardFinAppendTrueFalseFalse (n k l : Nat) :
    ((Finset.univ : Finset (Fin (n + (k + l)))).filter fun c =>
      Fin.append (fun _ : Fin n => true)
        (Fin.append (fun _ : Fin k => false) (fun _ : Fin l => false)) c).card =
        n := by
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp
  intro x
  exact Fin.addCases (fun i => by simp only [Fin.append_left])
    (fun i => by simp only [Fin.append_right]) x

private theorem main005VBandCellPresentation_strictIndices_card
    (epsilon : Real) (cell : Finset (Fin 5)) (hcell : cell.Nonempty) :
    (main005VBandCellPresentation epsilon cell hcell).strictIndices.card = 3 := by
  let remaining : Finset (Fin 5) := cell.erase (cell.min' hcell)
  have hflags :
      (main005VBandCellPresentation epsilon cell hcell).isStrict =
        Fin.append (fun _ : Fin 3 => true)
          (Fin.append (fun _ : Fin remaining.card => false)
            (fun _ : Fin remaining.card => false)) := by
    simp only [main005VBandCellPresentation]
    funext c
    exact Fin.addCases (fun i => by fin_cases i <;> rfl)
      (fun i => by simp only [Fin.append_right]; rfl) c
  rw [TypeIIAffineMixedPresentation.strictIndices, hflags]
  exact main005VCardFinAppendTrueFalseFalse 3 remaining.card remaining.card

/-- The Proposition 6.2 first-band sum for one nonempty event intersection. -/
noncomputable def sectionSixFirstLowCentralSmallQuadrupleBandCellSum
    (epsilon : Real) (cell : Finset (Fin 5))
    (hcell : cell.Nonempty) (digit : Fin 10) (length : Nat) : Real :=
  propositionSixTwoBandSum epsilon 4
    (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions
      (cell.min' hcell))
    (0 : Fin 4)
    (sectionSixFirstLowCentralSmallQuadrupleBandCellRegion
      epsilon cell hcell)
    digit length .first

/-- Every fixed nonempty cell satisfies the arbitrary raw-mass Proposition
6.2 budget, uniformly in the excluded digit. -/
theorem exists_sectionSixFirstLowCentralSmallQuadrupleBandCellSum_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (cell : Finset (Fin 5)) (hcell : cell.Nonempty)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowCentralSmallQuadrupleBandCellSum
            epsilon cell hcell digit length) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  obtain ⟨length0, hlength0, hbound⟩ :=
    propositionSixTwo epsilon hepsilon hepsilonSmall
      (sectionSixFirstLowCentralSmallQuadrupleBandPairPositions
        (cell.min' hcell))
      (0 : Fin 4)
      (main005VBandCellPresentation epsilon cell hcell)
      budget hbudget
  exact ⟨length0, hlength0, fun length hlength digit =>
    hbound length hlength digit .first⟩

end

end PrimesRestrictedDigits
