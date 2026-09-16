import PrimesRestrictedDigits.SieveAsymptotics.TypeIICubeGrid
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIInteriorFamily

/-!
# Interior Type II grid-family discrepancy

This specializes to a subfamily of the minimal bounded natural cube grid. The exact grid
cardinality absorbs the remaining anchor-count term, leaving the `delta / log X` error used by
Proposition 7.2.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/--
The interior discrepancy on any subfamily of the minimal natural grid. This is still
conditional only on the explicit local geometry hypotheses; region coverage and boundary cells
remain downstream.
-/
theorem exists_typeIIInteriorGridFamilyError_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ Ceta : Real, 0 < Ceta ∧
      ∀ mu : Real, 0 < mu ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (k : Nat)
            (anchors : Finset (Fin k -> Nat)),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let delta : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let tupleFamily : (Fin k -> Nat) ->
                Finset (Fin (k + 1) -> Nat) := fun anchor =>
              majorArcPrimeTuples XNat
                (scaledNaturalCubeAnchor delta anchor) delta eta
            let supportCount : (Fin k -> Nat) -> Finset Nat -> Real :=
              fun anchor C =>
                (((primeTupleProductSupport (tupleFamily anchor)).filter
                  (fun n => n ∈ C)).card : Real)
            anchors ⊆ typeIINaturalCubeGrid k delta ->
            1 <= k ->
            (((k + 1 : Nat) : Real) <= 2 / eta) ->
            (∀ anchor ∈ anchors, ∀ i,
              eta / 2 <= scaledNaturalCubeAnchor delta anchor i) ->
            (∀ anchor ∈ anchors,
              (∑ i, scaledNaturalCubeAnchor delta anchor i) <
                1 - eta / 2) ->
            (∀ anchor ∈ anchors,
              typeIIInteriorCellSeparated
                (scaledNaturalCubeAnchor delta anchor) delta) ->
            (∀ anchor ∈ anchors, ∃ I : Finset (Fin k),
              (∑ i ∈ I, scaledNaturalCubeAnchor delta anchor i) ∈
                    Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
                (∑ i ∈ I, scaledNaturalCubeAnchor delta anchor i) ∈
                    Set.Icc (23 / 40 + mu) (16 / 25 - mu)) ->
            (∑ anchor ∈ anchors,
              |supportCount anchor A -
                (restrictedDigitDensity digit : Real) *
                    (A.card : Real) / X * supportCount anchor B|) <=
              Ceta * (delta * (A.card : Real) / Real.log X) := by
  obtain ⟨C, hC, hfamily⟩ :=
    exists_typeIIInteriorCubeFamilyError_eta_upper eta heta
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro mu hmu
  obtain ⟨length0, hlength0, hfamilyAt⟩ := hfamily mu hmu
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit k anchors
  dsimp only
  intro hanchors hk hell hmargin hroom hseparated hconvenient
  have hbase := hfamilyAt length hlength digit k anchors hk hell
    hmargin hroom hseparated hconvenient
  have hcard : 0 <= ((paddedRestrictedNumbers digit length).card : Real) := by
    positivity
  have hgrid := typeIIAnchorFamily_logError_le_delta_logError
    (hlength0.trans hlength) anchors hanchors
    ((paddedRestrictedNumbers digit length).card : Real) hcard
  let X : Real := (((10 ^ length : Nat) : Nat) : Real)
  let delta : Real := majorArcM2LogLogDelta (10 ^ length)
  let card : Real := ((paddedRestrictedNumbers digit length).card : Real)
  let first : Real :=
    (anchors.card : Real) * card / Real.log X ^ (k + 2)
  let second : Real := delta * card / Real.log X
  have hfirst : first <= second := by
    simpa only [first, second, card, delta, X] using hgrid
  have hsum : first + second <= second + second :=
    add_le_add_left hfirst second
  have hscaled : C * (first + second) <= C * (second + second) :=
    mul_le_mul_of_nonneg_left hsum hC.le
  have hdouble : C * (second + second) = (2 * C) * second := by ring
  simpa only [first, second, card, delta, X] using
    hbase.trans (hscaled.trans_eq hdouble)

end

end PrimesRestrictedDigits
