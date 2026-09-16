import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionGeometry
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIInteriorGridFamily
import PrimesRestrictedDigits.ExceptionalMinorArcs.ExceptionalPropositionScalars

/-!
# Interior Type II source-region family discrepancy

This discharges the geometric hypotheses for the interior anchors of a source region. All
log-log width conditions are forced by one eventual decimal threshold. Boundary and
small-product terms remain downstream.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The Maynard log-log cube width is strictly positive at every positive
decimal length. -/
theorem majorArcM2LogLogDelta_powTen_pos
    {length : Nat} (hlength : 1 <= length) :
    0 < majorArcM2LogLogDelta (10 ^ length) := by
  have htenLe : 10 <= 10 ^ length := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < (10 : Nat)) hlength)
  have hlog : 1 < Real.log (((10 ^ length : Nat) : Real)) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 <= 10 ^ length by omega))
  have hloglog : 0 <
      Real.log (Real.log (((10 ^ length : Nat) : Real))) :=
    Real.log_pos hlog
  simpa only [majorArcM2LogLogDelta] using inv_pos.mpr hloglog

/--
The interior discrepancy specialized to the interior anchors of a source region. The
coefficient is uniform in the later convenience margin, region, digit, arity, and decimal
length.
-/
theorem exists_typeIIInteriorRegionFamilyError_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ Ceta : Real, 0 < Ceta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (k : Nat)
            (region : Set (Fin (k + 1) -> Real)),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let delta : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let anchors : Finset (Fin k -> Nat) :=
              typeIIInteriorCubeAnchors delta region
            let tupleFamily : (Fin k -> Nat) ->
                Finset (Fin (k + 1) -> Nat) := fun anchor =>
              majorArcPrimeTuples XNat
                (scaledNaturalCubeAnchor delta anchor) delta eta
            let supportCount : (Fin k -> Nat) -> Finset Nat -> Real :=
              fun anchor C =>
                (((primeTupleProductSupport (tupleFamily anchor)).filter
                  (fun n => n ∈ C)).card : Real)
            IsTypeIISourceRegion eta region ->
            IsTypeIIRegionConvenient epsilon region ->
            1 <= k ->
            (((k + 1 : Nat) : Real) <= 2 / eta) ->
            (∑ anchor ∈ anchors,
              |supportCount anchor A -
                (restrictedDigitDensity digit : Real) *
                    (A.card : Real) / X * supportCount anchor B|) <=
              Ceta * (delta * (A.card : Real) / Real.log X) := by
  obtain ⟨Ceta, hCeta, hfamily⟩ :=
    exists_typeIIInteriorGridFamilyError_eta_upper eta heta
  refine ⟨Ceta, hCeta, ?_⟩
  intro epsilon hepsilon
  obtain ⟨familyLength, hfamilyLength, hfamilyAt⟩ :=
    hfamily (epsilon / 2) (by positivity)
  let rho : Real := min (eta / 4) (min (1 / 2) (epsilon / 4))
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  obtain ⟨scalarLength, hscalarAt⟩ :=
    exists_exceptionalLogLogWidthMarginThreshold eta rho heta hrho
  let length0 := max familyLength scalarLength
  refine ⟨length0, hfamilyLength.trans (Nat.le_max_left _ _), ?_⟩
  intro length hlength digit k region
  dsimp only
  intro hregion hconvenient hk hell
  have hfamilyLengthAt : familyLength <= length :=
    (Nat.le_max_left _ _).trans hlength
  have hscalarLengthAt : scalarLength <= length :=
    (Nat.le_max_right _ _).trans hlength
  have hscalar := hscalarAt length hscalarLengthAt
  dsimp only at hscalar
  obtain ⟨hdeltaNonneg, hwidth⟩ := hscalar
  have hbudget := hwidth k hell
  let delta : Real := majorArcM2LogLogDelta (10 ^ length)
  have hdelta : 0 < delta := by
    exact majorArcM2LogLogDelta_powTen_pos
      (hfamilyLength.trans hfamilyLengthAt)
  have hlengthPos : 0 < length :=
    (hfamilyLength.trans hfamilyLengthAt)
  have hlengthInv : 0 <= 1 / (length : Real) := by positivity
  have hmulLeRho : ((k + 1 : Nat) : Real) * delta <= rho := by
    dsimp only [delta]
    linarith
  have hkCast : (k : Real) <= ((k + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ k
  have honeCast : (1 : Real) <= ((k + 1 : Nat) : Real) := by
    exact_mod_cast (show 1 <= k + 1 by omega)
  have hdeltaLeRho : delta <= rho := by
    have hmul := mul_le_mul_of_nonneg_right honeCast hdelta.le
    simpa only [one_mul] using hmul.trans hmulLeRho
  have hrhoEta : rho <= eta / 4 := by simp [rho]
  have hrhoHalf : rho <= 1 / 2 := by simp [rho]
  have hrhoEpsilon : rho <= epsilon / 4 := by simp [rho]
  have hmarginWidth : 2 * delta <= eta / 2 := by
    linarith [hdeltaLeRho.trans hrhoEta]
  have hdeltaHalf : delta <= 1 / 2 :=
    hdeltaLeRho.trans hrhoHalf
  have herror : 2 * (k : Real) * delta <= epsilon / 2 := by
    have hkMul : (k : Real) * delta <=
        ((k + 1 : Nat) : Real) * delta :=
      mul_le_mul_of_nonneg_right hkCast hdelta.le
    linarith [hkMul, hmulLeRho, hrhoEpsilon]
  let anchors : Finset (Fin k -> Nat) :=
    typeIIInteriorCubeAnchors delta region
  apply hfamilyAt length hfamilyLengthAt digit k anchors
  · intro anchor hanchor
    exact typeIIRelevantCubeAnchors_subset_grid delta region
      (mem_typeIIInteriorCubeAnchors.mp hanchor).1
  · exact hk
  · exact hell
  · intro anchor hanchor i
    exact typeIIRelevantCubeAnchor_margin hregion hmarginWidth
      (mem_typeIIInteriorCubeAnchors.mp hanchor).1 i
  · intro anchor hanchor
    exact typeIIRelevantCubeAnchor_room heta (by omega) hregion
      (mem_typeIIInteriorCubeAnchors.mp hanchor).1
  · intro anchor hanchor
    exact typeIIInteriorCubeAnchor_separated hdelta hregion hanchor
  · intro anchor hanchor
    exact typeIIRelevantCubeAnchor_convenient hepsilon hdelta herror
      hconvenient (mem_typeIIInteriorCubeAnchors.mp hanchor).1

end

end PrimesRestrictedDigits
