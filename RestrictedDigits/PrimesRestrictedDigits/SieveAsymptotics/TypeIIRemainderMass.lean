import PrimesRestrictedDigits.SieveAsymptotics.TypeIICellSupportMass
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRemainderCount
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionInteriorFamily

/-!
# Type II remainder-family analytic mass

This combines the positive one-cell support-mass estimate with the full-grid logarithmic
absorption and the codimension-one remainder count. It is the remainder contribution in Eqs.
(9.5)--(9.6) of `MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The positive Boolean support mass of all remainder cells is bounded at
the source scale.  The coefficient is fixed from `eta` and the affine
presentation before the convenience margin, decimal length, digit, and
log-log width are quantified. -/
theorem exists_typeIIRemainderRegionFamilyMass_eta_upper
    (eta : Real) (heta : 0 < eta)
    {k : Nat} (hk : 1 <= k)
    {region : Set (Fin (k + 1) -> Real)}
    (hregion : IsTypeIISourceRegion eta region)
    (hell : (((k + 1 : Nat) : Real) <= 2 / eta))
    (presentation : TypeIIAffineHalfspacePresentation region) :
    ∃ CregionEta : Real, 0 < CregionEta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        IsTypeIIRegionConvenient epsilon region ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ digit : Fin 10,
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let delta : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let anchors : Finset (Fin k -> Nat) :=
              typeIIRemainderCubeAnchors delta region
            let supportCount : (Fin k -> Nat) -> Finset Nat -> Real :=
              fun anchor C => typeIICellSupportCount XNat
                (scaledNaturalCubeAnchor delta anchor) delta eta C
            anchors.sum (fun anchor =>
                supportCount anchor A +
                  (restrictedDigitDensity digit : Real) *
                    (A.card : Real) / X * supportCount anchor B) <=
              CregionEta * delta * (A.card : Real) / Real.log X := by
  obtain ⟨Ccell, hCcell, hcell⟩ :=
    exists_typeIIOneCellSupportMass_eta_upper eta heta
  obtain ⟨Cregion, hCregion, hregionCard⟩ :=
    exists_typeIIRemainderCubeAnchorCard_upper presentation
  let CregionEta : Real := Ccell * (1 + Cregion)
  have hCregionEta : 0 < CregionEta := by
    dsimp only [CregionEta]
    positivity
  refine ⟨CregionEta, hCregionEta, ?_⟩
  intro epsilon hepsilon hconvenient
  obtain ⟨cellLength, hcellLength, hcellAt⟩ :=
    hcell (epsilon / 2) (by positivity)
  let rho : Real := min (eta / 4) (min (1 / 2) (epsilon / 4))
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  obtain ⟨scalarLength, hscalarAt⟩ :=
    exists_exceptionalLogLogWidthMarginThreshold eta rho heta hrho
  let length0 := max cellLength scalarLength
  refine ⟨length0, hcellLength.trans (Nat.le_max_left _ _), ?_⟩
  intro length hlength digit
  have hcellLengthAt : cellLength <= length :=
    (Nat.le_max_left _ _).trans hlength
  have hscalarLengthAt : scalarLength <= length :=
    (Nat.le_max_right _ _).trans hlength
  have hlengthOne : 1 <= length :=
    hcellLength.trans hcellLengthAt
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let delta : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let anchors : Finset (Fin k -> Nat) :=
    typeIIRemainderCubeAnchors delta region
  let supportCount : (Fin k -> Nat) -> Finset Nat -> Real :=
    fun anchor C => typeIICellSupportCount XNat
      (scaledNaturalCubeAnchor delta anchor) delta eta C
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let mass : (Fin k -> Nat) -> Real := fun anchor =>
    supportCount anchor A + lambda * supportCount anchor B
  let card : Real := (A.card : Real)
  let L : Real := Real.log X
  let first : Real := (anchors.card : Real) * card / L ^ (k + 2)
  let second : Real :=
    (anchors.card : Real) * (delta ^ k * card / L)
  let target : Real := delta * card / L
  change anchors.sum mass <= CregionEta * delta * card / L
  have hdelta : 0 < delta := by
    dsimp only [delta, XNat]
    exact majorArcM2LogLogDelta_powTen_pos hlengthOne
  have hscalar := hscalarAt length hscalarLengthAt
  dsimp only at hscalar
  have hbudget := hscalar.2 k hell
  have hlengthInv : 0 <= 1 / (length : Real) := by positivity
  have hmulLeRho : ((k + 1 : Nat) : Real) * delta <= rho := by
    dsimp only [delta, XNat]
    linarith
  have honeCast : (1 : Real) <= ((k + 1 : Nat) : Real) := by
    exact_mod_cast (show 1 <= k + 1 by omega)
  have hkCast : (k : Real) <= ((k + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ k
  have hdeltaLeRho : delta <= rho := by
    have hmul := mul_le_mul_of_nonneg_right honeCast hdelta.le
    simpa only [one_mul] using hmul.trans hmulLeRho
  have hrhoEta : rho <= eta / 4 := by simp [rho]
  have hrhoHalf : rho <= 1 / 2 := by simp [rho]
  have hrhoEpsilon : rho <= epsilon / 4 := by simp [rho]
  have hmarginWidth : 2 * delta <= eta / 2 := by
    linarith [hdeltaLeRho.trans hrhoEta]
  have hdeltaOne : delta <= 1 := by
    linarith [hdeltaLeRho.trans hrhoHalf]
  have herror : 2 * (k : Real) * delta <= epsilon / 2 := by
    have hkMul : (k : Real) * delta <=
        ((k + 1 : Nat) : Real) * delta :=
      mul_le_mul_of_nonneg_right hkCast hdelta.le
    linarith [hkMul, hmulLeRho, hrhoEpsilon]
  have hlocal (anchor : Fin k -> Nat) (hanchor : anchor ∈ anchors) :
      mass anchor <= Ccell *
        (card / L ^ (k + 2) + delta ^ k * card / L) := by
    have hrelevant : anchor ∈ typeIIRelevantCubeAnchors delta region :=
      (mem_typeIIRemainderCubeAnchors.mp hanchor).1
    have hmargin : ∀ i,
        eta / 2 <= scaledNaturalCubeAnchor delta anchor i :=
      typeIIRelevantCubeAnchor_margin hregion hmarginWidth hrelevant
    have hroom :
        (∑ i, scaledNaturalCubeAnchor delta anchor i) < 1 - eta / 2 :=
      typeIIRelevantCubeAnchor_room heta (by omega) hregion hrelevant
    obtain ⟨I, hI⟩ := typeIIRelevantCubeAnchor_convenient
      hepsilon hdelta herror hconvenient hrelevant
    have hbound := hcellAt length hcellLengthAt digit k
      (scaledNaturalCubeAnchor delta anchor) I hmargin hroom hell hI
    simpa only [mass, supportCount, lambda, card, L, A, B, X, XNat,
      delta] using hbound
  have hsumLocal : anchors.sum mass <= Ccell * (first + second) := by
    calc
      anchors.sum mass <= anchors.sum (fun _anchor =>
          Ccell * (card / L ^ (k + 2) + delta ^ k * card / L)) :=
        Finset.sum_le_sum hlocal
      _ = Ccell * (first + second) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp only [first, second]
        ring
  have hanchors : anchors ⊆ typeIINaturalCubeGrid k delta := by
    intro anchor hanchor
    exact typeIIRelevantCubeAnchors_subset_grid delta region
      (mem_typeIIRemainderCubeAnchors.mp hanchor).1
  have hcardNonneg : 0 <= card := by
    dsimp only [card]
    positivity
  have hfirst : first <= target := by
    have hgrid := typeIIAnchorFamily_logError_le_delta_logError
      hlengthOne anchors hanchors card hcardNonneg
    simpa only [first, target, card, L, X, XNat, delta] using hgrid
  have hanchorCard := hregionCard delta hdelta hdeltaOne
  have hpow : delta⁻¹ ^ (k - 1) * delta ^ k = delta := by
    cases k with
    | zero => omega
    | succ n =>
        simp only [Nat.succ_sub_one, pow_succ]
        rw [← mul_assoc, ← mul_pow]
        simp [hdelta.ne']
  have hsecond : second <= Cregion * target := by
    have hfactorNonneg : 0 <= delta ^ k * card / L := by positivity
    calc
      second <=
          (Cregion * delta⁻¹ ^ (k - 1)) *
            (delta ^ k * card / L) := by
        dsimp only [second]
        exact mul_le_mul_of_nonneg_right hanchorCard hfactorNonneg
      _ = Cregion * target := by
        dsimp only [target]
        rw [show
          (Cregion * delta⁻¹ ^ (k - 1)) *
              (delta ^ k * card / L) =
            Cregion *
              (delta⁻¹ ^ (k - 1) * delta ^ k) * card / L by ring,
          hpow]
        ring
  have htwoTerms : first + second <= (1 + Cregion) * target := by
    calc
      first + second <= target + Cregion * target :=
        add_le_add hfirst hsecond
      _ = (1 + Cregion) * target := by ring
  apply hsumLocal.trans
  calc
    Ccell * (first + second) <=
        Ccell * ((1 + Cregion) * target) :=
      mul_le_mul_of_nonneg_left htwoTerms hCcell.le
    _ = CregionEta * delta * card / L := by
      dsimp only [CregionEta, target]
      ring

end

end PrimesRestrictedDigits
