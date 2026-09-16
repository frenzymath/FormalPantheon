import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectFormalSignedTargetAggregation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption

/-!
# Two-band absorption of formal signed target errors

This combines the two literal direct bands in the proof of Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 149--152, and absorbs their fixed finite wall coefficient against
the varying log-log width.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The fixed nonnegative wall ledger for the two literal direct bands. -/
noncomputable def
    sectionSixDirectTwoBandSignedWeakPieceCanonicalWallCoefficientSum
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (epsilon delta : Real) (M : Nat) : Real :=
  sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum presentation
      epsilon delta .first M +
    sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum presentation
      epsilon delta .second M

/-- The sum of the first- and second-band wall ledgers is nonnegative. -/
theorem
    sectionSixDirectTwoBandSignedWeakPieceCanonicalWallCoefficientSum_nonneg
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (epsilon delta : Real) (M : Nat) :
    0 <= sectionSixDirectTwoBandSignedWeakPieceCanonicalWallCoefficientSum
      presentation epsilon delta M := by
  exact add_nonneg
    (sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum_nonneg
      presentation epsilon delta .first M)
    (sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum_nonneg
      presentation epsilon delta .second M)

set_option maxHeartbeats 2400000 in
/-- The algebraic sum of the two direct-band near discrepancies differs from
the sum of their formal target diagonals by an arbitrary positive logarithmic
budget at all sufficiently large decimal lengths. -/
theorem
    exists_sectionSixDirectTwoBandFormalSignedWeakPieceTargetError_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget) :
    forall epsilon : Real, 0 < epsilon ->
      forall (ell : Nat) (region : Set (Fin ell -> Real))
        (presentation : TypeIIAffineMixedPresentation region),
        exists length0 : Nat, 1 <= length0 ∧
          forall length : Nat, length0 <= length ->
          forall digit : Fin 10,
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let M : Nat := Nat.ceil (2 / delta)
            let lambda : Real :=
              (restrictedDigitDensity digit : Real) * (A.card : Real) / X
            let nearDiscrepancy : SectionSixDirectBand -> Real := fun band =>
              ((sectionSixDirectNearCandidates epsilon delta rho ell region
                length band A).card : Real) -
                lambda * ((sectionSixDirectNearCandidates epsilon delta rho
                  ell region length band B).card : Real)
            let formalTargetDiscrepancy : SectionSixDirectBand -> Real :=
              fun band =>
                sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
                  presentation digit epsilon delta rho length band
            epsilon <= 1 / 64 ->
            delta < sectionSixThetaGap epsilon ->
            rho ^ 2 < delta ->
            2 * rho <= delta / 2 ->
            rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
            abs ((nearDiscrepancy .first + nearDiscrepancy .second) -
                (formalTargetDiscrepancy .first +
                  formalTargetDiscrepancy .second)) <=
              budget * (A.card : Real) / Real.log X := by
  obtain ⟨Cdelta, hCdelta, hError⟩ :=
    exists_sectionSixDirectFormalSignedWeakPieceTargetError_delta_upper
      delta hdelta
  intro epsilon hepsilon ell region presentation
  let M : Nat := Nat.ceil (2 / delta)
  let Kfirst : Real :=
    sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum presentation
      epsilon delta .first M
  let Ksecond : Real :=
    sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum presentation
      epsilon delta .second M
  let K : Real := Cdelta * (Kfirst + Ksecond)
  have hK : 0 <= K := by
    dsimp only [K, Kfirst, Ksecond]
    exact mul_nonneg hCdelta.le
      (sectionSixDirectTwoBandSignedWeakPieceCanonicalWallCoefficientSum_nonneg
        presentation epsilon delta M)
  obtain ⟨lengthAbsorb, hlengthAbsorbOne, hAbsorb⟩ :=
    exists_mul_majorArcM2LogLogDelta_powTen_le K budget hK hbudget
  obtain ⟨lengthFirst, hlengthFirstOne, hFirst⟩ :=
    hError epsilon hepsilon ell region .first presentation
  obtain ⟨lengthSecond, hlengthSecondOne, hSecond⟩ :=
    hError epsilon hepsilon ell region .second presentation
  let length0 : Nat := max lengthAbsorb (max lengthFirst lengthSecond)
  have hlength0One : 1 <= length0 :=
    hlengthAbsorbOne.trans (le_max_left _ _)
  refine ⟨length0, hlength0One, ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hlengthAbsorb : lengthAbsorb <= length :=
    (le_max_left _ _).trans hlength
  have hlengthFirst : lengthFirst <= length :=
    (le_max_left lengthFirst lengthSecond).trans
      ((le_max_right lengthAbsorb _).trans hlength)
  have hlengthSecond : lengthSecond <= length :=
    (le_max_right lengthFirst lengthSecond).trans
      ((le_max_right lengthAbsorb _).trans hlength)
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let nearDiscrepancy : SectionSixDirectBand -> Real := fun band =>
    ((sectionSixDirectNearCandidates epsilon delta rho ell region length band A).card :
      Real) -
      lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell region
        length band B).card : Real)
  let formalTargetDiscrepancy : SectionSixDirectBand -> Real := fun band =>
    sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
      presentation digit epsilon delta rho length band
  have hFirstAt := hFirst length hlengthFirst digit hepsilonSmall
    hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hSecondAt := hSecond length hlengthSecond digit hepsilonSmall
    hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hFirstBound :
      abs (nearDiscrepancy .first - formalTargetDiscrepancy .first) <=
        Cdelta * ((rho * Kfirst) * (A.card : Real) / Real.log X) := by
    simpa only [nearDiscrepancy, formalTargetDiscrepancy, XNat, X, rho, A, B,
      M, lambda, Kfirst] using hFirstAt
  have hSecondBound :
      abs (nearDiscrepancy .second - formalTargetDiscrepancy .second) <=
        Cdelta * ((rho * Ksecond) * (A.card : Real) / Real.log X) := by
    simpa only [nearDiscrepancy, formalTargetDiscrepancy, XNat, X, rho, A, B,
      M, lambda, Ksecond] using hSecondAt
  have hScalar : K * rho <= budget := by
    simpa only [XNat, rho] using hAbsorb length hlengthAbsorb
  have hlengthOne : 1 <= length := hlength0One.trans hlength
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hmass : 0 <= (A.card : Real) / Real.log X := by
    positivity
  calc
    abs ((nearDiscrepancy .first + nearDiscrepancy .second) -
        (formalTargetDiscrepancy .first +
          formalTargetDiscrepancy .second)) =
        abs ((nearDiscrepancy .first - formalTargetDiscrepancy .first) +
          (nearDiscrepancy .second - formalTargetDiscrepancy .second)) := by
      congr 1
      ring
    _ <= abs (nearDiscrepancy .first - formalTargetDiscrepancy .first) +
        abs (nearDiscrepancy .second - formalTargetDiscrepancy .second) :=
      abs_add_le _ _
    _ <= Cdelta * ((rho * Kfirst) * (A.card : Real) / Real.log X) +
        Cdelta * ((rho * Ksecond) * (A.card : Real) / Real.log X) :=
      add_le_add hFirstBound hSecondBound
    _ = (K * rho) * ((A.card : Real) / Real.log X) := by
      dsimp only [K]
      ring
    _ <= budget * ((A.card : Real) / Real.log X) :=
      mul_le_mul_of_nonneg_right hScalar hmass
    _ = budget * (A.card : Real) / Real.log X := by ring

end

end PrimesRestrictedDigits
