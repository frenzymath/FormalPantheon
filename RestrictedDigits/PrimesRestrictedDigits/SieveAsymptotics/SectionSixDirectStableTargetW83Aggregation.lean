import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetReverseCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetW83Pattern

/-!
# aggregation over active direct stable-pattern targets

Patternwise coefficients and thresholds are selected over the full fixed stable-pattern type.
At a later length, the ambiently active subset is enlarged to that full type only after taking
absolute values.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/--
The active-target Sigma discrepancy is bounded by one finite aggregate of the patternwise
errors, uniformly in decimal length and excluded digit.
-/
theorem exists_sectionSixDirectActiveStableTargetDiscrepancy_delta_upper
    (delta : Real) (hdelta : 0 < delta)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell M : Nat) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) :
    ∃ Ctarget : Real, 0 < Ctarget ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          ∀ digit : Fin 10,
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let lambda : Real :=
              (restrictedDigitDensity digit : Real) * (A.card : Real) / X
            let activeTargetCount : Finset Nat -> Real := fun C =>
              ((sectionSixDirectActiveStableTargetValues epsilon delta rho ell
                region length band B C M).card : Real)
            abs (activeTargetCount A - lambda * activeTargetCount B) <=
              Ctarget * rho * (A.card : Real) / Real.log X := by
  let Pattern := SectionSixDirectStablePattern ell M
  have hPattern : ∀ pattern : Pattern,
      ∃ Cpattern : Real, 0 < Cpattern ∧
        ∃ threshold : Nat, 1 <= threshold ∧
          ∀ length : Nat, threshold <= length ->
          ∀ digit : Fin 10,
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let support : Finset Nat := typeIIOriginalRegionSupport XNat
              (sectionSixDirectStableTargetRegion epsilon delta region band
                pattern)
            |((support.filter fun n => n ∈ A).card : Real) -
                (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
                  ((support.filter fun n => n ∈ B).card : Real)| <=
              Cpattern * rho * (A.card : Real) / Real.log X := by
    intro pattern
    simpa only using
      exists_sectionSixDirectStableTargetSupportDiscrepancy_delta_upper
        delta hdelta epsilon hepsilon ell M region sourcePresentation band pattern
  choose Cpattern hCpatternData using hPattern
  have hThresholdExists : ∀ pattern : Pattern,
      ∃ threshold : Nat, 1 <= threshold ∧
        ∀ length : Nat, threshold <= length ->
        ∀ digit : Fin 10,
          let XNat : Nat := 10 ^ length
          let X : Real := (XNat : Real)
          let rho : Real := majorArcM2LogLogDelta XNat
          let A : Finset Nat := paddedRestrictedNumbers digit length
          let B : Finset Nat := maynardAmbientCarrier X
          let support : Finset Nat := typeIIOriginalRegionSupport XNat
            (sectionSixDirectStableTargetRegion epsilon delta region band pattern)
          |((support.filter fun n => n ∈ A).card : Real) -
              (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
                ((support.filter fun n => n ∈ B).card : Real)| <=
            Cpattern pattern * rho * (A.card : Real) / Real.log X := by
    intro pattern
    exact (hCpatternData pattern).2
  choose threshold hthresholdData using hThresholdExists
  let Ctarget : Real := 1 + ∑ pattern : Pattern, Cpattern pattern
  let length0 : Nat := max 1 (∑ pattern : Pattern, threshold pattern)
  have hCtarget : 0 < Ctarget := by
    have hsumNonneg : 0 <= ∑ pattern : Pattern, Cpattern pattern := by
      apply Finset.sum_nonneg
      intro pattern _
      exact (hCpatternData pattern).1.le
    dsimp only [Ctarget]
    linarith
  have hlength0 : 1 <= length0 := le_max_left _ _
  refine ⟨Ctarget, hCtarget, length0, hlength0, ?_⟩
  intro length hlength digit
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let active := sectionSixDirectActiveStablePatterns epsilon delta rho ell region
    length band B M
  let support : Pattern -> Finset Nat := fun pattern =>
    typeIIOriginalRegionSupport XNat
      (sectionSixDirectStableTargetRegion epsilon delta region band pattern)
  let signedError : Pattern -> Real := fun pattern =>
    ((support pattern).filter fun n => n ∈ A).card -
      lambda * ((support pattern).filter fun n => n ∈ B).card
  let error : Pattern -> Real := fun pattern => |signedError pattern|
  let activeTargetCount : Finset Nat -> Real := fun C =>
    ((sectionSixDirectActiveStableTargetValues epsilon delta rho ell region
      length band B C M).card : Real)
  have hlengthOne : 1 <= length := hlength0.trans hlength
  have hXOne : 1 < X := by
    dsimp only [X, XNat]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hlog : 0 < Real.log X := Real.log_pos hXOne
  have hrho : 0 < rho := by
    dsimp only [rho, XNat]
    exact majorArcM2LogLogDelta_powTen_pos hlengthOne
  have hscaleNonneg : 0 <= rho * (A.card : Real) / Real.log X := by
    positivity
  have hthresholdLe (pattern : Pattern) : threshold pattern <= length0 := by
    calc
      threshold pattern <= ∑ current : Pattern, threshold current := by
        exact Finset.single_le_sum (fun current _ => Nat.zero_le _)
          (Finset.mem_univ pattern)
      _ <= length0 := le_max_right _ _
  have hpatternBound (pattern : Pattern) :
      error pattern <=
        Cpattern pattern * rho * (A.card : Real) / Real.log X := by
    have hAt := (hthresholdData pattern).2 length
      ((hthresholdLe pattern).trans hlength) digit
    simpa only [error, signedError, support, lambda, XNat, X, rho, A, B,
      Nat.cast_ofNat] using hAt
  have hsumBound :
      (∑ pattern : Pattern, error pattern) <=
        Ctarget * rho * (A.card : Real) / Real.log X := by
    calc
      (∑ pattern : Pattern, error pattern) <=
          ∑ pattern : Pattern,
            Cpattern pattern * rho * (A.card : Real) / Real.log X := by
        exact Finset.sum_le_sum fun pattern _ => hpatternBound pattern
      _ = (∑ pattern : Pattern, Cpattern pattern) *
          (rho * (A.card : Real) / Real.log X) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro pattern _
        ring
      _ <= Ctarget * (rho * (A.card : Real) / Real.log X) := by
        apply mul_le_mul_of_nonneg_right _ hscaleNonneg
        dsimp only [Ctarget]
        linarith
      _ = Ctarget * rho * (A.card : Real) / Real.log X := by
        ring
  have htargetCount (C : Finset Nat) :
      activeTargetCount C =
        ∑ pattern ∈ active,
          (((support pattern).filter fun n => n ∈ C).card : Real) := by
    dsimp only [activeTargetCount, active, support,
      sectionSixDirectActiveStableTargetValues]
    rw [Finset.card_sigma, Nat.cast_sum]
  have hdiscrepancy :
      activeTargetCount A - lambda * activeTargetCount B =
        ∑ pattern ∈ active, signedError pattern := by
    rw [htargetCount A, htargetCount B]
    dsimp only [signedError]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  change |activeTargetCount A - lambda * activeTargetCount B| <=
    Ctarget * rho * (A.card : Real) / Real.log X
  rw [hdiscrepancy]
  calc
    |∑ pattern ∈ active, signedError pattern| <=
        ∑ pattern ∈ active, error pattern := by
      simpa only [error] using
        (Finset.abs_sum_le_sum_abs signedError active)
    _ <= ∑ pattern : Pattern, error pattern := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active)
      intro pattern _ _
      exact abs_nonneg _
    _ <= Ctarget * rho * (A.card : Real) / Real.log X := hsumBound

end

end PrimesRestrictedDigits
