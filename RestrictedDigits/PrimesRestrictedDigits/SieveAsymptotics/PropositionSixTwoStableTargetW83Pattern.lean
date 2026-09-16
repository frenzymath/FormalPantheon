import PrimesRestrictedDigits.SieveAsymptotics.PropositionSevenTwoRawArity
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetPresentation

/-!
# Proposition 7.2 for one Proposition 6.2 stable target

A nonempty fixed-pattern target supplies its arity bound from the ordered theta-gap simplex.
An empty target has empty support and zero discrepancy.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Proposition 7.2 specialized to one fixed Proposition 6.2 stable target.
The constant is chosen before the decimal length and excluded digit. -/
theorem exists_propositionSixTwoStableTargetSupportDiscrepancy_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {ell : Nat} (I : Finset (Fin ell)) (j : Fin ell)
    (M : Nat) (sourceRegion : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M) :
    ∃ Cpattern : Real, 0 < Cpattern ∧
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
          let support : Finset Nat := typeIIOriginalRegionSupport XNat
            (propositionSixTwoStableTargetRegion
              epsilon I sourceRegion band pattern)
          abs (((support.filter fun n => n ∈ A).card : Real) -
              lambda * ((support.filter fun n => n ∈ B).card : Real)) <=
            Cpattern * rho * (A.card : Real) / Real.log X := by
  let eta : Real := sectionSixThetaGap epsilon
  let target := propositionSixTwoStableTargetRegion
    epsilon I sourceRegion band pattern
  have heta : 0 < eta := by
    simpa only [eta] using
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hd : 0 < ell + pattern.1.1 := by
    have hell : 0 < ell := Nat.zero_lt_of_lt j.isLt
    omega
  have htargetSource : IsTypeIISourceRegion eta target := by
    simpa only [eta, target] using
      propositionSixTwoStableTargetRegion_isTypeIISourceRegion
        epsilon I sourceRegion band pattern
  by_cases htargetNonempty : target.Nonempty
  · have harity : (((ell + pattern.1.1 : Nat) : Real) <= 2 / eta) :=
      typeIISourceRegion_rawArity_le_two_div_of_nonempty
        heta htargetSource htargetNonempty
    obtain ⟨Cpattern, hCpattern, hestimate⟩ :=
      exists_typeIIRegionEstimate_raw_eta_upper eta heta hd htargetSource harity
        (propositionSixTwoStableTargetPresentation sourcePresentation epsilon I
          band pattern hd)
    obtain ⟨length0, hlength0, hAt⟩ :=
      hestimate epsilon hepsilon
        (propositionSixTwoStableTargetRegion_convenient hepsilon.le I
          sourceRegion band pattern)
    refine ⟨Cpattern, hCpattern, length0, hlength0, ?_⟩
    intro length hlength digit
    have hbound := hAt length hlength digit
    dsimp only [eta, target] at hbound
    dsimp only
    rw [typeIIOriginalRegionSupport_filter_ambient_eq_self]
    exact hbound
  · have htarget : target = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp htargetNonempty
    refine ⟨1, by norm_num, 1, le_rfl, ?_⟩
    intro length hlength digit
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let rho : Real := majorArcM2LogLogDelta XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let support : Finset Nat := typeIIOriginalRegionSupport XNat target
    have hXOne : 1 < X := by
      dsimp only [X, XNat]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hlog : 0 < Real.log X := Real.log_pos hXOne
    have hrho : 0 < rho := by
      dsimp only [rho, XNat]
      exact majorArcM2LogLogDelta_powTen_pos hlength
    have hsupport : support = ∅ := by
      dsimp only [support]
      rw [htarget]
      simp [typeIIOriginalRegionSupport, typeIIOriginalRegionPredicate]
    dsimp only
    change |(((support.filter fun n => n ∈ A).card : Real) -
        (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
          (((support.filter fun n =>
            n ∈ maynardAmbientCarrier X).card : Real)))| <=
      1 * rho * (A.card : Real) / Real.log X
    rw [hsupport]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
      sub_self, abs_zero, one_mul]
    positivity

end

end PrimesRestrictedDigits
