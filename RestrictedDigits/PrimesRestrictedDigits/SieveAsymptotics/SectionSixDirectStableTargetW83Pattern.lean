import PrimesRestrictedDigits.SieveAsymptotics.PropositionSevenTwo
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# for one direct stable-pattern target

An arbitrary syntactic stable pattern need not satisfy arity cap. For a nonempty target the
cap follows from its simplex lower bounds; an empty target has zero support and zero
discrepancy.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A nonempty ordered eta-simplex has at most `2 / eta` coordinates. -/
theorem typeIISourceRegion_arity_le_two_div_of_nonempty
    {eta : Real} {k : Nat} {region : Set (Fin (k + 1) -> Real)}
    (heta : 0 < eta)
    (hregion : IsTypeIISourceRegion eta region)
    (hnonempty : region.Nonempty) :
    (((k + 1 : Nat) : Real) <= 2 / eta) := by
  obtain ⟨x, hx⟩ := hnonempty
  have hsource := hregion hx
  have hsumLower : (∑ _ : Fin (k + 1), eta) <= ∑ i, x i :=
    Finset.sum_le_sum fun i _ => hsource.1 i
  have harityMul : (((k + 1 : Nat) : Real) * eta) <= 1 := by
    calc
      (((k + 1 : Nat) : Real) * eta) = ∑ _ : Fin (k + 1), eta := by simp
      _ <= ∑ i, x i := hsumLower
      _ = 1 := hsource.2.2
  apply (le_div_iff₀ heta).2
  linarith

/--
specialized to one fixed stable-pattern target. Empty targets are handled exactly, without
imposing an arity condition on the syntax.
-/
theorem exists_sectionSixDirectStableTargetSupportDiscrepancy_delta_upper
    (delta : Real) (hdelta : 0 < delta)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell M : Nat) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) :
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
              (sectionSixDirectStableTargetRegion epsilon delta region band
                pattern)
            abs (((support.filter fun n => n ∈ A).card : Real) -
                lambda * ((support.filter fun n => n ∈ B).card : Real)) <=
              Cpattern * rho * (A.card : Real) / Real.log X := by
  let target := sectionSixDirectStableTargetRegion epsilon delta region band
    pattern
  have hregion : IsTypeIISourceRegion delta target :=
    sectionSixDirectStableTargetRegion_isTypeIISourceRegion epsilon delta region
      band pattern
  by_cases hnonempty : target.Nonempty
  · have harity :
        ((((ell + pattern.1.1) + 1 : Nat) : Real) <= 2 / delta) :=
      typeIISourceRegion_arity_le_two_div_of_nonempty hdelta hregion hnonempty
    obtain ⟨Cpattern, hCpattern, hestimate⟩ :=
      exists_typeIIRegionEstimate_eta_upper delta hdelta hregion harity
        (sectionSixDirectStableTargetPresentation sourcePresentation epsilon delta
          band pattern)
    obtain ⟨length0, hlength0, hAt⟩ :=
      hestimate epsilon hepsilon
        (sectionSixDirectStableTargetRegion_convenient hepsilon.le region band
          pattern)
    refine ⟨Cpattern, hCpattern, length0, hlength0, ?_⟩
    intro length hlength digit
    have hbound := hAt length hlength digit
    dsimp only [target] at hbound
    dsimp only
    rw [typeIIOriginalRegionSupport_filter_ambient_eq_self]
    exact hbound
  · have htarget : target = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
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
          (((support.filter fun n => n ∈ maynardAmbientCarrier X).card : Real)))| <=
      1 * rho * (A.card : Real) / Real.log X
    rw [hsupport]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
      sub_self, abs_zero, one_mul]
    positivity

end

end PrimesRestrictedDigits
