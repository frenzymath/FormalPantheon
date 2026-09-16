import PrimesRestrictedDigits.SieveAsymptotics.PropositionSevenTwo

/-!
# Proposition 7.2 at raw positive arity

This file removes the syntactic `k + 1` arity convention from Proposition 7.2. It also records
the elementary arity bound forced by a nonempty source region.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A nonempty source region has at most `2 / eta` coordinates. -/
theorem typeIISourceRegion_rawArity_le_two_div_of_nonempty
    {eta : Real} {d : Nat} {region : Set (Fin d -> Real)}
    (heta : 0 < eta) (hregion : IsTypeIISourceRegion eta region)
    (hnonempty : region.Nonempty) :
    ((d : Real) <= 2 / eta) := by
  obtain ⟨x, hx⟩ := hnonempty
  have hsource := hregion hx
  have hsumLower : (∑ _ : Fin d, eta) <= ∑ i, x i :=
    Finset.sum_le_sum fun i _ => hsource.1 i
  have harityMul : (d : Real) * eta <= 1 := by
    calc
      (d : Real) * eta = ∑ _ : Fin d, eta := by simp
      _ <= ∑ i, x i := hsumLower
      _ = 1 := hsource.2.2
  apply (le_div_iff₀ heta).2
  linarith

/-- Proposition 7.2 for an arbitrary positive natural arity. -/
theorem exists_typeIIRegionEstimate_raw_eta_upper
    (eta : Real) (heta : 0 < eta)
    {d : Nat} (hd : 0 < d) {region : Set (Fin d -> Real)}
    (hregion : IsTypeIISourceRegion eta region)
    (hell : ((d : Real) <= 2 / eta))
    (presentation : TypeIIAffineHalfspacePresentation region) :
    ∃ CregionEta : Real, 0 < CregionEta ∧
      ∀ margin : Real, 0 < margin ->
        IsTypeIIRegionConvenient margin region ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ digit : Fin 10,
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let support : Finset Nat := typeIIOriginalRegionSupport XNat region
            abs (((support.filter fun n => n ∈ A).card : Real) -
                (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
                  (support.card : Real)) <=
              CregionEta * rho * (A.card : Real) / Real.log X := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  simpa only [Nat.succ_eq_add_one] using
    exists_typeIIRegionEstimate_eta_upper eta heta hregion hell presentation

end

end PrimesRestrictedDigits
