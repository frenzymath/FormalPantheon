import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullSourceWellFoundedShell
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserRawFullSourceLedger
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFullSourceBase
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceReadyData

/-!
# Full-source ready-step assembly

This module composes the tail-free complete shell with the rank-free raw cutoff ledger. It is
a one-step adapter, not the carrier induction or the upper low-coordinate closure.
-/

namespace PrimesRestrictedDigits

theorem dimensionOneRosserFullSourceUpperTarget_mono_in_multiplier
    (P : Finset Nat) {D₁ D₂ level z s : Real}
    (hD : D₁ <= D₂) (hprime : ∀ p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hsOne : 1 < s)
    (hTarget : dimensionOneRosserFullSourceUpperTarget P D₁ level z s) :
    dimensionOneRosserFullSourceUpperTarget P D₂ level z s := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    (sieveDensityBelow_reciprocal_pos P z hprime).le
  have hprofile : 0 <=
      dimensionOneRosserSourcePlusProfile (Real.log level) s := by
    unfold dimensionOneRosserSourcePlusProfile
    exact mul_nonneg (Real.rpow_pos_of_pos hL _).le
      (dimensionOneRosserPlusArtificialAux_pos hL hsPos).le
  have hscale : 0 <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg hV hsPos.le
  unfold dimensionOneRosserFullSourceUpperTarget at hTarget ⊢
  have hmul := mul_le_mul_of_nonneg_right hD hprofile
  have hcoef :
      dimensionOneRosserModelPlusRaw s +
          D₁ * dimensionOneRosserSourcePlusProfile (Real.log level) s <=
        dimensionOneRosserModelPlusRaw s +
          D₂ * dimensionOneRosserSourcePlusProfile (Real.log level) s := by
    simpa [add_comm] using add_le_add_left hmul
      (dimensionOneRosserModelPlusRaw s)
  exact hTarget.trans_le (mul_le_mul_of_nonneg_left hcoef hscale)

theorem dimensionOneRosserFullSourceLowerTarget_mono_in_multiplier
    (P : Finset Nat) {D₁ D₂ level z s : Real}
    (hD : D₁ <= D₂) (hprime : ∀ p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hsTwo : 2 <= s)
    (hTarget : dimensionOneRosserFullSourceLowerTarget P D₁ level z s) :
    dimensionOneRosserFullSourceLowerTarget P D₂ level z s := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    (sieveDensityBelow_reciprocal_pos P z hprime).le
  have hprofile : 0 <=
      dimensionOneRosserSourceMinusProfile (Real.log level) s := by
    unfold dimensionOneRosserSourceMinusProfile
    exact mul_nonneg (Real.rpow_pos_of_pos hL _).le
      (dimensionOneRosserMinusArtificialAux_pos hL hsPos).le
  have hscale : 0 <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg hV hsPos.le
  unfold dimensionOneRosserFullSourceLowerTarget at hTarget ⊢
  have hmul := mul_le_mul_of_nonneg_right hD hprofile
  have hcoef :
      dimensionOneRosserModelMinusRaw s +
          D₁ * dimensionOneRosserSourceMinusProfile (Real.log level) s <=
        dimensionOneRosserModelMinusRaw s +
          D₂ * dimensionOneRosserSourceMinusProfile (Real.log level) s := by
    simpa [add_comm] using add_le_add_left hmul
      (dimensionOneRosserModelMinusRaw s)
  exact hTarget.trans_le (mul_le_mul_of_nonneg_left hcoef hscale)

theorem dimensionOneRosserBudgetFreeDirectState_of_cutoffData
    {Sbase Sdata K level s : Real}
    (hS : Sbase <= Sdata)
    (data : DimensionOneRosserSourceCutoffData K Sdata level)
    (hs0s : data.s0 <= s) :
    dimensionOneRosserBudgetFreeDirectState Sbase level s := by
  exact ⟨data.s0, hS.trans data.hsTail, hs0s, data.hLExp, data.hsource⟩

theorem dimensionOneRosserSourceCutoffData_coordinate_eq
    {K Sdata level : Real} (hS : Real.exp 5000 + 1 <= Sdata)
    (hlevel : 2 <= level)
    (data : DimensionOneRosserSourceCutoffData K Sdata level) :
    data.s0 = Real.log level /
      Real.log (level ^ (1 / data.s0)) := by
  have hs0Pos : 0 < data.s0 := by
    have : Real.exp 5000 + 1 <= data.s0 := hS.trans data.hsTail
    linarith [Real.exp_pos (5000 : Real)]
  have hlevelPos : 0 < level := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  rw [log_rpow_one_div hlevelPos]
  field_simp [hL.ne', hs0Pos.ne']

private theorem dimensionOneRosserReadyBracket_le_upper
    {D s0 raw profile : Real} (hD : 0 <= D)
    (hs0 : 0 < s0) (_hraw : 0 <= raw) (hprofile : 0 <= profile) :
    raw - dimensionOneRosserModelPlusRaw s0 +
        D * (1 - 1 / (2 * s0)) * profile <= raw + D * profile := by
  have hcoeff : 1 - 1 / (2 * s0) <= (1 : Real) := by
    exact sub_le_self _ (by positivity)
  have hDprofile : 0 <= D * profile := mul_nonneg hD hprofile
  have hterm : D * (1 - 1 / (2 * s0)) * profile <= D * profile := by
    calc
      D * (1 - 1 / (2 * s0)) * profile =
          (1 - 1 / (2 * s0)) * (D * profile) := by ring
      _ <= 1 * (D * profile) :=
        mul_le_mul_of_nonneg_right hcoeff hDprofile
      _ = D * profile := by ring
  linarith [dimensionOneRosserModelPlusRaw_nonneg s0]

private theorem dimensionOneRosserReadyBracket_le_lower
    {D s0 raw profile : Real} (hD : 0 <= D)
    (hs0 : 0 < s0) (_hraw : 0 <= raw) (hprofile : 0 <= profile) :
    raw - dimensionOneRosserModelMinusRaw s0 +
        D * (1 - 1 / (2 * s0)) * profile <= raw + D * profile := by
  have hcoeff : 1 - 1 / (2 * s0) <= (1 : Real) := by
    exact sub_le_self _ (by positivity)
  have hDprofile : 0 <= D * profile := mul_nonneg hD hprofile
  have hterm : D * (1 - 1 / (2 * s0)) * profile <= D * profile := by
    calc
      D * (1 - 1 / (2 * s0)) * profile =
          (1 - 1 / (2 * s0)) * (D * profile) := by ring
      _ <= 1 * (D * profile) :=
        mul_le_mul_of_nonneg_right hcoeff hDprofile
      _ = D * profile := by ring
  linarith [dimensionOneRosserModelMinusRaw_nonneg s0]

theorem dimensionOneRosserFullSourceUpperTarget_of_innerAndRawLedger
    (P : Finset Nat) (D : Real) {level z s s0 : Real}
    (hD : 0 <= D) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hInner : ∀ p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) -> (p : Real) < z ->
      lowerRosserFailureSum P (fun q => (q : Real)⁻¹)
          (level / p) p <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusRaw
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserSourceMinusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real))))
    (hledger :
      upperRosserFailureSum P (fun p => (p : Real)⁻¹) level
          (level ^ (1 / s0)) +
          dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
          D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (dimensionOneRosserModelPlusRaw s -
              dimensionOneRosserModelPlusRaw s0 +
            D * (1 - 1 / (2 * s0)) *
              dimensionOneRosserSourcePlusProfile (Real.log level) s)) :
    dimensionOneRosserFullSourceUpperTarget P D level z s := by
  have hratio : (3 : Real) <= Real.log level / Real.log z := by
    rw [← hs]
    exact hsLower
  have hcube : z ^ (3 : Nat) <= level :=
    power_le_of_natCast_le_log_div_log hlevel hz hratio
  have hshell :=
    upperRosserFailureSum_le_cutoff_add_rawSourceShell_of_cube_le_rankZeroFree_tailFree
      P D hprime hlevel hz hs hsLower hss0 hcutoff hcube hInner
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hprofile : 0 <=
      dimensionOneRosserSourcePlusProfile (Real.log level) s := by
    unfold dimensionOneRosserSourcePlusProfile
    exact mul_nonneg (Real.rpow_pos_of_pos hL _).le
      (dimensionOneRosserPlusArtificialAux_pos hL hsPos).le
  have hbracket := dimensionOneRosserReadyBracket_le_upper hD hs0Pos
    (dimensionOneRosserModelPlusRaw_nonneg s) hprofile
  unfold dimensionOneRosserFullSourceUpperTarget
  exact hshell.trans_lt hledger |>.trans_le
    (mul_le_mul_of_nonneg_left hbracket
      (div_nonneg
        (sieveDensityBelow_reciprocal_pos P z hprime).le hsPos.le))

theorem dimensionOneRosserFullSourceLowerTarget_of_innerAndRawLedger
    (P : Finset Nat) (D : Real) {level z s s0 : Real}
    (hD : 0 <= D) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hInner : ∀ p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) -> (p : Real) < z ->
      upperRosserFailureSum P (fun q => (q : Real)⁻¹)
          (level / p) p <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelPlusRaw
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserSourcePlusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real))))
    (hledger :
      lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level
          (level ^ (1 / s0)) +
          dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
          D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (dimensionOneRosserModelMinusRaw s -
              dimensionOneRosserModelMinusRaw s0 +
            D * (1 - 1 / (2 * s0)) *
              dimensionOneRosserSourceMinusProfile (Real.log level) s)) :
    dimensionOneRosserFullSourceLowerTarget P D level z s := by
  have hshell :=
    lowerRosserFailureSum_le_cutoff_add_rawSourceShell_tailFree
      P D hprime hlevel hz hs hsLower hss0 hcutoff hInner
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hprofile : 0 <=
      dimensionOneRosserSourceMinusProfile (Real.log level) s := by
    unfold dimensionOneRosserSourceMinusProfile
    exact mul_nonneg (Real.rpow_pos_of_pos hL _).le
      (dimensionOneRosserMinusArtificialAux_pos hL hsPos).le
  have hbracket := dimensionOneRosserReadyBracket_le_lower hD hs0Pos
    (dimensionOneRosserModelMinusRaw_nonneg s) hprofile
  unfold dimensionOneRosserFullSourceLowerTarget
  exact hshell.trans_lt hledger |>.trans_le
    (mul_le_mul_of_nonneg_left hbracket
      (div_nonneg
        (sieveDensityBelow_reciprocal_pos P z hprime).le hsPos.le))

end PrimesRestrictedDigits
