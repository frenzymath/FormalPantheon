import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullShellRawAdapter
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceProfileShell

/-!
# Source-profile specialization of the complete raw shell

This specializes the explicit signed remainder to the source artificial profiles from Eqs.
(8.8)--(8.11). It leaves all full cutoff and rank-zero terms untouched.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem source_raw_shell_outer_lt_level
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s) :
    z < level := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogIdentity : s * Real.log z = Real.log level :=
    (eq_div_iff hlogz.ne').mp hs
  apply (Real.log_lt_log_iff hzPos hlevelPos).mp
  nlinarith

private theorem source_raw_shell_log_pos
    {level z s s0 x : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hx : level ^ (1 / s0) <= x) (hxz : x < z) :
    0 < Real.log (level / x) := by
  have hzLevel := source_raw_shell_outer_lt_level hlevel hz hs hsLower
  have hxTwo : (2 : Real) <= x := hcutoff.trans hx
  exact Real.log_pos ((one_lt_div (by linarith)).2
    (hxz.trans hzLevel))

/-- The lower-shell source-plus remainder is exactly the scaled minus-target
second raw prime sum. -/
theorem dimensionOneRosserRawFirstRemainderSum_sourcePlus_eq
    (P : Finset Nat) {D level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    dimensionOneRosserRawFirstRemainderSum P level s0 z
        (fun p => D * dimensionOneRosserSourcePlusProfile
          (Real.log (level / (p : Real)))
          (buchstabArgument level (p : Real))) =
      D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z := by
  have hzLevel := source_raw_shell_outer_lt_level hlevel hz hs hsLower
  unfold dimensionOneRosserRawFirstRemainderSum
    dimensionOneRosserMinusSecondRawPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpTwo : (2 : Real) <= p := hcutoff.trans hpData.2.1
  have hpOne : (1 : Real) < p := by linarith
  have hpLevel : (p : Real) < level := hpData.2.2.trans hzLevel
  have hL := source_raw_shell_log_pos hlevel hz hs hsLower hcutoff
    hpData.2.1 hpData.2.2
  dsimp
  unfold dimensionOneRosserSourcePlusProfile
    dimensionOneRosserPlusArtificialAux
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  norm_num
  ring

/-- The upper-shell source-minus remainder is exactly the scaled plus-target
second raw prime sum. -/
theorem dimensionOneRosserRawFirstRemainderSum_sourceMinus_eq
    (P : Finset Nat) {D level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    dimensionOneRosserRawFirstRemainderSum P level s0 z
        (fun p => D * dimensionOneRosserSourceMinusProfile
          (Real.log (level / (p : Real)))
          (buchstabArgument level (p : Real))) =
      D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z := by
  have hzLevel := source_raw_shell_outer_lt_level hlevel hz hs hsLower
  unfold dimensionOneRosserRawFirstRemainderSum
    dimensionOneRosserPlusSecondRawPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpTwo : (2 : Real) <= p := hcutoff.trans hpData.2.1
  have hpOne : (1 : Real) < p := by linarith
  have hpLevel : (p : Real) < level := hpData.2.2.trans hzLevel
  have hL := source_raw_shell_log_pos hlevel hz hs hsLower hcutoff
    hpData.2.1 hpData.2.2
  dsimp
  unfold dimensionOneRosserSourceMinusProfile
    dimensionOneRosserMinusArtificialAux
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  norm_num
  ring

/-- Source-profile form of the conditional lower complete-shell transport. -/
theorem lowerRosserFailureSum_le_cutoff_add_rawSourceShell
    (P : Finset Nat) (D : Real) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime)
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
              (buchstabArgument level (p : Real)))) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z := by
  have hraw := lowerRosserFailureSum_le_cutoff_add_rawFirstShell P
    (fun p => D * dimensionOneRosserSourcePlusProfile
      (Real.log (level / (p : Real)))
      (buchstabArgument level (p : Real))) hprime hlevel hz hs hsLower
      hss0 hcutoff hInner
  calc
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
          dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
          dimensionOneRosserRawFirstRemainderSum P level s0 z
            (fun p => D * dimensionOneRosserSourcePlusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real))) := hraw
    _ = _ := by
      rw [dimensionOneRosserRawFirstRemainderSum_sourcePlus_eq
        P hlevel hz hs hsLower hcutoff]

/-- Source-profile form of the conditional upper weak-cube shell transport. -/
theorem upperRosserFailureSum_le_cutoff_add_rawSourceShell_of_cube_le
    (P : Finset Nat) (D : Real) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hcube : z ^ 3 <= level)
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
              (buchstabArgument level (p : Real)))) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      upperRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        (upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level z 0 -
          upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) 0) +
        dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z := by
  have hraw := upperRosserFailureSum_le_cutoff_add_rawFirstShell_of_cube_le
    P (fun p => D * dimensionOneRosserSourceMinusProfile
      (Real.log (level / (p : Real)))
      (buchstabArgument level (p : Real))) hprime hlevel hz hs hsLower
      hss0 hcutoff hcube hInner
  calc
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        upperRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
          (upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
              level z 0 -
            upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
              level (level ^ (1 / s0)) 0) +
          dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
          dimensionOneRosserRawFirstRemainderSum P level s0 z
            (fun p => D * dimensionOneRosserSourceMinusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real))) := hraw
    _ = _ := by
      rw [dimensionOneRosserRawFirstRemainderSum_sourceMinus_eq
        P hlevel hz hs (by linarith) hcutoff]

end PrimesRestrictedDigits
