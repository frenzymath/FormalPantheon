import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullShellRawSourceTail
import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullBaseCutoff
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArithmeticBase

/-!
# Low-base complete source shell

This combines the cubic-root split and the complete source shell at the base ratio `s=3`. The outer
rank-zero layer, complete cutoff, and signed tail remain explicit. Source comparison:
Iwaniec--Rosser Eq. (4.6), pp. 180--181, and Eqs. (8.8)--(8.11), pp. 198--200.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The strict low-coordinate upper shell reduces to the exact base shell. -/
theorem upperRosserFailureSum_le_rankZero_add_baseRawSourceShell_with_tail
    (P : Finset Nat) (D : Real) (tau : Nat → Real) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 8 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (_hsOne : 1 < s) (hsUpper : s < 3) (hs0 : 3 < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hInner : ∀ p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) ->
      (p : Real) < iwaniecBaseCutoff level ->
      lowerRosserFailureSum P (fun q => (q : Real)⁻¹)
          (level / p) p <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusRaw
              (buchstabArgument level (p : Real)) +
            (D * dimensionOneRosserSourceMinusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)) + tau p))) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹) level z 0 +
        upperRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
        dimensionOneRosserPlusRawFirstPrimeSum P level s0
          (iwaniecBaseCutoff level) +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0
          (iwaniecBaseCutoff level) +
        dimensionOneRosserRawFirstRemainderSum P level
            s0 (iwaniecBaseCutoff level) tau := by
  have hlevelTwo : (2 : Real) <= level := by linarith
  have hlevelPos : 0 < level := by linarith
  have hbase : 2 <= iwaniecBaseCutoff level :=
    two_le_iwaniecBaseCutoff_of_eight_le hlevel
  have hbasePos : 0 < iwaniecBaseCutoff level := by linarith
  have hbaseLe : iwaniecBaseCutoff level <= z := by
    apply (iwaniecBaseCutoff_le_iff_cube_le (by linarith) (by linarith)).mpr
    apply le_power_of_log_div_log_le_natCast hlevelTwo hz
    have hratio : Real.log level / Real.log z < 3 := by
      simpa [hs] using hsUpper
    exact hratio.le
  have hbaseCube : iwaniecBaseCutoff level ^ (3 : Nat) <= level := by
    simpa using (iwaniecBaseCutoff_pow_three (by linarith)).le
  have hbaseCoord : 3 =
      Real.log level / Real.log (iwaniecBaseCutoff level) := by
    rw [log_iwaniecBaseCutoff hlevelPos]
    have hlogLevel : Real.log level ≠ 0 :=
      (Real.log_pos (by linarith)).ne'
    field_simp [hlogLevel]
  have hcutCube : (level ^ (1 / s0)) ^ (3 : Nat) <= level := by
    have hlevelOne : (1 : Real) <= level := by linarith
    have hs0Pos : 0 < s0 := by linarith
    have hexp : (1 / s0 : Real) * 3 <= 1 := by
      rw [show (1 / s0 : Real) * 3 = 3 / s0 by ring]
      apply (div_le_iff₀ hs0Pos).2
      nlinarith
    calc
      (level ^ (1 / s0)) ^ (3 : Nat) =
          level ^ ((1 / s0 : Real) * (3 : Real)) :=
        (Real.rpow_mul_natCast (by linarith) (1 / s0 : Real) 3).symm
      _ <= level ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hlevelOne hexp
      _ = level := by simp
  have hbaseZero : upperRosserFailureSumAtRank P
      (fun p => (p : Real)⁻¹) level (iwaniecBaseCutoff level) 0 = 0 :=
    upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le P
      (fun p => (p : Real)⁻¹) level (iwaniecBaseCutoff level) 0 hprime hbaseCube
  have hwZero : upperRosserFailureSumAtRank P
      (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) 0 = 0 :=
    upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le P
      (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) 0 hprime hcutCube
  have hbaseShell :=
    upperRosserFailureSum_le_cutoff_add_rawSourceShell_with_tail_of_cube_le
      P D tau hprime hlevelTwo hbase hbaseCoord (by norm_num) hs0 hcutoff
      hbaseCube hInner
  have hbaseShell' : upperRosserFailureSum P
      (fun p => (p : Real)⁻¹) level (iwaniecBaseCutoff level) <=
      upperRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        dimensionOneRosserPlusRawFirstPrimeSum P level s0
          (iwaniecBaseCutoff level) +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0
          (iwaniecBaseCutoff level) +
        dimensionOneRosserRawFirstRemainderSum P level
            s0 (iwaniecBaseCutoff level) tau := by
    simpa only [hbaseZero, hwZero, sub_self, zero_add, add_zero,
      add_assoc] using hbaseShell
  have hsplit := upperRosserFailureSum_eq_rankZero_add_baseCutoff
    P (fun p => (p : Real)⁻¹) level z hprime (by linarith) hbaseLe
  calc
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z =
        upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹) level z 0 +
          upperRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (iwaniecBaseCutoff level) := hsplit
    _ <= upperRosserFailureSumAtRank P
          (fun p => (p : Real)⁻¹) level z 0 +
        (upperRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
          dimensionOneRosserPlusRawFirstPrimeSum P level s0
            (iwaniecBaseCutoff level) +
          D * dimensionOneRosserPlusSecondRawPrimeSum P level s0
            (iwaniecBaseCutoff level) +
          dimensionOneRosserRawFirstRemainderSum P level
            s0 (iwaniecBaseCutoff level) tau) :=
      by linarith [hbaseShell']
    _ = _ := by ring

end PrimesRestrictedDigits
