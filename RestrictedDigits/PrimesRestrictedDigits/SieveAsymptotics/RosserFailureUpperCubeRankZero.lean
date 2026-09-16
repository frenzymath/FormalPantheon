import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullShellRawSourceTail

/-!
# Upper cube-gated rank-zero elimination

On the weak cube branch, the rank-zero difference retained by the complete source shell
vanishes at both cutoffs. This is the finite support specialization of Iwaniec--Rosser
(4.4)--(4.6), pp. 180--181, and the source shell transport in (8.8)--(8.11), pp. 198--200.
-/

namespace PrimesRestrictedDigits

/- The inner cutoff is strictly below the outer cutoff. -/
private theorem upperCubeRankZero_innerCutoff_lt
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) :
    level ^ (1 / s0) < z := by
  exact dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 (by linarith)

/- The weak outer cube bound transfers to the inner cutoff. -/
private theorem upperCubeRankZero_innerCutoff_cube_le
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hcube : z ^ (3 : Nat) <= level) :
    (level ^ (1 / s0)) ^ (3 : Nat) <= level := by
  have hwz := upperCubeRankZero_innerCutoff_lt hlevel hz hs hsLower hss0
  have hw0 : 0 <= level ^ (1 / s0) := by
    linarith
  exact (pow_le_pow_left₀ hw0 hwz.le 3).trans hcube

/-- The upper source shell with its exact rank-zero difference removed on
the weak cube branch.  The complete cutoff, source tail, and raw sums remain
unchanged. -/
theorem upperRosserFailureSum_le_cutoff_add_rawSourceShell_with_tail_of_cube_le_rankZeroFree
    (P : Finset Nat) (D : Real) (tau : Nat -> Real) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hcube : z ^ (3 : Nat) <= level)
    (hInner : forall p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) -> (p : Real) < z ->
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
      upperRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z +
        dimensionOneRosserRawFirstRemainderSum P level s0 z tau := by
  have hraw :=
    upperRosserFailureSum_le_cutoff_add_rawSourceShell_with_tail_of_cube_le
      P D tau hprime hlevel hz hs hsLower hss0 hcutoff hcube hInner
  have hwCube := upperCubeRankZero_innerCutoff_cube_le hlevel hz hs hsLower
    hss0 hcutoff hcube
  have hzZero : upperRosserFailureSumAtRank P
      (fun p => (p : Real)⁻¹) level z 0 = 0 :=
    upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le P
      (fun p => (p : Real)⁻¹) level z 0 hprime hcube
  have hwZero : upperRosserFailureSumAtRank P
      (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) 0 = 0 :=
    upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le P
      (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) 0 hprime hwCube
  rw [hzZero, hwZero, sub_self] at hraw
  simpa only [zero_add, add_zero, add_assoc] using hraw

end PrimesRestrictedDigits
