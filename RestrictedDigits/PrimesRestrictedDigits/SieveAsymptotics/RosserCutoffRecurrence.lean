import PrimesRestrictedDigits.SieveAsymptotics.RosserPowerRecurrence
import PrimesRestrictedDigits.SieveAsymptotics.RosserLogRatio

/-!
# The changing-cutoff Rosser recurrence

This makes explicit the cutoff suppressed in Iwaniec's equation (4.6). The level remains fixed
and the second upper partial sum has cutoff `level^(1/3)`.
-/

namespace PrimesRestrictedDigits

theorem iwaniecBaseCutoff_le_iff_cube_le
    {level x : Real} (hlevel : 0 ≤ level) (hx : 0 ≤ x) :
    iwaniecBaseCutoff level ≤ x ↔ level ≤ x ^ (3 : Nat) := by
  have hcutoff : iwaniecBaseCutoff level = rosserCutoffRoot level 3 := by
    rw [iwaniecBaseCutoff, rosserCutoffRoot]
    norm_num
  rw [hcutoff,
    rosserCutoffRoot_le_iff_pow_le hlevel hx (by norm_num)]

/-- Every positive upper rank has the same correction at `z` and at the
base cutoff, provided the latter is no larger than `z`. -/
theorem upperRosserFailureSumAtRank_succ_eq_baseCutoff
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (r : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 0 ≤ level)
    (hcutoff : iwaniecBaseCutoff level ≤ z) :
    upperRosserFailureSumAtRank P nu level z (r + 1) =
      upperRosserFailureSumAtRank P nu level
        (iwaniecBaseCutoff level) (r + 1) := by
  rw [upperRosserFailureSumAtRank_succ_eq_sum_lower
      P nu level z r hprime,
    upperRosserFailureSumAtRank_succ_eq_sum_lower
      P nu level (iwaniecBaseCutoff level) r hprime]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpP, hpz, hgate⟩
    refine ⟨hpP, ?_, hgate⟩
    apply (lt_iwaniecBaseCutoff_iff_cube_lt (by positivity) hlevel).mpr
    nlinarith
  · rintro ⟨hpP, hpw, hgate⟩
    exact ⟨hpP, hpw.trans_le hcutoff, hgate⟩

/-- The exact finite beta-two meaning of Iwaniec's equation (4.6). -/
theorem upperRosserFailurePartialSum_eq_rankZero_add_baseCutoff
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 0 ≤ level)
    (hcutoff : iwaniecBaseCutoff level ≤ z) :
    upperRosserFailurePartialSum P nu level z R =
      upperRosserFailureSumAtRank P nu level z 0 +
        upperRosserFailurePartialSum P nu level
          (iwaniecBaseCutoff level) R := by
  have hbaseZero : upperRosserFailureSumAtRank P nu level
      (iwaniecBaseCutoff level) 0 = 0 := by
    apply upperRosserFailureSumAtRank_eq_zero_of_cutoffPow_le
      P nu level (iwaniecBaseCutoff level) 0 hprime
    simpa using (iwaniecBaseCutoff_pow_three hlevel).le
  induction R with
  | zero =>
      simp only [upperRosserFailurePartialSum_zero, hbaseZero, add_zero]
  | succ R ih =>
      rw [upperRosserFailurePartialSum_succ, ih,
        upperRosserFailureSumAtRank_succ_eq_baseCutoff
          P nu level z R hprime hlevel hcutoff,
        upperRosserFailurePartialSum_succ]
      ring

/-- The logarithmic upper ratio bound supplies the cutoff comparison in
equation (4.6). -/
theorem upperRosserFailurePartialSum_eq_rankZero_add_baseCutoff_of_logRatio
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 ≤ level) (hz : 2 ≤ z)
    (hratio : Real.log level / Real.log z ≤ (3 : Real)) :
    upperRosserFailurePartialSum P nu level z R =
      upperRosserFailureSumAtRank P nu level z 0 +
        upperRosserFailurePartialSum P nu level
          (iwaniecBaseCutoff level) R := by
  apply upperRosserFailurePartialSum_eq_rankZero_add_baseCutoff
    P nu level z R hprime (by positivity)
  apply (iwaniecBaseCutoff_le_iff_cube_le (by positivity)
    (by positivity)).mpr
  exact le_power_of_log_div_log_le_natCast hlevel hz hratio

/-- Source-facing equation (4.6), retaining the printed ratio variable and
its complete domain. -/
theorem iwaniecRosserEquation_four_six
    (P : Finset Nat) (nu : Nat → Real) (level z s : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 ≤ level) (hz : 2 ≤ z)
    (_hR : 0 < R) (hs : s = Real.log level / Real.log z)
    (_hsLower : 1 < s) (hsUpper : s ≤ 3) :
    upperRosserFailurePartialSum P nu level z R =
      upperRosserFailureSumAtRank P nu level z 0 +
        upperRosserFailurePartialSum P nu level
          (iwaniecBaseCutoff level) R := by
  apply upperRosserFailurePartialSum_eq_rankZero_add_baseCutoff_of_logRatio
    P nu level z R hprime hlevel hz
  simpa only [hs] using hsUpper

end PrimesRestrictedDigits
