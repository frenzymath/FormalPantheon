import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullRecurrenceShell
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserRawFirstWeightedSum

/-!
# Raw-profile adapter for complete Rosser shells

This module conditionally transports full inner correction bounds through the exact half-open
shell recurrences. It retains the cutoff terms, the upper rank-zero difference, and an
explicit signed remainder shell.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The signed first-shell remainder left after extracting a raw model
profile from a complete inner correction bound. -/
noncomputable def dimensionOneRosserRawFirstRemainderSum
    (P : Finset Nat) (level s0 z : Real) (e : Nat → Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) * e p

private theorem raw_shell_outer_lt_level
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

private theorem raw_shell_buchstabArgument_inv_eq_log_ratio
    {level x : Real} (hlevel : 0 < level) (hx : 1 < x)
    (hxLevel : x < level) :
    (buchstabArgument level x)⁻¹ =
      Real.log x / Real.log (level / x) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogDiv : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  rw [<- log_div_log_eq_buchstabArgument hlevel hx]
  field_simp [hlogx.ne', hlogDiv.ne']

private theorem raw_shell_summand_eq
    (P : Finset Nat) {level x model error : Real}
    (hlevel : 0 < level) (hx : 1 < x) (hxLevel : x < level) :
    x⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x * (model + error)) =
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) * model +
        x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) * error := by
  have hcoord :
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x =
        sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) := by
    rw [div_eq_mul_inv,
      raw_shell_buchstabArgument_inv_eq_log_ratio hlevel hx hxLevel]
  rw [hcoord]
  ring

/-- A complete lower shell inherits a supplied raw upper-profile inner bound.
The cutoff correction and signed remainder shell remain explicit. -/
theorem lowerRosserFailureSum_le_cutoff_add_rawFirstShell
    (P : Finset Nat) (e : Nat → Real) {level z s s0 : Real}
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
              (buchstabArgument level (p : Real)) + e p)) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
        dimensionOneRosserRawFirstRemainderSum P level s0 z e := by
  have hzLevel := raw_shell_outer_lt_level hlevel hz hs hsLower
  have hsum :
      (∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
        (p : Real)⁻¹ * upperRosserFailureSum P
          (fun q => (q : Real)⁻¹) (level / p) p) <=
      dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
        dimensionOneRosserRawFirstRemainderSum P level s0 z e := by
    calc
      _ <= ∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          ((p : Real)⁻¹ *
              sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
              (Real.log (p : Real) / Real.log (level / (p : Real))) *
              dimensionOneRosserModelPlusRaw
                (buchstabArgument level (p : Real)) +
            (p : Real)⁻¹ *
              sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
              (Real.log (p : Real) / Real.log (level / (p : Real))) * e p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpData := Finset.mem_filter.mp hp
        have hpTwo : (2 : Real) <= p := hcutoff.trans hpData.2.1
        have hpRecip : (0 : Real) <= (p : Real)⁻¹ := by positivity
        have hinner := hInner p hpData.1 hpData.2.1 hpData.2.2
        have hmul := mul_le_mul_of_nonneg_left hinner hpRecip
        exact hmul.trans_eq <| raw_shell_summand_eq P
          (model := dimensionOneRosserModelPlusRaw
            (buchstabArgument level (p : Real)))
          (error := e p) (by linarith) (by linarith)
          (hpData.2.2.trans hzLevel)
      _ = _ := by
        unfold dimensionOneRosserMinusRawFirstPrimeSum
          dimensionOneRosserRawFirstRemainderSum
        rw [Finset.sum_add_distrib]
  have hwz : level ^ (1 / s0) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsLower).le
  calc
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z =
        lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
          ∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
            (p : Real)⁻¹ * upperRosserFailureSum P
              (fun q => (q : Real)⁻¹) (level / p) p :=
      lowerRosserFailureSum_eq_cutoff_add_sum_upper_full
        P (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) z
        hprime hwz
    _ <= _ := by
      simpa only [add_assoc] using add_le_add_right hsum
        (lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)))

/-- Under a weak cube cutoff, a complete upper shell inherits a supplied raw
lower-profile inner bound. The exact rank-zero difference is retained. -/
theorem upperRosserFailureSum_le_cutoff_add_rawFirstShell_of_cube_le
    (P : Finset Nat) (e : Nat → Real) {level z s s0 : Real}
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
              (buchstabArgument level (p : Real)) + e p)) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      upperRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        (upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level z 0 -
          upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) 0) +
        dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
        dimensionOneRosserRawFirstRemainderSum P level s0 z e := by
  have hzLevel := raw_shell_outer_lt_level hlevel hz hs (by linarith)
  have hsum :
      (∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
        (p : Real)⁻¹ * lowerRosserFailureSum P
          (fun q => (q : Real)⁻¹) (level / p) p) <=
      dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
        dimensionOneRosserRawFirstRemainderSum P level s0 z e := by
    calc
      _ <= ∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          ((p : Real)⁻¹ *
              sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
              (Real.log (p : Real) / Real.log (level / (p : Real))) *
              dimensionOneRosserModelMinusRaw
                (buchstabArgument level (p : Real)) +
            (p : Real)⁻¹ *
              sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
              (Real.log (p : Real) / Real.log (level / (p : Real))) * e p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpData := Finset.mem_filter.mp hp
        have hpTwo : (2 : Real) <= p := hcutoff.trans hpData.2.1
        have hpRecip : (0 : Real) <= (p : Real)⁻¹ := by positivity
        have hinner := hInner p hpData.1 hpData.2.1 hpData.2.2
        have hmul := mul_le_mul_of_nonneg_left hinner hpRecip
        exact hmul.trans_eq <| raw_shell_summand_eq P
          (model := dimensionOneRosserModelMinusRaw
            (buchstabArgument level (p : Real)))
          (error := e p) (by linarith) (by linarith)
          (hpData.2.2.trans hzLevel)
      _ = _ := by
        unfold dimensionOneRosserPlusRawFirstPrimeSum
          dimensionOneRosserRawFirstRemainderSum
        rw [Finset.sum_add_distrib]
  have hwz : level ^ (1 / s0) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0
      (by linarith)).le
  have hw0 : 0 <= level ^ (1 / s0) :=
    (Real.rpow_pos_of_pos (by linarith) _).le
  calc
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z =
        upperRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
          (upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
              level z 0 -
            upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
              level (level ^ (1 / s0)) 0) +
          ∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
            (p : Real)⁻¹ * lowerRosserFailureSum P
              (fun q => (q : Real)⁻¹) (level / p) p :=
      upperRosserFailureSum_eq_cutoff_add_sum_lower_full_of_cube_le
        P (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) z
        hprime hw0 hwz hcube
    _ <= _ := by
      simpa only [add_assoc] using add_le_add_right hsum
        (upperRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
          (upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
              level z 0 -
            upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
              level (level ^ (1 / s0)) 0))

end PrimesRestrictedDigits
