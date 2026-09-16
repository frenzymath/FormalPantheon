import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArtificialFactor
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFirstWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondRawPrimeSum
import PrimesRestrictedDigits.SieveAsymptotics.RosserCutoffSplit

/-!
# Source-normalized seed-free Rosser profile shell

This module replays the finite cutoff recurrence with the source-normalized profile from
Iwaniec's Eq. (8.8). The independent seed is represented by the distant boundary and is
therefore intentionally absent from the shell sums.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The source-normalized plus profile at a positive logarithmic level. -/
noncomputable def dimensionOneRosserSourcePlusProfile (L t : Real) : Real :=
  L ^ (-1 / 3 : Real) * dimensionOneRosserPlusArtificialAux L 0 t

/-- The source-normalized minus profile at a positive logarithmic level. -/
noncomputable def dimensionOneRosserSourceMinusProfile (L t : Real) : Real :=
  L ^ (-1 / 3 : Real) * dimensionOneRosserMinusArtificialAux L 0 t

private theorem sourceProfile_buchstabArgument_inv_eq_log_ratio
    {level x : Real} (hlevel : 0 < level) (hx : 1 < x)
    (hxLevel : x < level) :
    (buchstabArgument level x)⁻¹ =
      Real.log x / Real.log (level / x) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogDiv : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  rw [<- log_div_log_eq_buchstabArgument hlevel hx]
  field_simp [hlogx.ne', hlogDiv.ne']

/-- The seed-free plus shell summand expands into the first and raw-second
prime-sum summands.  The inner sign is minus, as in Eq. (8.8). -/
theorem dimensionOneRosserSourcePlusProfileSummand_eq
    (P : Finset Nat) (R : Nat) {D level x : Real}
    (hlevel : 0 < level) (hx : 1 < x) (hxLevel : x < level) :
    x⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x *
          (dimensionOneRosserModelMinusPartialSum R
              (buchstabArgument level x) +
            D * dimensionOneRosserSourceMinusProfile
              (Real.log (level / x)) (buchstabArgument level x))) =
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          dimensionOneRosserModelMinusPartialSum R
            (buchstabArgument level x) +
        D * (x⁻¹ * sieveDensityBelow P
            (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          (1 + buchstabArgument level x ^ 50 /
            Real.log (level / x)) ^ buchstabArgument level x *
          dimensionOneDelayScaledMinus (buchstabArgument level x) *
          (Real.log (level / x)) ^ (-1 / 3 : Real)) := by
  have hL : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  have hVcoord :
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x =
        sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) := by
    rw [div_eq_mul_inv,
      sourceProfile_buchstabArgument_inv_eq_log_ratio hlevel hx hxLevel]
  rw [hVcoord]
  unfold dimensionOneRosserSourceMinusProfile
    dimensionOneRosserMinusArtificialAux
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  norm_num
  ring

/-- The seed-free minus shell summand expands into the first and raw-second
prime-sum summands.  The inner sign is plus, as in Eq. (8.8). -/
theorem dimensionOneRosserSourceMinusProfileSummand_eq
    (P : Finset Nat) (R : Nat) {D level x : Real}
    (hlevel : 0 < level) (hx : 1 < x) (hxLevel : x < level) :
    x⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x *
          (dimensionOneRosserModelPlusPartialSum R
              (buchstabArgument level x) +
            D * dimensionOneRosserSourcePlusProfile
              (Real.log (level / x)) (buchstabArgument level x))) =
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          dimensionOneRosserModelPlusPartialSum R
            (buchstabArgument level x) +
        D * (x⁻¹ * sieveDensityBelow P
            (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          (1 + buchstabArgument level x ^ 50 /
            Real.log (level / x)) ^ buchstabArgument level x *
          dimensionOneDelayScaledPlus (buchstabArgument level x) *
          (Real.log (level / x)) ^ (-1 / 3 : Real)) := by
  have hL : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  have hVcoord :
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x =
        sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) := by
    rw [div_eq_mul_inv,
      sourceProfile_buchstabArgument_inv_eq_log_ratio hlevel hx hxLevel]
  rw [hVcoord]
  unfold dimensionOneRosserSourcePlusProfile
    dimensionOneRosserPlusArtificialAux
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  norm_num
  ring

private theorem sourceProfile_outer_lt_level
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s) :
    z < level := by
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogIdentity : s * Real.log z = Real.log level :=
    (eq_div_iff hlogz.ne').mp hs
  apply (Real.log_lt_log_iff (by linarith) (by linarith)).mp
  nlinarith

/-- The upper source-normalized shell has no independent seed-prime sum. -/
theorem dimensionOneRosserUpperFailure_le_sourceProfilePrimeCosts
    (P : Finset Nat) (R : Nat) {D level z s s0 : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hInner : forall p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) -> (p : Real) < z ->
      lowerRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserSourceMinusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)))) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R <=
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z := by
  let first := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      dimensionOneRosserModelMinusPartialSum R (buchstabArgument level p)
  let raw := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      (1 + buchstabArgument level p ^ 50 / Real.log (level / p)) ^
        buchstabArgument level p *
      dimensionOneDelayScaledMinus (buchstabArgument level p) *
      (Real.log (level / p)) ^ (-1 / 3 : Real)
  have hzLevel := sourceProfile_outer_lt_level hlevel hz hs
    (by linarith : 2 <= s)
  have hsum :
      (∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
        (p : Real)⁻¹ * lowerRosserFailurePartialSum P
          (fun q => (q : Real)⁻¹) (level / p) p R) <=
      dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z := by
    calc
      _ <= ∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          (first p + D * raw p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpData := Finset.mem_filter.mp hp
        have hpTwo : (2 : Real) <= p := hcutoff.trans hpData.2.1
        have hpPos : (0 : Real) <= (p : Real)⁻¹ := by positivity
        have hinner := hInner p hpData.1 hpData.2.1 hpData.2.2
        have hmul := mul_le_mul_of_nonneg_left hinner hpPos
        exact hmul.trans_eq <| by
          simpa only [first, raw] using
            (dimensionOneRosserSourcePlusProfileSummand_eq P R
              (D := D) (level := level) (x := p) (by linarith)
              (by linarith) (hpData.2.2.trans hzLevel))
      _ = _ := by
        unfold dimensionOneRosserPlusFirstPrimeSum
          dimensionOneRosserPlusSecondRawPrimeSum
        simp_rw [Finset.sum_add_distrib]
        rw [<- Finset.mul_sum]
  have hratio : (3 : Real) <= Real.log level / Real.log z := by
    rw [<- hs]
    exact hsLower
  have hcube : z ^ 3 <= level :=
    power_le_of_natCast_le_log_div_log hlevel hz hratio
  have hwz : level ^ (1 / s0) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0
      (by linarith : 2 <= s)).le
  have hw0 : 0 <= level ^ (1 / s0) :=
    (Real.rpow_pos_of_pos (by linarith) _).le
  calc
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R =
        upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          ∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
            (p : Real)⁻¹ * lowerRosserFailurePartialSum P
              (fun q => (q : Real)⁻¹) (level / p) p R :=
      upperRosserFailurePartialSum_eq_cutoff_add_sum_lower_of_cube_le
        P (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) z R
        hprime hw0 hwz hcube
    _ <= _ := by
      simpa only [add_assoc] using add_le_add_right hsum
        (upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R)

/-- The lower source-normalized successor shell has no independent seed-prime
sum. -/
theorem dimensionOneRosserLowerFailure_le_sourceProfilePrimeCosts
    (P : Finset Nat) (R : Nat) {D level z s s0 : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hInner : forall p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) -> (p : Real) < z ->
      upperRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelPlusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserSourcePlusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)))) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
        level z (R + 1) <=
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) (R + 1) +
        dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z := by
  let first := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      dimensionOneRosserModelPlusPartialSum R (buchstabArgument level p)
  let raw := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      (1 + buchstabArgument level p ^ 50 / Real.log (level / p)) ^
        buchstabArgument level p *
      dimensionOneDelayScaledPlus (buchstabArgument level p) *
      (Real.log (level / p)) ^ (-1 / 3 : Real)
  have hzLevel := sourceProfile_outer_lt_level hlevel hz hs hsLower
  have hsum :
      (∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
        (p : Real)⁻¹ * upperRosserFailurePartialSum P
          (fun q => (q : Real)⁻¹) (level / p) p R) <=
      dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z := by
    calc
      _ <= ∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
          (first p + D * raw p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpData := Finset.mem_filter.mp hp
        have hpTwo : (2 : Real) <= p := hcutoff.trans hpData.2.1
        have hpPos : (0 : Real) <= (p : Real)⁻¹ := by positivity
        have hinner := hInner p hpData.1 hpData.2.1 hpData.2.2
        have hmul := mul_le_mul_of_nonneg_left hinner hpPos
        exact hmul.trans_eq <| by
          simpa only [first, raw] using
            (dimensionOneRosserSourceMinusProfileSummand_eq P R
              (D := D) (level := level) (x := p) (by linarith)
              (by linarith) (hpData.2.2.trans hzLevel))
      _ = _ := by
        unfold dimensionOneRosserMinusFirstPrimeSum
          dimensionOneRosserMinusSecondRawPrimeSum
        simp_rw [Finset.sum_add_distrib]
        rw [<- Finset.mul_sum]
  have hwz : level ^ (1 / s0) <= z :=
    (dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsLower).le
  calc
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level z (R + 1) =
        lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) (R + 1) +
          ∑ p ∈ P.filter (fun p : Nat =>
            level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
            (p : Real)⁻¹ * upperRosserFailurePartialSum P
              (fun q => (q : Real)⁻¹) (level / p) p R :=
      lowerRosserFailurePartialSum_succ_eq_cutoff_add_sum_upper
        P (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) z R
        hprime hwz
    _ <= _ := by
      simpa only [add_assoc] using add_le_add_right hsum
        (lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) (R + 1))

end PrimesRestrictedDigits
