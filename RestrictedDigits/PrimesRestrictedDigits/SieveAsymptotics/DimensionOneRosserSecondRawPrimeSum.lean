import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatio
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondWeight
import PrimesRestrictedDigits.SieveAsymptotics.RosserLogRatio

/-!
# Raw second weighted dimension-one Rosser sums

This file isolates the rank-free profile in Iwaniec's second recurrence term and compares its
local artificial factor with the relaxed Eq. (8.11) weight. See `IWANIEC-ROSSER-SIEVE-1980`,
Eqs. (8.8) and (8.11).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The literal second recurrence profile for a plus target. The source pairs
this target with the shifted minus delay function. -/
noncomputable def dimensionOneRosserPlusSecondRawPrimeSum
    (P : Finset Nat) (level s0 z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      (1 + buchstabArgument level (p : Real) ^ 50 /
          Real.log (level / (p : Real))) ^
        buchstabArgument level (p : Real) *
      dimensionOneDelayScaledMinus (buchstabArgument level (p : Real)) *
      (Real.log (level / (p : Real))) ^ (-1 / 3 : Real)

/-- The literal second recurrence profile for a minus target. The source pairs
this target with the shifted plus delay function. -/
noncomputable def dimensionOneRosserMinusSecondRawPrimeSum
    (P : Finset Nat) (level s0 z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) *
      (1 + buchstabArgument level (p : Real) ^ 50 /
          Real.log (level / (p : Real))) ^
        buchstabArgument level (p : Real) *
      dimensionOneDelayScaledPlus (buchstabArgument level (p : Real)) *
      (Real.log (level / (p : Real))) ^ (-1 / 3 : Real)

/-- The plus-target sum after replacing the local artificial factor by the
global Eq. (8.11) weight. -/
noncomputable def dimensionOneRosserPlusSecondRelaxedPrimeSum
    (P : Finset Nat) (level s0 z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (Real.log level) ^ (-1 / 3 : Real) * (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log level) *
      dimensionOneRosserPlusSecondWeight level (p : Real)

/-- The minus-target sum after replacing the local artificial factor by the
global Eq. (8.11) weight. -/
noncomputable def dimensionOneRosserMinusSecondRelaxedPrimeSum
    (P : Finset Nat) (level s0 z : Real) : Real :=
  ∑ p ∈ P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
    (Real.log level) ^ (-1 / 3 : Real) * (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log level) *
      dimensionOneRosserMinusSecondWeight level (p : Real)

private theorem dimensionOneRosserSecondRawSummand_le_relaxed
    (P : Finset Nat) (kernel : Real → Real → Real)
    (scaledDelay : Real → Real)
    (hsource : ∀ {L t : Real}, 0 < L → 1 < t →
      kernel L t =
        (1 - 1 / t) ^ (-4 / 3 : Real) *
          (1 + t ^ 50 / L) ^ (t - 1) * scaledDelay (t - 1))
    (hscaled : ∀ {u : Real}, 0 < u → 0 < scaledDelay u)
    {level x : Real} (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hxOne : 1 < x) (hxLevel : x < level) :
    x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          (1 + buchstabArgument level x ^ 50 /
              Real.log (level / x)) ^ buchstabArgument level x *
          scaledDelay (buchstabArgument level x) *
          (Real.log (level / x)) ^ (-1 / 3 : Real) <=
      (Real.log level) ^ (-1 / 3 : Real) * x⁻¹ *
          sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log level) *
          kernel (Real.log level) (buchstabArgument level x + 1) := by
  let L : Real := Real.log level
  let ell : Real := Real.log (level / x)
  let l : Real := Real.log x
  let u : Real := buchstabArgument level x
  let t : Real := u + 1
  have hlevelPos : 0 < level :=
    (by norm_num : (0 : Real) < 2).trans_le hlevel
  have hxPos : 0 < x := by linarith
  have hL : 0 < L := by
    exact Real.log_pos (by linarith)
  have hl : 0 < l := Real.log_pos hxOne
  have hell : 0 < ell := by
    exact Real.log_pos ((one_lt_div hxPos).2 hxLevel)
  have hellEq : ell = u * l := by
    exact log_div_eq_buchstabArgument_mul_log hlevelPos hxOne
  have hu : 0 < u := by
    have hmul : 0 < u * l := by rwa [← hellEq]
    rcases (mul_pos_iff.mp hmul) with h | h
    · exact h.1
    · linarith [hl, h.2]
  have ht : 1 < t := by dsimp [t]; linarith
  have htEq : t = L / l := by
    dsimp [t, u, L, l, buchstabArgument]
    ring
  have hLEq : L = t * l := by
    rw [htEq]
    field_simp [hl.ne']
  have hbase : 0 < 1 - 1 / t := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact ht
  have hellFactor : ell = L * (1 - 1 / t) := by
    rw [hellEq, hLEq]
    dsimp [t]
    field_simp [show u + 1 ≠ 0 by linarith]
    ring
  have hpow49 : u ^ 49 <= t ^ 49 :=
    pow_le_pow_left₀ hu.le (show u <= t by dsimp [t]; linarith) 49
  have hlocalCancel : u ^ 50 / (u * l) = u ^ 49 / l := by
    rw [show u ^ 50 = u ^ 49 * u by ring]
    field_simp [hu.ne', hl.ne']
  have hglobalCancel : t ^ 50 / (t * l) = t ^ 49 / l := by
    rw [show t ^ 50 = t ^ 49 * t by ring]
    field_simp [show t ≠ 0 by linarith, hl.ne']
  have hratioPow : u ^ 50 / ell <= t ^ 50 / L := by
    rw [hellEq, hLEq, hlocalCancel, hglobalCancel]
    exact (div_le_div_iff_of_pos_right hl).2 hpow49
  have hbasePow :
      (1 + u ^ 50 / ell) ^ u <= (1 + t ^ 50 / L) ^ u := by
    have hlocalBase : 0 <= 1 + u ^ 50 / ell := by positivity
    exact Real.rpow_le_rpow hlocalBase (by linarith [hratioPow]) hu.le
  have hprofile :
      (1 + u ^ 50 / ell) ^ u * scaledDelay u <=
        (1 + t ^ 50 / L) ^ u * scaledDelay u :=
    mul_le_mul_of_nonneg_right hbasePow (hscaled hu).le
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) x :=
    sieveDensityBelow_reciprocal_pos P x hprime
  have hprefix :
      0 <= x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
        (l / ell) := by positivity
  have hellPow : 0 < ell ^ (-1 / 3 : Real) :=
    Real.rpow_pos_of_pos hell _
  have hweak :
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (l / ell) * (1 + u ^ 50 / ell) ^ u * scaledDelay u *
            ell ^ (-1 / 3 : Real) <=
        x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (l / ell) * ((1 + t ^ 50 / L) ^ u * scaledDelay u) *
            ell ^ (-1 / 3 : Real) := by
    calc
      _ = (x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (l / ell)) * ((1 + u ^ 50 / ell) ^ u * scaledDelay u) *
            ell ^ (-1 / 3 : Real) := by ring
      _ <= (x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (l / ell)) * ((1 + t ^ 50 / L) ^ u * scaledDelay u) *
            ell ^ (-1 / 3 : Real) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprofile hprefix) hellPow.le
      _ = _ := by ring
  have hpowNormalize :
      (1 - 1 / t) ^ (-1 / 3 : Real) =
        (1 - 1 / t) * (1 - 1 / t) ^ (-4 / 3 : Real) := by
    calc
      (1 - 1 / t) ^ (-1 / 3 : Real) =
          (1 - 1 / t) ^ ((1 : Real) + (-4 / 3 : Real)) := by
        congr 1
        norm_num
      _ = (1 - 1 / t) ^ (1 : Real) *
          (1 - 1 / t) ^ (-4 / 3 : Real) :=
        Real.rpow_add hbase 1 (-4 / 3 : Real)
      _ = (1 - 1 / t) *
          (1 - 1 / t) ^ (-4 / 3 : Real) := by
        rw [Real.rpow_one]
  have hscalar :
      l / ell * ell ^ (-1 / 3 : Real) =
        l / L * (1 - 1 / t) ^ (-4 / 3 : Real) *
          L ^ (-1 / 3 : Real) := by
    rw [hellFactor, Real.mul_rpow hL.le hbase.le, hpowNormalize]
    field_simp [hL.ne', hbase.ne', show t ≠ 0 by linarith]
    exact mul_div_cancel_left₀ _ (show t - 1 ≠ 0 by linarith)
  have hweight : kernel L t =
      (1 - 1 / t) ^ (-4 / 3 : Real) *
        (1 + t ^ 50 / L) ^ u * scaledDelay u := by
    rw [hsource hL ht]
    have hshift : t - 1 = u := by dsimp [t]; ring
    rw [hshift]
  have hglobalEq :
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (l / ell) * ((1 + t ^ 50 / L) ^ u * scaledDelay u) *
            ell ^ (-1 / 3 : Real) =
        L ^ (-1 / 3 : Real) * x⁻¹ *
            sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (l / L) * kernel L t := by
    rw [hweight]
    calc
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (l / ell) * ((1 + t ^ 50 / L) ^ u * scaledDelay u) *
            ell ^ (-1 / 3 : Real) =
          x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (l / ell * ell ^ (-1 / 3 : Real)) *
            ((1 + t ^ 50 / L) ^ u * scaledDelay u) := by ring
      _ = _ := by rw [hscalar]; ring
  change x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
      (l / ell) * (1 + u ^ 50 / ell) ^ u * scaledDelay u *
      ell ^ (-1 / 3 : Real) <= _
  exact hweak.trans_eq hglobalEq

/-- In the restricted large-`s` regime the printed `2*p<level` condition in
Iwaniec's Eq. (8.8) follows from the retained upper carrier `p<z`. -/
theorem dimensionOneRosser_two_mul_lt_level_of_lt_upper_of_large_s
    {level z s : Real} {p : Nat} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hpTwo : 2 <= (p : Real)) (hpz : (p : Real) < z) :
    2 * (p : Real) < level := by
  have hsTwo : (2 : Real) <= Real.log level / Real.log z := by
    rw [← hs]
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hzSq : z ^ 2 <= level :=
    power_le_of_natCast_le_log_div_log hlevel hz hsTwo
  have hpSq : (p : Real) ^ 2 < z ^ 2 :=
    pow_lt_pow_left₀ hpz (by linarith) (by norm_num)
  have htwice : 2 * (p : Real) <= (p : Real) ^ 2 := by nlinarith
  exact htwice.trans_lt (hpSq.trans_le hzSq)

/-- The literal plus-target second profile is bounded by its relaxed Eq.
(8.11) sum on the natural second-recurrence domain. -/
theorem dimensionOneRosserPlusSecondRawPrimeSum_le_relaxed_of_two_le
    (P : Finset Nat) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsTwo : 2 <= s)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <=
      dimensionOneRosserPlusSecondRelaxedPrimeSum P level s0 z := by
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsOne : 1 < s := by linarith
  have hlogIdentity : Real.log level = s * Real.log z := by
    rw [hs]
    field_simp [hlogz.ne']
  have hzLevel : z < level := by
    apply (Real.log_lt_log_iff (by linarith) (by linarith)).mp
    rw [hlogIdentity]
    nlinarith
  unfold dimensionOneRosserPlusSecondRawPrimeSum
    dimensionOneRosserPlusSecondRelaxedPrimeSum
    dimensionOneRosserPlusSecondWeight
  apply Finset.sum_le_sum
  intro p hp
  have hpBounds := Finset.mem_filter.mp hp
  have hpOne : 1 < (p : Real) := by
    linarith [hcutoff.trans hpBounds.2.1]
  exact dimensionOneRosserSecondRawSummand_le_relaxed P
    dimensionOneRosserPlusSecondKernel dimensionOneDelayScaledMinus
    dimensionOneRosserPlusSecondKernel_eq_source
    (fun hu => by
      rw [← sq_mul_dimensionOneDelayQMinus hu.ne']
      exact mul_pos (sq_pos_of_pos hu) (dimensionOneDelayQMinus_pos hu))
    hprime hlevel hpOne (hpBounds.2.2.trans hzLevel)

/-- Large-domain compatibility form of the plus raw-to-relaxed comparison. -/
theorem dimensionOneRosserPlusSecondRawPrimeSum_le_relaxed
    (P : Finset Nat) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <=
      dimensionOneRosserPlusSecondRelaxedPrimeSum P level s0 z := by
  apply dimensionOneRosserPlusSecondRawPrimeSum_le_relaxed_of_two_le P
    hprime hlevel hz hs _ hcutoff
  have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
  linarith

/-- The literal minus-target second profile is bounded by its relaxed Eq.
(8.11) sum on the natural second-recurrence domain. -/
theorem dimensionOneRosserMinusSecondRawPrimeSum_le_relaxed_of_two_le
    (P : Finset Nat) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsTwo : 2 <= s)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <=
      dimensionOneRosserMinusSecondRelaxedPrimeSum P level s0 z := by
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsOne : 1 < s := by linarith
  have hlogIdentity : Real.log level = s * Real.log z := by
    rw [hs]
    field_simp [hlogz.ne']
  have hzLevel : z < level := by
    apply (Real.log_lt_log_iff (by linarith) (by linarith)).mp
    rw [hlogIdentity]
    nlinarith
  unfold dimensionOneRosserMinusSecondRawPrimeSum
    dimensionOneRosserMinusSecondRelaxedPrimeSum
    dimensionOneRosserMinusSecondWeight
  apply Finset.sum_le_sum
  intro p hp
  have hpBounds := Finset.mem_filter.mp hp
  have hpOne : 1 < (p : Real) := by
    linarith [hcutoff.trans hpBounds.2.1]
  exact dimensionOneRosserSecondRawSummand_le_relaxed P
    dimensionOneRosserMinusSecondKernel dimensionOneDelayScaledPlus
    dimensionOneRosserMinusSecondKernel_eq_source
    (fun hu => by
      rw [← sq_mul_dimensionOneDelayQPlus hu.ne']
      exact mul_pos (sq_pos_of_pos hu) (dimensionOneDelayQPlus_pos hu))
    hprime hlevel hpOne (hpBounds.2.2.trans hzLevel)

/-- Large-domain compatibility form of the minus raw-to-relaxed comparison. -/
theorem dimensionOneRosserMinusSecondRawPrimeSum_le_relaxed
    (P : Finset Nat) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hcutoff : 2 <= level ^ (1 / s0)) :
    dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <=
      dimensionOneRosserMinusSecondRelaxedPrimeSum P level s0 z := by
  apply dimensionOneRosserMinusSecondRawPrimeSum_le_relaxed_of_two_le P
    hprime hlevel hz hs _ hcutoff
  have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
  linarith

end PrimesRestrictedDigits
