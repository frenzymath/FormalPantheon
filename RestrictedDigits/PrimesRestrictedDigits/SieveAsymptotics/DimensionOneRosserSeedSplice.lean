import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatioPair
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedProfileScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedPrimeSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserInnerRange
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserUnscaledDelayPrimeSum

/-!
# Splitting the independent Rosser seed at the bounded splice

This file partitions the literal finite seed carrier at the fixed cutoff and compares its
outer part with the appropriate bounded delay profile. The endpoint case is kept explicit
because the strict-shell transport theorems do not apply there.
-/

open Finset Set
open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The seed-prime carrier is the disjoint union of its distant and bounded
fixed-splice pieces. -/
theorem dimensionOneRosserSeedPrimeSum_fixedSplice_eq
    (P : Finset Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice < s0) :
    dimensionOneRosserSeedPrimeSum P level s0 z =
      dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        dimensionOneRosserSeedPrimeSum P level
          dimensionOneRosserSecondSplice z := by
  have horder := dimensionOneRosserFixedSpliceCutoff_order
    hlevel hz hs hsLower hsUpper hUs0
  let high := P.filter (fun p : Nat =>
    level ^ (1 / s0) <= (p : Real) ∧
      (p : Real) < dimensionOneRosserFixedSpliceCutoff level)
  let outer := P.filter (fun p : Nat =>
    dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ∧
      (p : Real) < z)
  have hdisjoint : Disjoint high outer := by
    rw [Finset.disjoint_left]
    intro p hpHigh hpOuter
    simp only [high, outer, Finset.mem_filter] at hpHigh hpOuter
    linarith [hpHigh.2.2, hpOuter.2.1]
  have hunion : P.filter (fun p : Nat =>
      level ^ (1 / s0) <= (p : Real) /\ (p : Real) < z) =
      high ∪ outer := by
    ext p
    simp only [high, outer, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hp
      by_cases hpCut :
          (p : Real) < dimensionOneRosserFixedSpliceCutoff level
      · exact Or.inl ⟨hp.1, hp.2.1, hpCut⟩
      · exact Or.inr ⟨hp.1, le_of_not_gt hpCut, hp.2.2⟩
    · intro hp
      rcases hp with hp | hp
      · exact ⟨hp.1, hp.2.1, hp.2.2.trans_le horder.2⟩
      · exact ⟨hp.1, horder.1.le.trans hp.2.1, hp.2.2⟩
  unfold dimensionOneRosserSeedPrimeSum
  rw [hunion, Finset.sum_union hdisjoint]
  simp only [high, outer, dimensionOneRosserFixedSpliceCutoff]

private theorem fixedSplice_outer_lt_level
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

private theorem fixedSplice_primeFactor_nonneg
    (P : Finset Nat) {level z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    {p : Nat} (hpP : p ∈ P) (hpz : (p : Real) < z) :
    0 <= (p : Real)⁻¹ *
      sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
      (Real.log (p : Real) / Real.log (level / (p : Real))) := by
  have hpPrime := hprime p hpP
  have hpTwo : (2 : Real) <= p := by exact_mod_cast hpPrime.two_le
  have hpPos : (0 : Real) < p := by linarith
  have hpLevel : (p : Real) < level :=
    hpz.trans (fixedSplice_outer_lt_level hlevel hz hs hsLower)
  have hden : 0 < Real.log (level / (p : Real)) :=
    Real.log_pos ((one_lt_div hpPos).2 hpLevel)
  have hlogp : 0 <= Real.log (p : Real) :=
    Real.log_nonneg (by linarith)
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr hpPos.le)
      (sieveDensityBelow_reciprocal_pos P (p : Real) hprime).le)
    (div_nonneg hlogp hden.le)

/-- On a strict bounded outer shell, the seed is controlled by the delay
sum paired with an upper target. -/
theorem dimensionOneRosserSeedPrimeSum_le_plusUnscaled
    (P : Finset Nat) {level z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsUpper : s < dimensionOneRosserSecondSplice) :
    dimensionOneRosserSeedPrimeSum P level
        dimensionOneRosserSecondSplice z <=
      dimensionOneRosserBoundedSeedShare *
        dimensionOneRosserPlusUnscaledDelayPrimeSum P level
          dimensionOneRosserSecondSplice z := by
  have hlevelOne : 1 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hsPos : 0 < s := by linarith
  unfold dimensionOneRosserSeedPrimeSum
    dimensionOneRosserPlusUnscaledDelayPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have harg := buchstabArgument_mem_Ioc_realEndpoints
    hlevelOne hzOne hsPos hs hsUpper hpData.2
  have hseed := dimensionOneRosserSeedEnvelope_le_boundedMinus
    (show 2 <= buchstabArgument level (p : Real) by linarith [harg.1])
    (show buchstabArgument level (p : Real) <=
        dimensionOneRosserSecondSplice by linarith [harg.2])
  have hfactor := fixedSplice_primeFactor_nonneg P hprime hlevel hz hs
    (by linarith : 2 <= s) hpData.1 hpData.2.2
  calc
    (p : Real)⁻¹ *
          sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
          (Real.log (p : Real) / Real.log (level / (p : Real))) *
          dimensionOneRosserSeedEnvelope
            (buchstabArgument level (p : Real)) <=
        ((p : Real)⁻¹ *
          sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
          (Real.log (p : Real) / Real.log (level / (p : Real)))) *
          (dimensionOneRosserBoundedSeedShare *
            dimensionOneDelayScaledMinus
              (buchstabArgument level (p : Real))) :=
      mul_le_mul_of_nonneg_left hseed hfactor
    _ = dimensionOneRosserBoundedSeedShare *
        ((p : Real)⁻¹ *
          sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
          (Real.log (p : Real) / Real.log (level / (p : Real))) *
          dimensionOneDelayScaledMinus
            (buchstabArgument level (p : Real))) := by ring

/-- On a strict bounded outer shell, the seed is controlled by the delay
sum paired with a lower target. -/
theorem dimensionOneRosserSeedPrimeSum_le_minusUnscaled
    (P : Finset Nat) {level z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s < dimensionOneRosserSecondSplice) :
    dimensionOneRosserSeedPrimeSum P level
        dimensionOneRosserSecondSplice z <=
      dimensionOneRosserBoundedSeedShare *
        dimensionOneRosserMinusUnscaledDelayPrimeSum P level
          dimensionOneRosserSecondSplice z := by
  have hlevelOne : 1 < level := by linarith
  have hzOne : 1 < z := by linarith
  have hsPos : 0 < s := by linarith
  unfold dimensionOneRosserSeedPrimeSum
    dimensionOneRosserMinusUnscaledDelayPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have harg := buchstabArgument_mem_Ioc_realEndpoints
    hlevelOne hzOne hsPos hs hsUpper hpData.2
  have hseed := dimensionOneRosserSeedEnvelope_le_boundedPlus
    (show 1 <= buchstabArgument level (p : Real) by linarith [harg.1])
    (show buchstabArgument level (p : Real) <=
        dimensionOneRosserSecondSplice by linarith [harg.2])
  have hfactor := fixedSplice_primeFactor_nonneg P hprime hlevel hz hs
    hsLower hpData.1 hpData.2.2
  calc
    (p : Real)⁻¹ *
          sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
          (Real.log (p : Real) / Real.log (level / (p : Real))) *
          dimensionOneRosserSeedEnvelope
            (buchstabArgument level (p : Real)) <=
        ((p : Real)⁻¹ *
          sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
          (Real.log (p : Real) / Real.log (level / (p : Real)))) *
          (dimensionOneRosserBoundedSeedShare *
            dimensionOneDelayScaledPlus
              (buchstabArgument level (p : Real))) :=
      mul_le_mul_of_nonneg_left hseed hfactor
    _ = dimensionOneRosserBoundedSeedShare *
        ((p : Real)⁻¹ *
          sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) *
          (Real.log (p : Real) / Real.log (level / (p : Real))) *
          dimensionOneDelayScaledPlus
            (buchstabArgument level (p : Real))) := by ring

/-- At the fixed endpoint, the outer seed carrier is empty. -/
theorem dimensionOneRosserSeedPrimeSum_fixedSplice_eq_zero
    (P : Finset Nat) {level z : Real}
    (hcutoff : dimensionOneRosserFixedSpliceCutoff level = z) :
    dimensionOneRosserSeedPrimeSum P level
      dimensionOneRosserSecondSplice z = 0 := by
  unfold dimensionOneRosserSeedPrimeSum
  unfold dimensionOneRosserFixedSpliceCutoff at hcutoff
  apply Finset.sum_eq_zero
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exfalso
  rw [hcutoff] at hpData
  exact (not_lt_of_ge hpData.2.1) hpData.2.2

/-- At the fixed endpoint, the upper-target outer delay carrier is empty. -/
theorem dimensionOneRosserPlusUnscaledDelayPrimeSum_fixedSplice_eq_zero
    (P : Finset Nat) {level z : Real}
    (hcutoff : dimensionOneRosserFixedSpliceCutoff level = z) :
    dimensionOneRosserPlusUnscaledDelayPrimeSum P level
      dimensionOneRosserSecondSplice z = 0 := by
  unfold dimensionOneRosserPlusUnscaledDelayPrimeSum
  unfold dimensionOneRosserFixedSpliceCutoff at hcutoff
  apply Finset.sum_eq_zero
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exfalso
  rw [hcutoff] at hpData
  exact (not_lt_of_ge hpData.2.1) hpData.2.2

/-- At the fixed endpoint, the lower-target outer delay carrier is empty. -/
theorem dimensionOneRosserMinusUnscaledDelayPrimeSum_fixedSplice_eq_zero
    (P : Finset Nat) {level z : Real}
    (hcutoff : dimensionOneRosserFixedSpliceCutoff level = z) :
    dimensionOneRosserMinusUnscaledDelayPrimeSum P level
      dimensionOneRosserSecondSplice z = 0 := by
  unfold dimensionOneRosserMinusUnscaledDelayPrimeSum
  unfold dimensionOneRosserFixedSpliceCutoff at hcutoff
  apply Finset.sum_eq_zero
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exfalso
  rw [hcutoff] at hpData
  exact (not_lt_of_ge hpData.2.1) hpData.2.2

end PrimesRestrictedDigits
