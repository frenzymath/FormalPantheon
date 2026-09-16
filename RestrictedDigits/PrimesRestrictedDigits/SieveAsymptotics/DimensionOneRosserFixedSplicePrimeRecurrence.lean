import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFixedSplicePrimeProfiles
import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatioPair
import PrimesRestrictedDigits.SieveAsymptotics.RosserCutoffSplit

/-!
# Exact Rosser recurrence costs at the fixed splice

This file applies piecewise high and bounded inner hypotheses to the exact finite cutoff
recurrences and recombines their literal prime summands.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem fixedSplicePrimeCarrier_eq_union
    (P : Finset Nat) {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice < s0) :
    P.filter (fun p : Nat =>
        level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z) =
      P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧
            (p : Real) < dimensionOneRosserFixedSpliceCutoff level) ∪
        P.filter (fun p : Nat =>
          dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ∧
            (p : Real) < z) := by
  have horder := dimensionOneRosserFixedSpliceCutoff_order hlevel hz hs
    hsLower hsUpper hUs0
  ext p
  simp only [Finset.mem_filter, Finset.mem_union]
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

private theorem fixedSplicePrimeCarriers_disjoint
    (P : Finset Nat) (level z s0 : Real) :
    Disjoint
      (P.filter (fun p : Nat =>
        level ^ (1 / s0) <= (p : Real) ∧
          (p : Real) < dimensionOneRosserFixedSpliceCutoff level))
      (P.filter (fun p : Nat =>
        dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ∧
          (p : Real) < z)) := by
  rw [Finset.disjoint_left]
  intro p hpHigh hpOuter
  simp only [Finset.mem_filter] at hpHigh hpOuter
  exact (not_lt_of_ge hpOuter.2.1) hpHigh.2.2

private theorem fixedSplice_outer_lt_level
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s) :
    z < level := by
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogIdentity : s * Real.log z = Real.log level :=
    (eq_div_iff hlogz.ne').mp hs
  apply (Real.log_lt_log_iff (by linarith) (by linarith)).mp
  nlinarith

/-- The upper exact recurrence is bounded by the whole first and raw sums,
the high seed, and the bounded outer plus-named delay cost. -/
theorem dimensionOneRosserUpperFailure_le_fixedSplicePrimeCosts
    (P : Finset Nat) (R : Nat) {D level z s s0 : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hHigh : forall p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) ->
      (p : Real) < dimensionOneRosserFixedSpliceCutoff level ->
      lowerRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserFirstRegimeMinusMajorant
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real))))
    (hOuter : forall p : Nat, p ∈ P ->
      dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ->
      (p : Real) < z ->
      lowerRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserBoundedMinusMajorant
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)))) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R <=
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z +
        D * dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        D * dimensionOneRosserBoundedSeedShare *
          dimensionOneRosserPlusUnscaledDelayPrimeSum P level
            dimensionOneRosserSecondSplice z := by
  let high := P.filter (fun p : Nat =>
    level ^ (1 / s0) <= (p : Real) ∧
      (p : Real) < dimensionOneRosserFixedSpliceCutoff level)
  let outer := P.filter (fun p : Nat =>
    dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ∧
      (p : Real) < z)
  let first := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      dimensionOneRosserModelMinusPartialSum R
        (buchstabArgument level p)
  let raw := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      (1 + buchstabArgument level p ^ 50 / Real.log (level / p)) ^
        buchstabArgument level p *
      dimensionOneDelayScaledMinus (buchstabArgument level p) *
      (Real.log (level / p)) ^ (-1 / 3 : Real)
  let seed := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      dimensionOneRosserSeedEnvelope (buchstabArgument level p)
  let delay := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      dimensionOneDelayScaledMinus (buchstabArgument level p)
  have hunion := fixedSplicePrimeCarrier_eq_union P hlevel hz hs
    (by linarith : 2 <= s) hsUpper hUs0
  have hdisjoint := fixedSplicePrimeCarriers_disjoint P level z s0
  have hzLevel := fixedSplice_outer_lt_level hlevel hz hs
    (by linarith : 2 <= s)
  have hhighSum :
      (∑ p ∈ high, (p : Real)⁻¹ *
        lowerRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R) <=
        ∑ p ∈ high, (first p + D * raw p + D * seed p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpTwo : (2 : Real) <= p := hcutoff.trans hpData.2.1
    have hpPos : (0 : Real) <= (p : Real)⁻¹ := by positivity
    have hinner := hHigh p hpData.1 hpData.2.1 hpData.2.2
    have hmul := mul_le_mul_of_nonneg_left hinner hpPos
    exact hmul.trans_eq <| by
      simpa only [first, raw, seed] using
        (dimensionOneRosserPlusHighProfileSummand_eq P R
          (D := D) (level := level) (x := p) (by linarith)
          (by linarith) (hpData.2.2.trans_le
            (dimensionOneRosserFixedSpliceCutoff_order hlevel hz hs
              (by linarith : 2 <= s) hsUpper hUs0).2 |>.trans hzLevel))
  have houterSum :
      (∑ p ∈ outer, (p : Real)⁻¹ *
        lowerRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R) <=
        ∑ p ∈ outer,
          (first p + D * raw p +
            D * dimensionOneRosserBoundedSeedShare * delay p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have horder := dimensionOneRosserFixedSpliceCutoff_order hlevel hz hs
      (by linarith : 2 <= s) hsUpper hUs0
    have hpTwo : (2 : Real) <= p :=
      hcutoff.trans (horder.1.le.trans hpData.2.1)
    have hpPos : (0 : Real) <= (p : Real)⁻¹ := by positivity
    have hinner := hOuter p hpData.1 hpData.2.1 hpData.2.2
    have hmul := mul_le_mul_of_nonneg_left hinner hpPos
    exact hmul.trans_eq <| by
      simpa only [first, raw, delay] using
        (dimensionOneRosserPlusBoundedProfileSummand_eq P R
          (D := D) (level := level) (x := p) (by linarith)
          (by linarith) (hpData.2.2.trans hzLevel))
  have hsum :
      (∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
        (p : Real)⁻¹ * lowerRosserFailurePartialSum P
          (fun q => (q : Real)⁻¹) (level / p) p R) <=
      dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z +
        D * dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        D * dimensionOneRosserBoundedSeedShare *
          dimensionOneRosserPlusUnscaledDelayPrimeSum P level
            dimensionOneRosserSecondSplice z := by
    rw [hunion, Finset.sum_union hdisjoint]
    calc
      _ <= (∑ p ∈ high, (first p + D * raw p + D * seed p)) +
          ∑ p ∈ outer,
            (first p + D * raw p +
              D * dimensionOneRosserBoundedSeedShare * delay p) :=
        add_le_add hhighSum houterSum
      _ = _ := by
        unfold dimensionOneRosserPlusFirstPrimeSum
          dimensionOneRosserPlusSecondRawPrimeSum
          dimensionOneRosserSeedPrimeSum
          dimensionOneRosserPlusUnscaledDelayPrimeSum
        rw [hunion, Finset.sum_union hdisjoint,
          Finset.sum_union hdisjoint]
        simp_rw [Finset.sum_add_distrib]
        rw [<- Finset.mul_sum, <- Finset.mul_sum, <- Finset.mul_sum,
          <- Finset.mul_sum]
        simp only [high, outer, first, raw, seed, delay,
          dimensionOneRosserFixedSpliceCutoff, div_eq_mul_inv, mul_comm]
        ring
  have hratio : (3 : Real) <= Real.log level / Real.log z := by
    rw [<- hs]
    exact hsLower
  have hcube : z ^ 3 <= level :=
    power_le_of_natCast_le_log_div_log hlevel hz hratio
  have horder := dimensionOneRosserFixedSpliceCutoff_order hlevel hz hs
    (by linarith : 2 <= s) hsUpper hUs0
  have hwz : level ^ (1 / s0) <= z := horder.1.le.trans horder.2
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

/-- The lower exact recurrence is bounded by the whole first and raw sums,
the high seed, and the bounded outer minus-named delay cost. -/
theorem dimensionOneRosserLowerFailure_le_fixedSplicePrimeCosts
    (P : Finset Nat) (R : Nat) {D level z s s0 : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hHigh : forall p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) ->
      (p : Real) < dimensionOneRosserFixedSpliceCutoff level ->
      upperRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelPlusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserFirstRegimePlusMajorant
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real))))
    (hOuter : forall p : Nat, p ∈ P ->
      dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ->
      (p : Real) < z ->
      upperRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelPlusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserBoundedPlusMajorant
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)))) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
        level z (R + 1) <=
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) (R + 1) +
        dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z +
        D * dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        D * dimensionOneRosserBoundedSeedShare *
          dimensionOneRosserMinusUnscaledDelayPrimeSum P level
            dimensionOneRosserSecondSplice z := by
  let high := P.filter (fun p : Nat =>
    level ^ (1 / s0) <= (p : Real) ∧
      (p : Real) < dimensionOneRosserFixedSpliceCutoff level)
  let outer := P.filter (fun p : Nat =>
    dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ∧
      (p : Real) < z)
  let first := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      dimensionOneRosserModelPlusPartialSum R
        (buchstabArgument level p)
  let raw := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      (1 + buchstabArgument level p ^ 50 / Real.log (level / p)) ^
        buchstabArgument level p *
      dimensionOneDelayScaledPlus (buchstabArgument level p) *
      (Real.log (level / p)) ^ (-1 / 3 : Real)
  let seed := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      dimensionOneRosserSeedEnvelope (buchstabArgument level p)
  let delay := fun p : Nat =>
    (p : Real)⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) p *
      (Real.log p / Real.log (level / p)) *
      dimensionOneDelayScaledPlus (buchstabArgument level p)
  have hunion := fixedSplicePrimeCarrier_eq_union P hlevel hz hs hsLower
    hsUpper hUs0
  have hdisjoint := fixedSplicePrimeCarriers_disjoint P level z s0
  have hzLevel := fixedSplice_outer_lt_level hlevel hz hs hsLower
  have horder := dimensionOneRosserFixedSpliceCutoff_order hlevel hz hs
    hsLower hsUpper hUs0
  have hhighSum :
      (∑ p ∈ high, (p : Real)⁻¹ *
        upperRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R) <=
        ∑ p ∈ high, (first p + D * raw p + D * seed p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpTwo : (2 : Real) <= p := hcutoff.trans hpData.2.1
    have hpPos : (0 : Real) <= (p : Real)⁻¹ := by positivity
    have hinner := hHigh p hpData.1 hpData.2.1 hpData.2.2
    have hmul := mul_le_mul_of_nonneg_left hinner hpPos
    exact hmul.trans_eq <| by
      simpa only [first, raw, seed] using
        (dimensionOneRosserMinusHighProfileSummand_eq P R
          (D := D) (level := level) (x := p) (by linarith)
          (by linarith) (hpData.2.2.trans_le horder.2 |>.trans hzLevel))
  have houterSum :
      (∑ p ∈ outer, (p : Real)⁻¹ *
        upperRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R) <=
        ∑ p ∈ outer,
          (first p + D * raw p +
            D * dimensionOneRosserBoundedSeedShare * delay p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpTwo : (2 : Real) <= p :=
      hcutoff.trans (horder.1.le.trans hpData.2.1)
    have hpPos : (0 : Real) <= (p : Real)⁻¹ := by positivity
    have hinner := hOuter p hpData.1 hpData.2.1 hpData.2.2
    have hmul := mul_le_mul_of_nonneg_left hinner hpPos
    exact hmul.trans_eq <| by
      simpa only [first, raw, delay] using
        (dimensionOneRosserMinusBoundedProfileSummand_eq P R
          (D := D) (level := level) (x := p) (by linarith)
          (by linarith) (hpData.2.2.trans hzLevel))
  have hsum :
      (∑ p ∈ P.filter (fun p : Nat =>
          level ^ (1 / s0) <= (p : Real) ∧ (p : Real) < z),
        (p : Real)⁻¹ * upperRosserFailurePartialSum P
          (fun q => (q : Real)⁻¹) (level / p) p R) <=
      dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z +
        D * dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        D * dimensionOneRosserBoundedSeedShare *
          dimensionOneRosserMinusUnscaledDelayPrimeSum P level
            dimensionOneRosserSecondSplice z := by
    rw [hunion, Finset.sum_union hdisjoint]
    calc
      _ <= (∑ p ∈ high, (first p + D * raw p + D * seed p)) +
          ∑ p ∈ outer,
            (first p + D * raw p +
              D * dimensionOneRosserBoundedSeedShare * delay p) :=
        add_le_add hhighSum houterSum
      _ = _ := by
        unfold dimensionOneRosserMinusFirstPrimeSum
          dimensionOneRosserMinusSecondRawPrimeSum
          dimensionOneRosserSeedPrimeSum
          dimensionOneRosserMinusUnscaledDelayPrimeSum
        rw [hunion, Finset.sum_union hdisjoint,
          Finset.sum_union hdisjoint]
        simp_rw [Finset.sum_add_distrib]
        rw [<- Finset.mul_sum, <- Finset.mul_sum, <- Finset.mul_sum,
          <- Finset.mul_sum]
        simp only [high, outer, first, raw, seed, delay,
          dimensionOneRosserFixedSpliceCutoff, div_eq_mul_inv, mul_comm]
        ring
  have hwz : level ^ (1 / s0) <= z := horder.1.le.trans horder.2
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
