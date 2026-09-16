import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeed
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedPrimeSum

/-!
# Propagating the independent high-rank Rosser seed

This file combines the distant finite seed with its sign-free transformed prime sum. The
resulting half-budget is independent of the later mutual-rank induction.
-/

open MeasureTheory

namespace PrimesRestrictedDigits

/-- The transported boundary, shifted integral, and weighted endpoint consume
at most half of the independent seed envelope. -/
theorem dimensionOneRosserSeedTransportBudget_le_half
    {K L s s0 : Real} (hK : 0 <= K)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46) :
    ((1 + K * s0 / L) / s0) *
          dimensionOneRosserSeedEnvelope s0 +
        (∫ t in s..s0,
          dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) +
        (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneRosserSeedEnvelope (s - 1) <=
      dimensionOneRosserSeedEnvelope s / 2 := by
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hsTwo : 2 <= s := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hs0Eight : (8 : Real) <= s0 := by
    have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    nlinarith [Real.exp_pos (5000 : Real)]
  have hL : 0 < L := (pow_pos hs0Pos 50).trans_le hcap
  have hpow47 : s0 ^ 47 <= s0 ^ 50 := by
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hKnonneg : 0 <= K * s0 := mul_nonneg hK hs0Pos.le
  have hKscale : K * s0 <= L := by
    calc
      K * s0 <= 13824 * K * s0 := by nlinarith
      _ <= s0 ^ 46 * s0 :=
        mul_le_mul_of_nonneg_right hdom hs0Pos.le
      _ = s0 ^ 47 := by ring
      _ <= s0 ^ 50 := hpow47
      _ <= L := hcap
  have hKratio : K * s0 / L <= 1 := (div_le_one hL).2 hKscale
  have hboundaryCoefficient : (1 + K * s0 / L) / s0 <= 1 / 4 := by
    rw [div_le_iff₀ hs0Pos]
    nlinarith
  have hEnvelope0 : 0 <= dimensionOneRosserSeedEnvelope s0 :=
    (dimensionOneRosserSeedEnvelope_pos s0).le
  have hboundary :
      ((1 + K * s0 / L) / s0) *
          dimensionOneRosserSeedEnvelope s0 <=
        dimensionOneRosserSeedEnvelope s0 / 4 := by
    calc
      _ <= (1 / 4 : Real) * dimensionOneRosserSeedEnvelope s0 :=
        mul_le_mul_of_nonneg_right hboundaryCoefficient hEnvelope0
      _ = _ := by ring
  have hintegral := integral_dimensionOneRosserSeedEnvelope_shift_le
    hsLarge hss0.le
  have hhalf : (1 / 2 : Real) <= 1 - 1 / s := by
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hsTwo
    linarith
  have hden : 0 < L * (1 - 1 / s) :=
    mul_pos hL (by linarith)
  have hpow48 : s0 ^ 48 <= s0 ^ 50 := by
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hscaledDom : 16 * K * s0 * s <= L := by
    calc
      16 * K * s0 * s <= 16 * K * s0 * s0 := by
        gcongr
      _ <= 13824 * K * s0 ^ 2 := by
        have hKs0Sq : 0 <= K * s0 ^ 2 := mul_nonneg hK (sq_nonneg s0)
        nlinarith
      _ <= s0 ^ 46 * s0 ^ 2 :=
        mul_le_mul_of_nonneg_right hdom (sq_nonneg s0)
      _ = s0 ^ 48 := by ring
      _ <= s0 ^ 50 := hpow48
      _ <= L := hcap
  have hendpointCoefficient :
      (2 * K * s0 / (L * (1 - 1 / s))) * s <= 1 / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hLhalf : L / 2 <= L * (1 - 1 / s) := by
      have := mul_le_mul_of_nonneg_left hhalf hL.le
      nlinarith
    nlinarith
  have hshift := dimensionOneRosserSeedEnvelope_shift_le hsLarge
  have hendpointMultiplier :
      0 <= 2 * K * s0 / (L * (1 - 1 / s)) := by positivity
  have hendpoint :
      (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneRosserSeedEnvelope (s - 1) <=
        dimensionOneRosserSeedEnvelope s / 4 := by
    calc
      _ <= (2 * K * s0 / (L * (1 - 1 / s))) *
          (s * dimensionOneRosserSeedEnvelope s) :=
        mul_le_mul_of_nonneg_left hshift hendpointMultiplier
      _ = ((2 * K * s0 / (L * (1 - 1 / s))) * s) *
          dimensionOneRosserSeedEnvelope s := by ring
      _ <= (1 / 4 : Real) * dimensionOneRosserSeedEnvelope s :=
        mul_le_mul_of_nonneg_right hendpointCoefficient
          (dimensionOneRosserSeedEnvelope_pos s).le
      _ = _ := by ring
  linarith

private theorem rosserSeed_add_primeSum_lt_half
    (P : Finset Nat) {K level z s s0 : Real}
    (failure : Real)
    (hseed : failure <
      sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (level ^ (1 / s0)) / s0 ^ 2 *
        dimensionOneRosserSeedEnvelope s0)
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hdom : 13824 * K <= s0 ^ 46)
    (hRatio : forall x : Real,
      level ^ (1 / s0) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    failure + dimensionOneRosserSeedPrimeSum P level s0 z <
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneRosserSeedEnvelope s / 2) := by
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hlevelPos : 0 < level := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hzLog : 0 < Real.log z := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hwz : level ^ (1 / s0) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 (by
      have hexp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
      linarith)
  have hratioW := hRatio (level ^ (1 / s0)) le_rfl hwz
  have hlogw : Real.log (level ^ (1 / s0)) =
      Real.log level / s0 := log_rpow_one_div hlevelPos
  have hlogz : Real.log z = Real.log level / s := by
    rw [hs]
    field_simp [hL.ne', hzLog.ne']
  have hratioExact :
      Real.log z / Real.log (level ^ (1 / s0)) *
          (1 + K / Real.log (level ^ (1 / s0))) =
        s0 / s * (1 + K * s0 / Real.log level) := by
    rw [hlogw, hlogz]
    field_simp [hL.ne', hsPos.ne', hs0Pos.ne']
  rw [hratioExact] at hratioW
  have hboundaryTransport :
      sieveDensityBelow P (fun q => (q : Real)⁻¹)
            (level ^ (1 / s0)) / s0 ^ 2 *
          dimensionOneRosserSeedEnvelope s0 <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
          (((1 + K * s0 / Real.log level) / s0) *
            dimensionOneRosserSeedEnvelope s0) := by
    have hratioMul := mul_le_mul_of_nonneg_left hratioW hV.le
    have hVbound : sieveDensityBelow P (fun q => (q : Real)⁻¹)
          (level ^ (1 / s0)) <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) z *
          (s0 / s * (1 + K * s0 / Real.log level)) := by
      calc
        _ = sieveDensityBelow P (fun q => (q : Real)⁻¹) z *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹)
              (level ^ (1 / s0)) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) := by
          field_simp [hV.ne']
        _ <= _ := hratioMul
    have hmult : 0 <= dimensionOneRosserSeedEnvelope s0 / s0 ^ 2 :=
      div_nonneg (dimensionOneRosserSeedEnvelope_pos s0).le
        (sq_nonneg s0)
    have := mul_le_mul_of_nonneg_right hVbound hmult
    calc
      _ = sieveDensityBelow P (fun q => (q : Real)⁻¹)
          (level ^ (1 / s0)) *
            (dimensionOneRosserSeedEnvelope s0 / s0 ^ 2) := by ring
      _ <= (sieveDensityBelow P (fun q => (q : Real)⁻¹) z *
          (s0 / s * (1 + K * s0 / Real.log level))) *
            (dimensionOneRosserSeedEnvelope s0 / s0 ^ 2) := this
      _ = _ := by field_simp [hL.ne', hsPos.ne', hs0Pos.ne']
  have hprimeSum := dimensionOneRosserSeedPrimeSum_le_of_ratio P hK hprime
    hlevel hz hs hsLarge hss0 hcutoff hRatio
  have hscale : 0 <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s :=
    div_nonneg hV.le hsPos.le
  have hbudget := dimensionOneRosserSeedTransportBudget_le_half hK hsLarge
    hss0 hcap hdom
  have hbudget' :
      ((1 + K * s0 / Real.log level) / s0) *
            dimensionOneRosserSeedEnvelope s0 +
          ((∫ t in s..s0,
            dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserSeedEnvelope (s - 1)) <=
        dimensionOneRosserSeedEnvelope s / 2 := by
    simpa only [add_assoc] using hbudget
  calc
    failure + dimensionOneRosserSeedPrimeSum P level s0 z <
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s) *
          (((1 + K * s0 / Real.log level) / s0) *
              dimensionOneRosserSeedEnvelope s0) +
          dimensionOneRosserSeedPrimeSum P level s0 z :=
      add_lt_add_of_lt_of_le (hseed.trans_le hboundaryTransport) le_rfl
    _ <= (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s) *
          (((1 + K * s0 / Real.log level) / s0) *
            dimensionOneRosserSeedEnvelope s0) +
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s) *
          ((∫ t in s..s0,
            dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserSeedEnvelope (s - 1)) :=
      add_le_add le_rfl hprimeSum
    _ = (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s) *
        (((1 + K * s0 / Real.log level) / s0) *
            dimensionOneRosserSeedEnvelope s0 +
          ((∫ t in s..s0,
            dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserSeedEnvelope (s - 1))) := by
      ring
    _ <= (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s) *
        (dimensionOneRosserSeedEnvelope s / 2) :=
      mul_le_mul_of_nonneg_left hbudget' hscale

/-- The upper boundary seed and its transformed sign-free error use at most
half of the current envelope, uniformly in rank. -/
theorem dimensionOneRosserUpperSeed_add_primeSum_lt_half
    (P : Finset Nat) (R : Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hdom : 13824 * K <= s0 ^ 46)
    (hRatio : forall x : Real,
      level ^ (1 / s0) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
        level (level ^ (1 / s0)) R +
        dimensionOneRosserSeedPrimeSum P level s0 z <
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneRosserSeedEnvelope s / 2) := by
  apply rosserSeed_add_primeSum_lt_half P
  · apply dimensionOneRosserUpperFailurePartialSum_lt_seedEnvelope P R hprime
      hlevel hcutoff
    · symm
      rw [log_rpow_one_div (by linarith : 0 < level)]
      field_simp [show s0 ≠ 0 by
        have hsPos := dimensionOneRosserSeed_pos hsLarge
        linarith, show Real.log level ≠ 0 by
        exact (Real.log_pos (by linarith)).ne']
    · have hsPos := dimensionOneRosserSeed_pos hsLarge
      exact hsLarge.trans (by linarith)
    · exact hband
  · exact hK
  · exact hprime
  · exact hlevel
  · exact hz
  · exact hs
  · exact hsLarge
  · exact hss0
  · exact hcutoff
  · exact hcap
  · exact hdom
  · exact hRatio

/-- The lower boundary seed and its transformed sign-free error use at most
half of the current envelope, uniformly in rank. -/
theorem dimensionOneRosserLowerSeed_add_primeSum_lt_half
    (P : Finset Nat) (R : Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hdom : 13824 * K <= s0 ^ 46)
    (hRatio : forall x : Real,
      level ^ (1 / s0) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
        level (level ^ (1 / s0)) R +
        dimensionOneRosserSeedPrimeSum P level s0 z <
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (dimensionOneRosserSeedEnvelope s / 2) := by
  apply rosserSeed_add_primeSum_lt_half P
  · apply dimensionOneRosserLowerFailurePartialSum_lt_seedEnvelope P R hprime
      hlevel hcutoff
    · symm
      rw [log_rpow_one_div (by linarith : 0 < level)]
      field_simp [show s0 ≠ 0 by
        have hsPos := dimensionOneRosserSeed_pos hsLarge
        linarith, show Real.log level ≠ 0 by
        exact (Real.log_pos (by linarith)).ne']
    · have hsPos := dimensionOneRosserSeed_pos hsLarge
      exact hsLarge.trans (by linarith)
    · exact hband
  · exact hK
  · exact hprime
  · exact hlevel
  · exact hz
  · exact hs
  · exact hsLarge
  · exact hss0
  · exact hcutoff
  · exact hcap
  · exact hdom
  · exact hRatio

end PrimesRestrictedDigits
