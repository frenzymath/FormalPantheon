import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserCompleteRapidScalar
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFullSourceMutualInduction
/-! # DimensionOneRosserCompleteRapidDecay -/

set_option maxHeartbeats 4000000

/-!
# Complete rapid Rosser failure decay

The complete source targets and the independent high-seed envelope are joined at the explicit
logarithmic split `log level <= s^51`. This is the source-layer estimate needed before the
main-sum and remainder bridges of the repaired Fundamental Lemma.
-/

namespace PrimesRestrictedDigits

private theorem completeRapid_large_implies_delay_threshold
    {s : Real} (hsLarge : Real.exp 5000 + 1 <= s) :
    128 * Real.exp 2 <= s := by
  have hlogTwo : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : Real))
      (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hlog128 : Real.log (128 : Real) = 7 * Real.log 2 := by
    rw [show (128 : Real) = 2 ^ (7 : Nat) by norm_num, Real.log_pow]
    norm_num
  have hlogProduct : Real.log ((128 : Real) * Real.exp 2) =
      Real.log 128 + 2 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero 2), Real.log_exp]
  have hlogBound : Real.log ((128 : Real) * Real.exp 2) < 5000 := by
    rw [hlogProduct, hlog128]
    nlinarith
  have hpositive : 0 < (128 : Real) * Real.exp 2 := by positivity
  have hconstant : (128 : Real) * Real.exp 2 < Real.exp 5000 := by
    calc
      (128 : Real) * Real.exp 2 =
          Real.exp (Real.log ((128 : Real) * Real.exp 2)) := by
            rw [Real.exp_log hpositive]
      _ < Real.exp 5000 := Real.exp_lt_exp.mpr hlogBound
  have hbase : Real.exp 5000 <= Real.exp 5000 + 1 := by linarith
  exact hconstant.le.trans (hbase.trans hsLarge)

private theorem dimensionOneRosserSourcePlusProfile_lt_exp_neg
    {L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hpow : s ^ (51 : Nat) <= L) :
    dimensionOneRosserSourcePlusProfile L s <
      Real.exp 1 * Real.exp (-s) := by
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hsOne : 1 <= s := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hspowOne : 1 <= s ^ (51 : Nat) := one_le_pow₀ hsOne
  have hLOne : 1 <= L := hspowOne.trans hpow
  have hfactor := dimensionOneRosserArtificialFactor_zero_le_exp_one
    hsOne hpow
  have hLpow : L ^ (-1 / 3 : Real) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hLOne (by norm_num)
  have hfactor0 : 0 <=
      dimensionOneRosserArtificialFactor L 0 s :=
    (Real.exp_pos _).le
  have hdelay := dimensionOneDelayQPlus_scaled_lt_exp_neg
    (completeRapid_large_implies_delay_threshold hsLarge)
  rw [sq_mul_dimensionOneDelayQPlus hsPos.ne'] at hdelay
  have hscaled0 : 0 <= dimensionOneDelayScaledPlus s :=
    (dimensionOneDelayScaledPlus_pos hsPos).le
  have hfirst : L ^ (-1 / 3 : Real) *
      dimensionOneRosserArtificialFactor L 0 s <= Real.exp 1 := by
    calc
      L ^ (-1 / 3 : Real) *
          dimensionOneRosserArtificialFactor L 0 s <=
          1 * dimensionOneRosserArtificialFactor L 0 s :=
        mul_le_mul_of_nonneg_right hLpow hfactor0
      _ <= Real.exp 1 := by simpa using hfactor
  have hsecond :
      (L ^ (-1 / 3 : Real) *
        dimensionOneRosserArtificialFactor L 0 s) *
        dimensionOneDelayScaledPlus s <=
      Real.exp 1 * dimensionOneDelayScaledPlus s :=
    mul_le_mul_of_nonneg_right hfirst hscaled0
  unfold dimensionOneRosserSourcePlusProfile
    dimensionOneRosserPlusArtificialAux
  calc
    L ^ (-1 / 3 : Real) *
        (dimensionOneRosserArtificialFactor L 0 s *
          dimensionOneDelayScaledPlus s) =
      (L ^ (-1 / 3 : Real) *
        dimensionOneRosserArtificialFactor L 0 s) *
        dimensionOneDelayScaledPlus s := by ring
    _ <= Real.exp 1 * dimensionOneDelayScaledPlus s := hsecond
    _ < Real.exp 1 * Real.exp (-s) :=
      mul_lt_mul_of_pos_left hdelay (Real.exp_pos 1)

private theorem dimensionOneRosserSourceMinusProfile_lt_exp_neg
    {L s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hpow : s ^ (51 : Nat) <= L) :
    dimensionOneRosserSourceMinusProfile L s <
      Real.exp 1 * Real.exp (-s) := by
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hsTwo : 2 <= s := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hsOne : 1 <= s := by linarith
  have hspowOne : 1 <= s ^ (51 : Nat) := one_le_pow₀ hsOne
  have hLOne : 1 <= L := hspowOne.trans hpow
  have hfactor := dimensionOneRosserArtificialFactor_zero_le_exp_one
    hsOne hpow
  have hLpow : L ^ (-1 / 3 : Real) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hLOne (by norm_num)
  have hfactor0 : 0 <=
      dimensionOneRosserArtificialFactor L 0 s :=
    (Real.exp_pos _).le
  have hdelay := dimensionOneDelayQMinus_scaled_lt_exp_neg
    (completeRapid_large_implies_delay_threshold hsLarge)
  rw [sq_mul_dimensionOneDelayQMinus hsPos.ne'] at hdelay
  have hscaled0 : 0 <= dimensionOneDelayScaledMinus s :=
    (dimensionOneDelayScaledMinus_pos hsPos).le
  have hfirst : L ^ (-1 / 3 : Real) *
      dimensionOneRosserArtificialFactor L 0 s <= Real.exp 1 := by
    calc
      L ^ (-1 / 3 : Real) *
          dimensionOneRosserArtificialFactor L 0 s <=
          1 * dimensionOneRosserArtificialFactor L 0 s :=
        mul_le_mul_of_nonneg_right hLpow hfactor0
      _ <= Real.exp 1 := by simpa using hfactor
  have hsecond :
      (L ^ (-1 / 3 : Real) *
        dimensionOneRosserArtificialFactor L 0 s) *
        dimensionOneDelayScaledMinus s <=
      Real.exp 1 * dimensionOneDelayScaledMinus s :=
    mul_le_mul_of_nonneg_right hfirst hscaled0
  unfold dimensionOneRosserSourceMinusProfile
    dimensionOneRosserMinusArtificialAux
  calc
    L ^ (-1 / 3 : Real) *
        (dimensionOneRosserArtificialFactor L 0 s *
          dimensionOneDelayScaledMinus s) =
      (L ^ (-1 / 3 : Real) *
        dimensionOneRosserArtificialFactor L 0 s) *
        dimensionOneDelayScaledMinus s := by ring
    _ <= Real.exp 1 * dimensionOneDelayScaledMinus s := hsecond
    _ < Real.exp 1 * Real.exp (-s) :=
      mul_lt_mul_of_pos_left hdelay (Real.exp_pos 1)

private theorem dimensionOneRosserCompleteRapid_high
    {P : Finset Nat} {C level z s : Real}
    (hC : 1 <= C) (hprime : ∀ p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hband : Real.log level <= s ^ (51 : Nat)) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (C * Real.exp (-s)) ∧
      lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (C * Real.exp (-s)) := by
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hsOne : 1 <= s := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hOutside : 0 <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s ^ 2 :=
    div_pos hV (sq_pos_of_pos hsPos)
  have hExp : Real.exp 5000 <= s := by linarith
  have hEnv := dimensionOneRosserSeedEnvelope_lt_exp_neg hExp
  have hUpper := dimensionOneRosserUpperFailureSum_lt_seedEnvelope
    P hprime hlevel hz hs hsLarge hband
  have hLower := dimensionOneRosserLowerFailureSum_lt_seedEnvelope
    P hprime hlevel hz hs hsLarge hband
  have hUpper' := hUpper.trans
    (mul_lt_mul_of_pos_left hEnv hOutside)
  have hLower' := hLower.trans
    (mul_lt_mul_of_pos_left hEnv hOutside)
  have hInner : Real.exp (-s) / s <= C * Real.exp (-s) := by
    have hdiv : Real.exp (-s) / s <= Real.exp (-s) :=
      div_le_self (Real.exp_pos (-s)).le hsOne
    have hCexp : Real.exp (-s) <= C * Real.exp (-s) := by
      nlinarith [Real.exp_pos (-s), hC]
    exact hdiv.trans hCexp
  have hScale : 0 <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    (div_pos hV hsPos).le
  have hCompare :
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s ^ 2 *
          Real.exp (-s) <=
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (C * Real.exp (-s)) := by
    calc
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s ^ 2 *
          Real.exp (-s) =
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
          (Real.exp (-s) / s) := by field_simp [hsPos.ne']
      _ <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (C * Real.exp (-s)) :=
        mul_le_mul_of_nonneg_left hInner hScale
  exact ⟨hUpper'.trans_le hCompare, hLower'.trans_le hCompare⟩

/-- One absolute rapid-decay constant controls both complete Rosser failure
 sums on the large-coordinate domain. -/
theorem exists_dimensionOneRosserCompleteFailureSums_lt_exp_neg :
    ∃ C : Real, 1 <= C ∧
      ∀ (P : Finset Nat),
        (∀ p, p ∈ P -> p.Prime) ->
        (∀ p, p ∈ P -> ¬p ∣ 10) ->
        ∀ {level z s : Real},
          2 <= level -> 2 <= z ->
          s = Real.log level / Real.log z ->
          Real.exp 5000 + 1 <= s ->
          upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <
              sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
                (C * Real.exp (-s)) ∧
          lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <
              sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
                (C * Real.exp (-s)) := by
  obtain ⟨D, hD, hTargets⟩ := exists_dimensionOneRosserFullSourceTargets
  obtain ⟨c, hc, hModelPlus, hModelMinus⟩ :=
    exists_dimensionOneRosserModelRaw_le_delay_closed
  let C : Real := 1 + c + D * Real.exp 1
  have hC : 1 <= C := by
    dsimp [C]
    have hE : 0 < Real.exp 1 := Real.exp_pos 1
    have hD0 : 0 <= D := by linarith
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro P hprime hdecimal
  obtain ⟨hUpperTarget, hLowerTarget⟩ := hTargets P hprime hdecimal
  intro level z s hlevel hz hs hsLarge
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hsOne : 1 < s := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hsTwo : 2 <= s := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  by_cases hband : Real.log level <= s ^ (51 : Nat)
  · exact dimensionOneRosserCompleteRapid_high hC hprime hlevel hz hs
      hsLarge hband
  · have hpowStrict : s ^ (51 : Nat) < Real.log level :=
      lt_of_not_ge hband
    have hpow : s ^ (51 : Nat) <= Real.log level := hpowStrict.le
    have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
      sieveDensityBelow_reciprocal_pos P z hprime
    have hScale : 0 <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
      div_pos hV hsPos
    have hRawPlus := hModelPlus (s := s) hsOne.le
    have hRawMinus := hModelMinus (s := s) hsTwo
    have hDelayPlus := dimensionOneDelayQPlus_scaled_lt_exp_neg
      (completeRapid_large_implies_delay_threshold hsLarge)
    have hDelayMinus := dimensionOneDelayQMinus_scaled_lt_exp_neg
      (completeRapid_large_implies_delay_threshold hsLarge)
    rw [sq_mul_dimensionOneDelayQPlus hsPos.ne'] at hDelayPlus
    rw [sq_mul_dimensionOneDelayQMinus hsPos.ne'] at hDelayMinus
    have hRawPlus' : dimensionOneRosserModelPlusRaw s <
        c * Real.exp (-s) :=
      hRawPlus.trans_lt (mul_lt_mul_of_pos_left hDelayPlus hc)
    have hRawMinus' : dimensionOneRosserModelMinusRaw s <
        c * Real.exp (-s) :=
      hRawMinus.trans_lt (mul_lt_mul_of_pos_left hDelayMinus hc)
    have hProfilePlus := dimensionOneRosserSourcePlusProfile_lt_exp_neg
      hsLarge hpow
    have hProfileMinus := dimensionOneRosserSourceMinusProfile_lt_exp_neg
      hsLarge hpow
    have hDPos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hDPlus := mul_lt_mul_of_pos_left hProfilePlus hDPos
    have hDMinus := mul_lt_mul_of_pos_left hProfileMinus hDPos
    have hBracketPlus :
        dimensionOneRosserModelPlusRaw s +
            D * dimensionOneRosserSourcePlusProfile (Real.log level) s <
          C * Real.exp (-s) := by
      have hsum := add_lt_add hRawPlus' hDPlus
      dsimp [C] at hsum ⊢
      nlinarith [Real.exp_pos (-s)]
    have hBracketMinus :
        dimensionOneRosserModelMinusRaw s +
            D * dimensionOneRosserSourceMinusProfile (Real.log level) s <
          C * Real.exp (-s) := by
      have hsum := add_lt_add hRawMinus' hDMinus
      dsimp [C] at hsum ⊢
      nlinarith [Real.exp_pos (-s)]
    have hFullUpper := hUpperTarget hlevel hz hs hsOne
    have hFullLower := hLowerTarget hlevel hz hs hsTwo
    unfold dimensionOneRosserFullSourceUpperTarget at hFullUpper
    unfold dimensionOneRosserFullSourceLowerTarget at hFullLower
    constructor
    · exact hFullUpper.trans
        (mul_lt_mul_of_pos_left hBracketPlus hScale)
    · exact hFullLower.trans
        (mul_lt_mul_of_pos_left hBracketMinus hScale)

end PrimesRestrictedDigits
