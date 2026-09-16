import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeed
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceNormalizedScalar

/-!
# Rank-uniform source-normalized high seed

This combines the independent finite high-seed estimate with the unconditional W3 scalar bound
at Iwaniec's Eq. (8.7) cutoff. It proves the source-shaped Eq. (8.13) boundary, but not the
later recurrence ledger.
-/

namespace PrimesRestrictedDigits

private theorem sourceCutoff_logLevel_le_seedUpperBand
    {level s : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hL : Real.exp 1 <= Real.log level)
    (hcutoff : s ^ 50 = Real.log level *
      (Real.log (Real.log level)) ^ 3) :
    Real.log level <= s ^ 51 := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hsOne : 1 <= s := by
    have : 1 < Real.exp 5000 + 1 := by
      linarith [Real.exp_pos 5000]
    exact this.le.trans hsLarge
  have hLPos : 0 < Real.log level := (Real.exp_pos 1).trans_le hL
  have hlogL : 1 <= Real.log (Real.log level) :=
    (Real.le_log_iff_exp_le hLPos).2 hL
  have hlogPow : 1 <= (Real.log (Real.log level)) ^ 3 :=
    one_le_pow₀ hlogL
  have hLle : Real.log level <= s ^ 50 := by
    calc
      Real.log level = Real.log level * 1 := by ring
      _ <= Real.log level * (Real.log (Real.log level)) ^ 3 :=
        mul_le_mul_of_nonneg_left hlogPow hLPos.le
      _ = s ^ 50 := hcutoff.symm
  have hpow : s ^ 50 <= s ^ 51 := by
    calc
      s ^ 50 = s ^ 50 * 1 := by ring
      _ <= s ^ 50 * s :=
        mul_le_mul_of_nonneg_left hsOne (pow_nonneg hs.le 50)
      _ = s ^ 51 := by ring
  exact hLle.trans hpow

/-- Both source-facing Rosser failure truncations satisfy the normalized
Eq. (8.13) boundary, with one threshold uniform in the rank and sign. -/
theorem exists_dimensionOneRosserFailurePartialSums_sourceNormalized :
    ∃ S : Real, Real.exp 5000 + 1 <= S ∧
      ∀ (P : Finset Nat) (R : Nat) {level z0 s0 : Real},
        (forall p, p ∈ P -> p.Prime) ->
          2 <= level -> 2 <= z0 ->
            s0 = Real.log level / Real.log z0 ->
              S <= s0 -> Real.exp 1 <= Real.log level ->
                s0 ^ 50 = Real.log level *
                  (Real.log (Real.log level)) ^ 3 ->
                    upperRosserFailurePartialSum P
                        (fun p => (p : Real)⁻¹) level z0 R <
                      sieveDensityBelow P (fun p => (p : Real)⁻¹) z0 /
                          s0 ^ 2 *
                        (dimensionOneRosserArtificialFactor
                              (Real.log level) 0 s0 *
                            dimensionOneDelayScaledPlus s0 *
                          (Real.log level) ^ (-3 / 8 : Real)) ∧
                    lowerRosserFailurePartialSum P
                        (fun p => (p : Real)⁻¹) level z0 R <
                      sieveDensityBelow P (fun p => (p : Real)⁻¹) z0 /
                          s0 ^ 2 *
                        (dimensionOneRosserArtificialFactor
                              (Real.log level) 0 s0 *
                            dimensionOneDelayScaledMinus s0 *
                          (Real.log level) ^ (-3 / 8 : Real)) := by
  obtain ⟨_C, S, _hC, hS, hscalar⟩ :=
    exists_dimensionOneRosserSeedEnvelope_sourceNormalized
  refine ⟨S, hS, ?_⟩
  intro P R level z0 s0 hprime hlevel hz0 hs0 hsTail hL hcutoff
  have hsLarge : Real.exp 5000 + 1 <= s0 := hS.trans hsTail
  have hs : 0 < s0 := dimensionOneRosserSeed_pos hsLarge
  have hband : Real.log level <= s0 ^ 51 :=
    sourceCutoff_logLevel_le_seedUpperBand hsLarge hL hcutoff
  have hV : 0 <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z0 :=
    sieveDensityBelow_reciprocal_pos P z0 hprime
  have houtside : 0 <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z0 / s0 ^ 2 :=
    div_pos hV (pow_pos hs 2)
  have hupper := dimensionOneRosserUpperFailurePartialSum_lt_seedEnvelope
    P R hprime hlevel hz0 hs0 hsLarge hband
  have hlower := dimensionOneRosserLowerFailurePartialSum_lt_seedEnvelope
    P R hprime hlevel hz0 hs0 hsLarge hband
  have hnormalized := hscalar hsTail hL hcutoff
  exact ⟨hupper.trans (mul_lt_mul_of_pos_left hnormalized.1 houtside),
    hlower.trans (mul_lt_mul_of_pos_left hnormalized.2 houtside)⟩

end PrimesRestrictedDigits
