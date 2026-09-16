import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayLowerScaleErrorThreshold
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceSeedNormalization

/-!
# Unconditional source-normalized scalar seed

This composes the W1/W2 delay bounds with the conditional X wrappers. The source cutoff and
`exp 1 <= L` remain explicit hypotheses.
-/

namespace PrimesRestrictedDigits

theorem exists_dimensionOneRosserSeedEnvelope_sourceNormalized :
    ∃ C S : Real, 0 < C ∧ Real.exp 5000 + 1 <= S ∧
      ∀ {L s : Real}, S <= s -> Real.exp 1 <= L ->
        s ^ 50 = L * (Real.log L) ^ 3 ->
          dimensionOneRosserSeedEnvelope s <
              dimensionOneRosserArtificialFactor L 0 s *
                dimensionOneDelayScaledPlus s * L ^ (-3 / 8 : Real) ∧
          dimensionOneRosserSeedEnvelope s <
              dimensionOneRosserArtificialFactor L 0 s *
                dimensionOneDelayScaledMinus s * L ^ (-3 / 8 : Real) := by
  obtain ⟨C, S₁, hC, _hS₁, hLower⟩ :=
    exists_dimensionOneDelaySum_lowerScale
  obtain ⟨S₂, hS₂, hError⟩ :=
    exists_dimensionOneDelayLowerScale_error_threshold hC
  let S : Real := max S₁ (max (Real.exp 5000 + 1) S₂)
  refine ⟨C, S, hC, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · intro L s hs hL hcutoff
    have hs₁ : S₁ <= s := (le_max_left _ _).trans hs
    have hs₂ : S₂ <= s :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hs)
    have hsLarge : Real.exp 5000 + 1 <= s :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hs)
    have hlower : dimensionOneDelayLowerScale C s <=
        dimensionOneDelaySum s := (hLower hs₁).le
    have herror : C * Real.log (Real.log (2 * s)) <= Real.log s :=
      hError hs₂
    have hPlus := dimensionOneRosserSeedEnvelope_lt_sourceNormalizedPlus
      (le_of_lt hC) hsLarge hL hcutoff herror hlower
    have hMinus := dimensionOneRosserSeedEnvelope_lt_sourceNormalizedMinus
      (le_of_lt hC) hsLarge hL hcutoff herror hlower
    exact ⟨hPlus, hMinus⟩

end PrimesRestrictedDigits
