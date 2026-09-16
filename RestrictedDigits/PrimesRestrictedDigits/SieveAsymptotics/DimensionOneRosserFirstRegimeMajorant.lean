import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArtificialFactor
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedScalars

/-!
# Additive first-regime Rosser majorants

These profiles retain the independently propagated high-rank seed beside the contracted
dimension-one delay term. They do not claim Iwaniec's Eq. (8.14) or Eq. (9.1).
-/

namespace PrimesRestrictedDigits

/-- The target-plus first-regime profile with an additive independent seed. -/
noncomputable def dimensionOneRosserFirstRegimePlusMajorant
    (L s : Real) : Real :=
  L ^ (-1 / 3 : Real) * dimensionOneRosserArtificialFactor L 0 s *
      dimensionOneDelayScaledPlus s +
    dimensionOneRosserSeedEnvelope s

/-- The target-minus first-regime profile with an additive independent seed. -/
noncomputable def dimensionOneRosserFirstRegimeMinusMajorant
    (L s : Real) : Real :=
  L ^ (-1 / 3 : Real) * dimensionOneRosserArtificialFactor L 0 s *
      dimensionOneDelayScaledMinus s +
    dimensionOneRosserSeedEnvelope s

/-- Source-facing form of the target-plus additive profile. -/
theorem dimensionOneRosserFirstRegimePlusMajorant_eq
    {L s : Real} (hL : 0 < L) :
    dimensionOneRosserFirstRegimePlusMajorant L s =
      L ^ (-1 / 3 : Real) * (1 + s ^ 50 / L) ^ s *
        dimensionOneDelayScaledPlus s +
          dimensionOneRosserSeedEnvelope s := by
  unfold dimensionOneRosserFirstRegimePlusMajorant
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  norm_num

/-- Source-facing form of the target-minus additive profile. -/
theorem dimensionOneRosserFirstRegimeMinusMajorant_eq
    {L s : Real} (hL : 0 < L) :
    dimensionOneRosserFirstRegimeMinusMajorant L s =
      L ^ (-1 / 3 : Real) * (1 + s ^ 50 / L) ^ s *
        dimensionOneDelayScaledMinus s +
          dimensionOneRosserSeedEnvelope s := by
  unfold dimensionOneRosserFirstRegimeMinusMajorant
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  norm_num

end PrimesRestrictedDigits
