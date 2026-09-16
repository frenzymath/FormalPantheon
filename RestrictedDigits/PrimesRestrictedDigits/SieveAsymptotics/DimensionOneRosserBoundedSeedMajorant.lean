import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedSeedAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFirstRegimeMajorant

/-!
# Bounded additive Rosser majorants

These profiles replace the independent seed envelope by its compact sign-specific delay bound.
The added delay term is not logarithmically normalized and is not an induction-ready form of
Iwaniec's Eq. (8.14).
-/

namespace PrimesRestrictedDigits

/-- The target-plus bounded majorant with the absorbed seed coefficient. -/
noncomputable def dimensionOneRosserBoundedPlusMajorant
    (L t : Real) : Real :=
  L ^ (-1 / 3 : Real) * dimensionOneRosserArtificialFactor L 0 t *
      dimensionOneDelayScaledPlus t +
    (dimensionOneRosserBoundedSeedConstant / 4) *
      dimensionOneDelayScaledPlus t

/-- The target-minus bounded majorant with the absorbed seed coefficient. -/
noncomputable def dimensionOneRosserBoundedMinusMajorant
    (L t : Real) : Real :=
  L ^ (-1 / 3 : Real) * dimensionOneRosserArtificialFactor L 0 t *
      dimensionOneDelayScaledMinus t +
    (dimensionOneRosserBoundedSeedConstant / 4) *
      dimensionOneDelayScaledMinus t

/-- The additive target-plus first-regime profile is bounded by the compact
delay majorant. -/
theorem dimensionOneRosserFirstRegimePlusMajorant_le_bounded
    (L : Real) {t : Real} (ht : 1 <= t)
    (htU : t <= dimensionOneRosserSecondSplice) :
    dimensionOneRosserFirstRegimePlusMajorant L t <=
      dimensionOneRosserBoundedPlusMajorant L t := by
  unfold dimensionOneRosserFirstRegimePlusMajorant
    dimensionOneRosserBoundedPlusMajorant
  exact add_le_add_right
    (dimensionOneRosserSeedEnvelope_le_boundedPlus ht htU) _

/-- The additive target-minus first-regime profile is bounded by the compact
delay majorant. -/
theorem dimensionOneRosserFirstRegimeMinusMajorant_le_bounded
    (L : Real) {t : Real} (ht : 2 <= t)
    (htU : t <= dimensionOneRosserSecondSplice) :
    dimensionOneRosserFirstRegimeMinusMajorant L t <=
      dimensionOneRosserBoundedMinusMajorant L t := by
  unfold dimensionOneRosserFirstRegimeMinusMajorant
    dimensionOneRosserBoundedMinusMajorant
  exact add_le_add_right
    (dimensionOneRosserSeedEnvelope_le_boundedMinus ht htU) _

end PrimesRestrictedDigits
