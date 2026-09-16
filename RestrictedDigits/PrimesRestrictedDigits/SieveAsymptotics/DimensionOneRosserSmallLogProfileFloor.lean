import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceProfileShell
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails

/-!
# Small-log source-profile floor

A logarithmic cap bounds the source coordinate and gives both epsilon-zero source profiles one
common positive floor. This is a project-local compact bound, not Iwaniec's factorial tail
estimate.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable def dimensionOneRosserSmallLogCoordinateCap
    (Lambda : Real) : Real :=
  max 2 (Lambda / Real.log 2)

noncomputable def dimensionOneRosserSmallLogProfileFloor
    (Lambda : Real) : Real :=
  Lambda ^ (-1 / 3 : Real) *
    min
      (dimensionOneDelayScaledPlus
        (dimensionOneRosserSmallLogCoordinateCap Lambda))
      (dimensionOneDelayScaledMinus
        (dimensionOneRosserSmallLogCoordinateCap Lambda))

theorem dimensionOneRosserSourceCoordinate_le_smallLogCoordinateCap
    {level z s Lambda : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hlog : Real.log level <= Lambda) :
    s <= dimensionOneRosserSmallLogCoordinateCap Lambda := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogTwoLe : Real.log 2 <= Real.log z :=
    Real.log_le_log (by norm_num) hz
  have hLambda : 0 < Lambda := hlogLevel.trans_le hlog
  have hratioNonneg : 0 <= Lambda / Real.log 2 :=
    div_nonneg hLambda.le hlogTwo.le
  have hLambdaLe : Lambda <=
      (Lambda / Real.log 2) * Real.log z := by
    calc
      Lambda = (Lambda / Real.log 2) * Real.log 2 := by
        field_simp
      _ <= (Lambda / Real.log 2) * Real.log z :=
        mul_le_mul_of_nonneg_left hlogTwoLe hratioNonneg
  have hratio : Real.log level / Real.log z <=
      Lambda / Real.log 2 := by
    rw [div_le_iff₀ hlogz]
    exact hlog.trans hLambdaLe
  rw [hs]
  exact hratio.trans (le_max_right 2 (Lambda / Real.log 2))

theorem dimensionOneRosserSmallLogProfileFloor_pos
    {Lambda : Real} (hLambda : 0 < Lambda) :
    0 < dimensionOneRosserSmallLogProfileFloor Lambda := by
  have hcap : 2 <= dimensionOneRosserSmallLogCoordinateCap Lambda := by
    exact le_max_left _ _
  unfold dimensionOneRosserSmallLogProfileFloor
  exact mul_pos (Real.rpow_pos_of_pos hLambda _)
    (lt_min
      (dimensionOneDelayScaledPlus_pos (by linarith))
      (dimensionOneDelayScaledMinus_pos (by linarith)))

private theorem smallLogProfileFloor_le_aux
    {L s Lambda : Real} (hL : 0 < L) (hLLambda : L <= Lambda)
    (hs : 0 <= s) {delay : Real -> Real}
    (hdelayS : 0 <= delay s)
    (hmin : min
      (dimensionOneDelayScaledPlus
        (dimensionOneRosserSmallLogCoordinateCap Lambda))
      (dimensionOneDelayScaledMinus
        (dimensionOneRosserSmallLogCoordinateCap Lambda)) <=
      delay (dimensionOneRosserSmallLogCoordinateCap Lambda))
    (hdelay : delay (dimensionOneRosserSmallLogCoordinateCap Lambda) <=
      delay s) :
    dimensionOneRosserSmallLogProfileFloor Lambda <=
      L ^ (-1 / 3 : Real) *
        (dimensionOneRosserArtificialFactor L 0 s * delay s) := by
  have hLambda : 0 < Lambda := hL.trans_le hLLambda
  have hcap : 2 <= dimensionOneRosserSmallLogCoordinateCap Lambda := by
    exact le_max_left _ _
  have hpower : Lambda ^ (-1 / 3 : Real) <=
      L ^ (-1 / 3 : Real) :=
    Real.rpow_le_rpow_of_nonpos hL hLLambda (by norm_num)
  have hfactor : 1 <= dimensionOneRosserArtificialFactor L 0 s :=
    one_le_dimensionOneRosserArtificialFactor_zero hL hs
  have hterminal : min
      (dimensionOneDelayScaledPlus
        (dimensionOneRosserSmallLogCoordinateCap Lambda))
      (dimensionOneDelayScaledMinus
        (dimensionOneRosserSmallLogCoordinateCap Lambda)) <=
      dimensionOneRosserArtificialFactor L 0 s * delay s := by
    have hfactorDelay : delay s <=
        dimensionOneRosserArtificialFactor L 0 s * delay s := by
      simpa using mul_le_mul_of_nonneg_right hfactor hdelayS
    exact hmin.trans (hdelay.trans hfactorDelay)
  unfold dimensionOneRosserSmallLogProfileFloor
  exact mul_le_mul hpower hterminal
    ((lt_min
      (dimensionOneDelayScaledPlus_pos (by linarith))
      (dimensionOneDelayScaledMinus_pos (by linarith))).le)
    (Real.rpow_pos_of_pos hL _).le

theorem dimensionOneRosserSmallLogProfileFloor_le_sourcePlusProfile
    {level z s Lambda : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsOne : 1 <= s) (hlog : Real.log level <= Lambda) :
    dimensionOneRosserSmallLogProfileFloor Lambda <=
      dimensionOneRosserSourcePlusProfile (Real.log level) s := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hsCap := dimensionOneRosserSourceCoordinate_le_smallLogCoordinateCap
    hlevel hz hs hlog
  have hdelay := dimensionOneDelayScaledPlus_antitoneOn
    (show s ∈ Ici (1 : Real) by exact hsOne)
    (show dimensionOneRosserSmallLogCoordinateCap Lambda ∈ Ici (1 : Real) by
      change 1 <= dimensionOneRosserSmallLogCoordinateCap Lambda
      exact (by norm_num : (1 : Real) <= 2).trans (le_max_left _ _))
    hsCap
  simpa [dimensionOneRosserSourcePlusProfile,
    dimensionOneRosserPlusArtificialAux] using
    (smallLogProfileFloor_le_aux hL hlog (by linarith)
      (dimensionOneDelayScaledPlus_pos (by linarith)).le
      (min_le_left _ _) hdelay)

theorem dimensionOneRosserSmallLogProfileFloor_le_sourceMinusProfile
    {level z s Lambda : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsTwo : 2 <= s) (hlog : Real.log level <= Lambda) :
    dimensionOneRosserSmallLogProfileFloor Lambda <=
      dimensionOneRosserSourceMinusProfile (Real.log level) s := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hsCap := dimensionOneRosserSourceCoordinate_le_smallLogCoordinateCap
    hlevel hz hs hlog
  have hdelay := dimensionOneDelayScaledMinus_antitoneOn
    (show s ∈ Ici (2 : Real) by exact hsTwo)
    (show dimensionOneRosserSmallLogCoordinateCap Lambda ∈ Ici (2 : Real) by
      change 2 <= dimensionOneRosserSmallLogCoordinateCap Lambda
      exact le_max_left _ _)
    hsCap
  simpa [dimensionOneRosserSourceMinusProfile,
    dimensionOneRosserMinusArtificialAux] using
    (smallLogProfileFloor_le_aux hL hlog (by linarith)
      (dimensionOneDelayScaledMinus_pos (by linarith)).le
      (min_le_right _ _) hdelay)

end PrimesRestrictedDigits
