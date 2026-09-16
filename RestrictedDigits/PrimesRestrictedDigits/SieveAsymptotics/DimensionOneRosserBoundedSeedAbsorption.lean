import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedScalars

/-!
# Bounded absorption of the independent Rosser seed

This compares the project-local high-rank seed envelope with the two dimension-one delay
profiles on a fixed compact range. It is an independent replacement helper and does not claim
Iwaniec's Eq. (8.13).
-/

open Set

namespace PrimesRestrictedDigits

/-- An explicit absolute ceiling for the seed envelope on the bounded range. -/
noncomputable def dimensionOneRosserBoundedSeedCeiling : Real :=
  Real.exp (1026 * dimensionOneRosserSecondSplice)

/-- A common positive endpoint floor for the two scaled delay profiles. -/
noncomputable def dimensionOneRosserBoundedDelayFloor : Real :=
  min
    (dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice)
    (dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice)

/-- The absolute coefficient used to absorb the bounded seed envelope. -/
noncomputable def dimensionOneRosserBoundedSeedConstant : Real :=
  4 * dimensionOneRosserBoundedSeedCeiling /
    dimensionOneRosserBoundedDelayFloor

/-- The common delay floor at the fixed splice is strictly positive. -/
theorem dimensionOneRosserBoundedDelayFloor_pos :
    0 < dimensionOneRosserBoundedDelayFloor := by
  have hU : 0 < dimensionOneRosserSecondSplice :=
    zero_lt_one.trans_le one_le_dimensionOneRosserSecondSplice
  exact lt_min
    (dimensionOneDelayScaledPlus_pos hU)
    (dimensionOneDelayScaledMinus_pos hU)

/-- The bounded absorption coefficient is at least one. -/
theorem one_le_dimensionOneRosserBoundedSeedConstant :
    1 <= dimensionOneRosserBoundedSeedConstant := by
  have hU0 : 0 <= dimensionOneRosserSecondSplice :=
    (zero_le_one.trans one_le_dimensionOneRosserSecondSplice)
  have hCeiling : 1 <= dimensionOneRosserBoundedSeedCeiling := by
    unfold dimensionOneRosserBoundedSeedCeiling
    exact Real.one_le_exp (mul_nonneg (by norm_num) hU0)
  have hPlusAtSplice :
      dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice <=
        dimensionOneDelayScaledPlus 1 :=
    dimensionOneDelayScaledPlus_antitoneOn
      (show (1 : Real) ∈ Ici 1 by norm_num)
      (show dimensionOneRosserSecondSplice ∈ Ici (1 : Real) by
        exact one_le_dimensionOneRosserSecondSplice)
      one_le_dimensionOneRosserSecondSplice
  have hFloorOne : dimensionOneRosserBoundedDelayFloor <= 1 := by
    calc
      dimensionOneRosserBoundedDelayFloor <=
          dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice :=
        min_le_left _ _
      _ <= dimensionOneDelayScaledPlus 1 := hPlusAtSplice
      _ = 1 / 2 := dimensionOneDelayScaledPlus_eq_half_of_le (by norm_num)
      _ <= 1 := by norm_num
  rw [dimensionOneRosserBoundedSeedConstant,
    le_div_iff₀ dimensionOneRosserBoundedDelayFloor_pos]
  nlinarith

/-- The seed envelope is uniformly bounded by the explicit ceiling on the
closed interval from one to the fixed splice. -/
theorem dimensionOneRosserSeedEnvelope_le_boundedCeiling
    {t : Real} (ht : 1 <= t)
    (htU : t <= dimensionOneRosserSecondSplice) :
    dimensionOneRosserSeedEnvelope t <=
      dimensionOneRosserBoundedSeedCeiling := by
  by_cases htOne : t = 1
  · subst t
    unfold dimensionOneRosserSeedEnvelope dimensionOneRosserSeedTilt
      dimensionOneRosserBoundedSeedCeiling
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith [one_le_dimensionOneRosserSecondSplice]
  · have htStrict : 1 < t := lt_of_le_of_ne ht (Ne.symm htOne)
    have htPos : 0 < t := zero_lt_one.trans htStrict
    have hlogPos : 0 < Real.log t := Real.log_pos htStrict
    have hdenPos : 0 < 1024 * Real.log t :=
      mul_pos (by norm_num) hlogPos
    have hlogTilt :
        Real.log (dimensionOneRosserSeedTilt t) =
          Real.log t - Real.log 1024 - Real.log (Real.log t) := by
      unfold dimensionOneRosserSeedTilt
      rw [Real.log_div htPos.ne' hdenPos.ne',
        Real.log_mul (by norm_num) hlogPos.ne']
      ring
    have hlogLog : Real.log (Real.log t) <= Real.log t - 1 :=
      Real.log_le_sub_one_of_pos hlogPos
    have hlogNumeral : Real.log (1024 : Real) <= 1023 := by
      convert Real.log_le_sub_one_of_pos
        (show (0 : Real) < 1024 by norm_num) using 1; norm_num
    have hcoefficient :
        4 - Real.log (dimensionOneRosserSeedTilt t) <= 1026 := by
      rw [hlogTilt]
      linarith
    have hexponent :
        t * (4 - Real.log (dimensionOneRosserSeedTilt t)) <=
          1026 * dimensionOneRosserSecondSplice := by
      calc
        t * (4 - Real.log (dimensionOneRosserSeedTilt t)) <=
            t * 1026 := mul_le_mul_of_nonneg_left hcoefficient htPos.le
        _ <= dimensionOneRosserSecondSplice * 1026 :=
          mul_le_mul_of_nonneg_right htU (by norm_num)
        _ = 1026 * dimensionOneRosserSecondSplice := by ring
    unfold dimensionOneRosserSeedEnvelope
      dimensionOneRosserBoundedSeedCeiling
    exact Real.exp_le_exp.mpr hexponent

private theorem boundedSeedCeiling_eq_constant_mul_floor :
    dimensionOneRosserBoundedSeedCeiling =
      (dimensionOneRosserBoundedSeedConstant / 4) *
        dimensionOneRosserBoundedDelayFloor := by
  unfold dimensionOneRosserBoundedSeedConstant
  field_simp [dimensionOneRosserBoundedDelayFloor_pos.ne']

/-- On the full shifted-plus compact domain, the seed envelope consumes at
most one quarter of the common delay coefficient. -/
theorem dimensionOneRosserSeedEnvelope_le_boundedPlus
    {t : Real} (ht : 1 <= t)
    (htU : t <= dimensionOneRosserSecondSplice) :
    dimensionOneRosserSeedEnvelope t <=
      (dimensionOneRosserBoundedSeedConstant / 4) *
        dimensionOneDelayScaledPlus t := by
  have hFloor : dimensionOneRosserBoundedDelayFloor <=
      dimensionOneDelayScaledPlus t := by
    calc
      dimensionOneRosserBoundedDelayFloor <=
          dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice :=
        min_le_left _ _
      _ <= dimensionOneDelayScaledPlus t :=
        dimensionOneDelayScaledPlus_antitoneOn
          (show t ∈ Ici (1 : Real) by exact ht)
          (show dimensionOneRosserSecondSplice ∈ Ici (1 : Real) by
            exact one_le_dimensionOneRosserSecondSplice)
          htU
  calc
    dimensionOneRosserSeedEnvelope t <=
        dimensionOneRosserBoundedSeedCeiling :=
      dimensionOneRosserSeedEnvelope_le_boundedCeiling ht htU
    _ = (dimensionOneRosserBoundedSeedConstant / 4) *
        dimensionOneRosserBoundedDelayFloor :=
      boundedSeedCeiling_eq_constant_mul_floor
    _ <= (dimensionOneRosserBoundedSeedConstant / 4) *
        dimensionOneDelayScaledPlus t :=
      mul_le_mul_of_nonneg_left hFloor
        (by positivity [one_le_dimensionOneRosserBoundedSeedConstant])

/-- On the natural minus compact domain, the seed envelope consumes at most
one quarter of the common delay coefficient. -/
theorem dimensionOneRosserSeedEnvelope_le_boundedMinus
    {t : Real} (ht : 2 <= t)
    (htU : t <= dimensionOneRosserSecondSplice) :
    dimensionOneRosserSeedEnvelope t <=
      (dimensionOneRosserBoundedSeedConstant / 4) *
        dimensionOneDelayScaledMinus t := by
  have hFloor : dimensionOneRosserBoundedDelayFloor <=
      dimensionOneDelayScaledMinus t := by
    calc
      dimensionOneRosserBoundedDelayFloor <=
          dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice :=
        min_le_right _ _
      _ <= dimensionOneDelayScaledMinus t :=
        dimensionOneDelayScaledMinus_antitoneOn
          (show t ∈ Ici (2 : Real) by exact ht)
          (show dimensionOneRosserSecondSplice ∈ Ici (2 : Real) by
            change 2 <= dimensionOneRosserSecondSplice
            linarith [one_le_dimensionOneRosserSecondSplice])
          htU
  calc
    dimensionOneRosserSeedEnvelope t <=
        dimensionOneRosserBoundedSeedCeiling :=
      dimensionOneRosserSeedEnvelope_le_boundedCeiling (by linarith) htU
    _ = (dimensionOneRosserBoundedSeedConstant / 4) *
        dimensionOneRosserBoundedDelayFloor :=
      boundedSeedCeiling_eq_constant_mul_floor
    _ <= (dimensionOneRosserBoundedSeedConstant / 4) *
        dimensionOneDelayScaledMinus t :=
      mul_le_mul_of_nonneg_left hFloor
        (by positivity [one_le_dimensionOneRosserBoundedSeedConstant])

end PrimesRestrictedDigits
