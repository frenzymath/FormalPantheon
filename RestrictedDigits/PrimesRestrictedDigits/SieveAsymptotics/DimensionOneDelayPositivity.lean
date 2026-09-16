import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayContraction

/-!
# Positivity and comparison for the dimension-one delay functions

The strict half-contraction implies positivity, quarter/three-quarter bounds, and Iwaniec's
Eq. (6.3) with explicit factor three. See `IWANIEC-ROSSER-SIEVE-1980`, printed pp. 189--191.
-/

namespace PrimesRestrictedDigits

theorem dimensionOneDelaySum_pos {s : Real} (hs0 : 0 < s) :
    0 < dimensionOneDelaySum s := by
  have h := dimensionOneDelay_contraction hs0
  linarith [abs_nonneg (dimensionOneDelayDifference s)]

theorem dimensionOneDelayQPlus_bounds {s : Real} (hs0 : 0 < s) :
    dimensionOneDelaySum s / 4 < dimensionOneDelayQPlus s ∧
      dimensionOneDelayQPlus s < 3 * dimensionOneDelaySum s / 4 := by
  have h := dimensionOneDelay_contraction hs0
  rw [abs_lt] at h
  unfold dimensionOneDelayDifference dimensionOneDelaySum at h
  unfold dimensionOneDelaySum
  constructor <;> linarith

theorem dimensionOneDelayQMinus_bounds {s : Real} (hs0 : 0 < s) :
    dimensionOneDelaySum s / 4 < dimensionOneDelayQMinus s ∧
      dimensionOneDelayQMinus s < 3 * dimensionOneDelaySum s / 4 := by
  have h := dimensionOneDelay_contraction hs0
  rw [abs_lt] at h
  unfold dimensionOneDelayDifference dimensionOneDelaySum at h
  unfold dimensionOneDelaySum
  constructor <;> linarith

theorem dimensionOneDelayQPlus_pos {s : Real} (hs0 : 0 < s) :
    0 < dimensionOneDelayQPlus s := by
  linarith [(dimensionOneDelayQPlus_bounds hs0).1,
    dimensionOneDelaySum_pos hs0]

theorem dimensionOneDelayQMinus_pos {s : Real} (hs0 : 0 < s) :
    0 < dimensionOneDelayQMinus s := by
  linarith [(dimensionOneDelayQMinus_bounds hs0).1,
    dimensionOneDelaySum_pos hs0]

theorem dimensionOneDelayQPlus_lt_three_mul_QMinus
    {s : Real} (hs0 : 0 < s) :
    dimensionOneDelayQPlus s < 3 * dimensionOneDelayQMinus s := by
  have h := dimensionOneDelay_contraction hs0
  rw [abs_lt] at h
  unfold dimensionOneDelayDifference dimensionOneDelaySum at h
  linarith

theorem dimensionOneDelayQMinus_lt_three_mul_QPlus
    {s : Real} (hs0 : 0 < s) :
    dimensionOneDelayQMinus s < 3 * dimensionOneDelayQPlus s := by
  have h := dimensionOneDelay_contraction hs0
  rw [abs_lt] at h
  unfold dimensionOneDelayDifference dimensionOneDelaySum at h
  linarith

end PrimesRestrictedDigits
