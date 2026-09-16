import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayAveraging
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayPositivity

/-!
# Unweighted pairing for the dimension-one delay sum

The corrected weighted averaging identity, positivity of the delay sum, and monotonicity of
its conjugate weight give a weak unweighted interval estimate. See
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 189--190.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

/-- The conjugate-weight averaging identity controls the unweighted mass on
the preceding unit interval. This is not a lower asymptotic for the delay sum. -/
theorem dimensionOneDelaySum_integral_le {s : Real} (hs : 3 <= s) :
    (∫ x in s - 1..s, dimensionOneDelaySum x) <=
      s * dimensionOneDelaySum s := by
  have hWindowPositive : Icc (s - 1) s ⊆ Ioi (0 : Real) := by
    intro x hx
    change 0 < x
    linarith [hx.1]
  have hSumContinuous : ContinuousOn dimensionOneDelaySum (Icc (s - 1) s) :=
    dimensionOneDelaySum_continuousOn.mono hWindowPositive
  have hGShiftContinuous : Continuous (fun x : Real =>
      dimensionOneDelayConjugateWeight (x + 1)) :=
    dimensionOneDelayConjugateWeight_continuous.comp
      (continuous_id.add continuous_const)
  have hLeftInt : IntervalIntegrable (fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight s)
      volume (s - 1) s :=
    (hSumContinuous.mul continuousOn_const).intervalIntegrable_of_Icc
      (by linarith)
  have hRightInt : IntervalIntegrable (fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      volume (s - 1) s :=
    (hSumContinuous.mul hGShiftContinuous.continuousOn).intervalIntegrable_of_Icc
      (by linarith)
  have hPointwise : ∀ x ∈ Icc (s - 1) s,
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight s <=
        dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hWeight : dimensionOneDelayConjugateWeight s <=
        dimensionOneDelayConjugateWeight (x + 1) :=
      dimensionOneDelayConjugateWeight_monoOn
        (by change 1 <= s; linarith)
        (by change 1 <= x + 1; linarith [hx.1])
        (by linarith [hx.1])
    exact mul_le_mul_of_nonneg_left hWeight (dimensionOneDelaySum_pos hx0).le
  have hIntegral := intervalIntegral.integral_mono_on
    (by linarith : s - 1 <= s) hLeftInt hRightInt hPointwise
  have hProduct :
      (∫ x in s - 1..s, dimensionOneDelaySum x) *
          dimensionOneDelayConjugateWeight s <=
        (s * dimensionOneDelaySum s) *
          dimensionOneDelayConjugateWeight s := by
    calc
      (∫ x in s - 1..s, dimensionOneDelaySum x) *
          dimensionOneDelayConjugateWeight s =
          ∫ x in s - 1..s,
            dimensionOneDelaySum x * dimensionOneDelayConjugateWeight s := by
        rw [intervalIntegral.integral_mul_const]
      _ <= ∫ x in s - 1..s,
          dimensionOneDelaySum x *
            dimensionOneDelayConjugateWeight (x + 1) := hIntegral
      _ = (s * dimensionOneDelaySum s) *
          dimensionOneDelayConjugateWeight s :=
        (dimensionOneDelaySum_averaging hs).symm
  exact (mul_le_mul_iff_of_pos_right
    (dimensionOneDelayConjugateWeight_pos (by linarith : 2 <= s))).mp hProduct

end PrimesRestrictedDigits
