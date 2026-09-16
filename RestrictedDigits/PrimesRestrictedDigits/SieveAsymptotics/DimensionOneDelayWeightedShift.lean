import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayShiftUpper

/-!
# Weighted reverse shift for the dimension-one delay sum

The corrected averaging identity and opposite monotonicity of its two factors give the
endpoint majorant used in Iwaniec's proof of Lemma 16. See `IWANIEC-ROSSER-SIEVE-1980`,
printed pp. 190--192.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

/-- Majorize the corrected averaging integral by the product of its two
opposite endpoint values. -/
theorem dimensionOneDelaySum_weighted_shift_le {s : Real} (hs : 3 <= s) :
    s * dimensionOneDelaySum s * dimensionOneDelayConjugateWeight s <=
      dimensionOneDelaySum (s - 1) *
        dimensionOneDelayConjugateWeight (s + 1) := by
  have hWindowPositive : Icc (s - 1) s ⊆ Ioi (0 : Real) := by
    intro x hx
    change 0 < x
    linarith [hx.1]
  have hGShiftContinuous : Continuous (fun x : Real =>
      dimensionOneDelayConjugateWeight (x + 1)) :=
    dimensionOneDelayConjugateWeight_continuous.comp
      (continuous_id.add continuous_const)
  have hFContinuous : ContinuousOn (fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      (Icc (s - 1) s) :=
    (dimensionOneDelaySum_continuousOn.mono hWindowPositive).mul
      hGShiftContinuous.continuousOn
  have hFInt : IntervalIntegrable (fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
      volume (s - 1) s :=
    hFContinuous.intervalIntegrable_of_Icc (by linarith)
  have hPointwise : ∀ x ∈ Icc (s - 1) s,
      dimensionOneDelaySum x *
          dimensionOneDelayConjugateWeight (x + 1) <=
        dimensionOneDelaySum (s - 1) *
          dimensionOneDelayConjugateWeight (s + 1) := by
    intro x hx
    have hLeft0 : s - 1 ∈ Ioi (0 : Real) := by
      change 0 < s - 1
      linarith
    have hx0 : x ∈ Ioi (0 : Real) := hWindowPositive hx
    have hSum : dimensionOneDelaySum x <=
        dimensionOneDelaySum (s - 1) :=
      dimensionOneDelaySum_strictAntiOn.antitoneOn hLeft0 hx0 hx.1
    have hWeight : dimensionOneDelayConjugateWeight (x + 1) <=
        dimensionOneDelayConjugateWeight (s + 1) :=
      dimensionOneDelayConjugateWeight_monoOn
        (by change 1 <= x + 1; linarith [hx.1])
        (by change 1 <= s + 1; linarith)
        (by linarith [hx.2])
    exact mul_le_mul hSum hWeight
      (dimensionOneDelayConjugateWeight_pos
        (by linarith [hx.1])).le
      (dimensionOneDelaySum_pos hLeft0).le
  have hIntegral := intervalIntegral.integral_mono_on
    (f := fun x : Real =>
      dimensionOneDelaySum x * dimensionOneDelayConjugateWeight (x + 1))
    (g := fun _ : Real =>
      dimensionOneDelaySum (s - 1) *
        dimensionOneDelayConjugateWeight (s + 1))
    (by linarith : s - 1 <= s) hFInt intervalIntegrable_const hPointwise
  calc
    s * dimensionOneDelaySum s * dimensionOneDelayConjugateWeight s =
        ∫ x in s - 1..s,
          dimensionOneDelaySum x *
            dimensionOneDelayConjugateWeight (x + 1) :=
      dimensionOneDelaySum_averaging hs
    _ <= ∫ _x in s - 1..s,
        dimensionOneDelaySum (s - 1) *
          dimensionOneDelayConjugateWeight (s + 1) := hIntegral
    _ = dimensionOneDelaySum (s - 1) *
        dimensionOneDelayConjugateWeight (s + 1) := by
      rw [intervalIntegral.integral_const]
      ring

/-- The exact polynomial residual in the weighted shift gives a strict
linear reverse comparison. -/
theorem dimensionOneDelaySum_linear_shift_lt {s : Real} (hs : 3 <= s) :
    (s - 2) * dimensionOneDelaySum s <
      dimensionOneDelaySum (s - 1) := by
  have hWeighted := dimensionOneDelaySum_weighted_shift_le hs
  have hs0 : 0 < s := by linarith
  have hResidual : 0 < (s - 1) * dimensionOneDelaySum s :=
    mul_pos (by linarith) (dimensionOneDelaySum_pos hs0)
  have hIdentity :
      s * dimensionOneDelaySum s * dimensionOneDelayConjugateWeight s =
        (s - 2) * dimensionOneDelaySum s *
            dimensionOneDelayConjugateWeight (s + 1) +
          (s - 1) * dimensionOneDelaySum s := by
    unfold dimensionOneDelayConjugateWeight
    ring
  have hProduct :
      (s - 2) * dimensionOneDelaySum s *
          dimensionOneDelayConjugateWeight (s + 1) <
        dimensionOneDelaySum (s - 1) *
          dimensionOneDelayConjugateWeight (s + 1) := by
    calc
      (s - 2) * dimensionOneDelaySum s *
          dimensionOneDelayConjugateWeight (s + 1) <
          s * dimensionOneDelaySum s *
            dimensionOneDelayConjugateWeight s := by
        rw [hIdentity]
        linarith
      _ <= dimensionOneDelaySum (s - 1) *
          dimensionOneDelayConjugateWeight (s + 1) := hWeighted
  exact (mul_lt_mul_iff_of_pos_right
    (dimensionOneDelayConjugateWeight_pos (by linarith : 2 <= s + 1))).mp
      hProduct

end PrimesRestrictedDigits
