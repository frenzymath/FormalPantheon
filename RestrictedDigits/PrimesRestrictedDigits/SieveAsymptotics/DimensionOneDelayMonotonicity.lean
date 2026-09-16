import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayPositivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Monotone.Union

/-!
# Monotonicity of the dimension-one delay sum

The corrected delay sum is strictly decreasing on the positive reals. The proof treats its
initial, middle, and tail branches separately, so it never asserts differentiability at a
seam. See `IWANIEC-ROSSER-SIEVE-1980`, printed p. 191.
-/

open Set

namespace PrimesRestrictedDigits

/-- The corrected sum of the two dimension-one delay functions is strictly
decreasing throughout its positive domain. -/
theorem dimensionOneDelaySum_strictAntiOn :
    StrictAntiOn dimensionOneDelaySum (Ioi 0) := by
  have hInitial : StrictAntiOn dimensionOneDelaySum (Ioc 0 2) := by
    intro x hx y hy hxy
    have hsq : x ^ 2 < y ^ 2 :=
      (sq_lt_sq₀ hx.1.le hy.1.le).2 hxy
    have hinv : (y ^ 2)⁻¹ < (x ^ 2)⁻¹ :=
      (inv_lt_inv₀ (sq_pos_of_pos hy.1) (sq_pos_of_pos hx.1)).2 hsq
    unfold dimensionOneDelaySum dimensionOneDelayQPlus
      dimensionOneDelayQMinus
    rw [dimensionOneDelayScaledPlus_eq_half_of_le
        (s := y) (hy.2.trans (by norm_num)),
      dimensionOneDelayScaledMinus_eq_one_of_le (s := y) hy.2,
      dimensionOneDelayScaledPlus_eq_half_of_le
        (s := x) (hx.2.trans (by norm_num)),
      dimensionOneDelayScaledMinus_eq_one_of_le (s := x) hx.2]
    calc
      (1 / 2 : Real) / y ^ 2 + 1 / y ^ 2 =
          (3 / 2 : Real) * (y ^ 2)⁻¹ := by ring
      _ < (3 / 2 : Real) * (x ^ 2)⁻¹ :=
        mul_lt_mul_of_pos_left hinv (by norm_num)
      _ = (1 / 2 : Real) / x ^ 2 + 1 / x ^ 2 := by ring
  have hMiddle : StrictAntiOn dimensionOneDelaySum (Icc 2 3) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg
      (D := Icc (2 : Real) 3)
      (f' := fun s =>
        (-2 * dimensionOneDelaySum s -
          dimensionOneDelayQPlus (s - 1)) / s)
      (convex_Icc 2 3) ?_ ?_ ?_
    · exact dimensionOneDelaySum_continuousOn.mono fun s hs => by
        change 2 <= s ∧ s <= 3 at hs
        change 0 < s
        linarith [hs.1]
    · intro s hs
      rw [interior_Icc] at hs
      change 2 < s ∧ s < 3 at hs
      exact (dimensionOneDelaySum_hasDerivAt_middle hs.1 hs.2).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      change 2 < s ∧ s < 3 at hs
      apply div_neg_of_neg_of_pos
      · linarith [dimensionOneDelaySum_pos (by linarith : 0 < s),
          dimensionOneDelayQPlus_pos (by linarith : 0 < s - 1)]
      · linarith
  have hTail : StrictAntiOn dimensionOneDelaySum (Ici 3) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg
      (D := Ici (3 : Real))
      (f' := fun s =>
        (-2 * dimensionOneDelaySum s - dimensionOneDelaySum (s - 1)) / s)
      (convex_Ici 3) ?_ ?_ ?_
    · exact dimensionOneDelaySum_continuousOn.mono fun s hs => by
        change 3 <= s at hs
        change 0 < s
        linarith
    · intro s hs
      rw [interior_Ici] at hs
      change 3 < s at hs
      exact (dimensionOneDelaySum_hasDerivAt hs).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      change 3 < s at hs
      apply div_neg_of_neg_of_pos
      · linarith [dimensionOneDelaySum_pos (by linarith : 0 < s),
          dimensionOneDelaySum_pos (by linarith : 0 < s - 1)]
      · linarith
  have hThroughThree : StrictAntiOn dimensionOneDelaySum (Ioc 0 3) := by
    rw [<- Ioc_union_Icc_eq_Ioc (a := (0 : Real)) (b := 2) (c := 3)
      (by norm_num) (by norm_num)]
    exact hInitial.union hMiddle
      (isGreatest_Ioc (by norm_num)) (isLeast_Icc (by norm_num))
  rw [<- Ioc_union_Ici_eq_Ioi (a := (0 : Real)) (b := 3) (by norm_num)]
  exact hThroughThree.union hTail (isGreatest_Ioc (by norm_num)) isLeast_Ici

end PrimesRestrictedDigits
