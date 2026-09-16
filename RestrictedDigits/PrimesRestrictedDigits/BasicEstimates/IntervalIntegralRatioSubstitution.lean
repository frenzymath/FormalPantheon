import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

/-!
Reciprocal-affine changes of variables used by the directed Section 6 integral
certificates.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

private theorem intervalIntegral_comp_mul_neg_deriv'
    {a b : Real} {f j g : Real -> Real}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (-j x) x)
    (hj : ContinuousOn j (uIcc a b))
    (hg : ContinuousOn g (f '' uIcc a b)) :
    (∫ x in a..b, g (f x) * j x) =
      ∫ y in f b..f a, g y := by
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (f := f) (f' := fun x => -j x) (g := g) hf hj.neg hg
  calc
    (∫ x in a..b, g (f x) * j x) =
        -(∫ x in a..b, (g ∘ f) x * (-j x)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Function.comp_apply]
      ring
    _ = -(∫ y in f a..f b, g y) := congrArg Neg.neg hsubst
    _ = ∫ y in f b..f a, g y := by
      rw [intervalIntegral.integral_symm]
      simp

/-- Increasing fractional-linear substitution with its signed Jacobian. -/
theorem intervalIntegral_const_div_const_sub
    {a b c d : Real} {g : Real -> Real}
    (hden : ∀ x ∈ uIcc a b, d - x ≠ 0)
    (hg : ContinuousOn g
      ((fun x : Real => c / (d - x)) '' uIcc a b)) :
    (∫ x in a..b, g (c / (d - x)) * (c / (d - x) ^ 2)) =
      ∫ r in c / (d - a)..c / (d - b), g r := by
  have hf : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : Real => c / (d - y)) (c / (d - x) ^ 2) x := by
    intro x hx
    simpa using (HasDerivAt.fun_div (hasDerivAt_const x c)
      ((hasDerivAt_const x d).sub (hasDerivAt_id x)) (hden x hx))
  have hj : ContinuousOn (fun x : Real => c / (d - x) ^ 2) (uIcc a b) :=
    continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun x hx => pow_ne_zero 2 (hden x hx))
  simpa only [Function.comp_apply] using
    intervalIntegral.integral_comp_mul_deriv' hf hj hg

/-- Decreasing reciprocal-affine substitution with reversed target endpoints. -/
theorem intervalIntegral_const_div_sub_const
    {a b c k : Real} {g : Real -> Real}
    (hden : ∀ x ∈ uIcc a b, x ≠ 0)
    (hg : ContinuousOn g
      ((fun x : Real => c / x - k) '' uIcc a b)) :
    (∫ x in a..b, g (c / x - k) * (c / x ^ 2)) =
      ∫ r in c / b - k..c / a - k, g r := by
  have hf : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : Real => c / y - k) (-(c / x ^ 2)) x := by
    intro x hx
    simpa [neg_div] using ((HasDerivAt.fun_div (hasDerivAt_const x c)
      (hasDerivAt_id x) (hden x hx)).sub_const k
    )
  have hj : ContinuousOn (fun x : Real => c / x ^ 2) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (hden x hx))
  exact intervalIntegral_comp_mul_neg_deriv' hf hj hg

end

end PrimesRestrictedDigits
