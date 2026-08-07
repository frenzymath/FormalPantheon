import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanAbelEstimate

/-!
# Conductor conclusion for the Vaughan primitive mean estimate

This file combines the natural-upper Abel estimate with SEM-428's
`5 * log x` conductor reduction. The resulting logarithmic factor is the
equation-(1.2) power `(log x)^(9/2)`.

Source: `AkbaryHambrook2013v2`, Theorem 1.3 and Section 7, printed p. 25.
Semantic review: `SEM-461`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The source factor `(log x)^(9/2)`, represented using an integer power and
a nonnegative square root. -/
noncomputable def vaughanPrimitiveMeanEquationOneTwoLogPower
    (x : ℕ) : ℝ :=
  Real.log (x : ℝ) ^ 4 * Real.sqrt (Real.log (x : ℝ))

theorem vaughanPrimitiveMeanEquationOneTwoLogPower_nonneg (x : ℕ) :
    0 ≤ vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  unfold vaughanPrimitiveMeanEquationOneTwoLogPower
  positivity

theorem five_log_mul_equationOneOneLogPower (x : ℕ) :
    (5 * Real.log (x : ℝ)) *
        vaughanPrimitiveMeanEquationOneOneLogPower x =
      5 * vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  unfold vaughanPrimitiveMeanEquationOneOneLogPower
    vaughanPrimitiveMeanEquationOneTwoLogPower
  ring

noncomputable local instance
    roughModulusAboveDecidableForVaughanPrimitiveMeanConductorConclusion
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- Generic conductor conclusion after inserting the equation-(1.1)
cumulative estimate into the exact Abel expression. -/
theorem sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_abelEnvelope_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) ≤
      (5 * vaughanPrimitiveMeanEquationOneOneConstant A) *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  have hlog : 0 ≤ 5 * Real.log (x : ℝ) := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ x by omega)
  have habel :=
    primitiveRawMeanValueAbelExpression_natUpper_le_envelope_of_psi
      hA hpsi hx hQ1 hQ hQsqrt
  calc
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            inducingPrimitiveCenteredEndpointMaximum x q χ) ≤
        (5 * Real.log (x : ℝ)) *
          ((Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
            Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
              ∫ t in Set.Ioc Q1 (Q : ℝ),
                primitiveRawMeanValueCumulative x t / t ^ 2) :=
      sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_five_log_abel
        x Q Q1 hx hQsqrt hQ1 hQ
    _ ≤ (5 * Real.log (x : ℝ)) *
        (vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
            vaughanPrimitiveMeanEquationOneOneLogPower x) :=
      mul_le_mul_of_nonneg_left habel hlog
    _ = vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          ((5 * Real.log (x : ℝ)) *
            vaughanPrimitiveMeanEquationOneOneLogPower x) := by ring
    _ = vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          (5 * vaughanPrimitiveMeanEquationOneTwoLogPower x) := by
      rw [five_log_mul_equationOneOneLogPower]
    _ = (5 * vaughanPrimitiveMeanEquationOneOneConstant A) *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by ring

/-- Unconditional conductor conclusion using Mathlib's verified Chebyshev
constant. -/
theorem sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_abelEnvelope
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) ≤
      (5 * vaughanPrimitiveMeanEquationOneOneConstant
          (Real.log 4 + 4)) *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  refine
    sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_abelEnvelope_of_psi
      (A := Real.log 4 + 4) ?_ ?_ x Q Q1 hx hQsqrt hQ1 hQ
  · have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz

end

end BoundedGaps.Maynard
