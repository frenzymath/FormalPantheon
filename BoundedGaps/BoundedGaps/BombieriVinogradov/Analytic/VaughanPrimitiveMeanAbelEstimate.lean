import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanAbelIntegrals
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanEquationOneOne
import Mathlib.MeasureTheory.Function.Floor

/-!
# Abel estimate for the Vaughan primitive mean bound

This file inserts the continuous equation-(1.1) cumulative estimate into the
positive upper-boundary and integral terms of the exact SEM-428 Abel
expression. The negative lower boundary remains visible before it is
discarded using nonnegativity.

Source: `AkbaryHambrook2013v2`, Theorem 1.2 and Section 7, printed p. 25.
Semantic review: `SEM-461`.
-/

namespace BoundedGaps.Maynard

open MeasureTheory

noncomputable section

/-- The floor-indexed cumulative primitive mean is a measurable step
function. -/
theorem primitiveRawMeanValueCumulative_measurable (x : ℕ) :
    Measurable (primitiveRawMeanValueCumulative x) := by
  unfold primitiveRawMeanValueCumulative
  change Measurable
    ((fun n : ℕ ↦ ∑ q ∈ Finset.Icc 0 n,
      primitiveRawMeanValueWeight x q) ∘ (Nat.floor : ℝ → ℕ))
  exact
    (measurable_of_countable
      (fun n : ℕ ↦ ∑ q ∈ Finset.Icc 0 n, primitiveRawMeanValueWeight x q)).comp
        (Nat.measurable_floor (R := ℝ))

private theorem primitiveRawMeanValueCumulative_div_sq_le_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x : ℕ} (hx : 4 ≤ x) {Q1 Q t : ℝ}
    (hQ1 : 1 ≤ Q1)
    (hQsqrt : Q ≤ Real.sqrt (x : ℝ)) (ht : t ∈ Set.Ioc Q1 Q) :
    primitiveRawMeanValueCumulative x t / t ^ 2 ≤
      (vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOneLogPower x) *
        (vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2) := by
  have ht0 : 0 ≤ t := (zero_le_one.trans hQ1).trans ht.1.le
  have htsqrt : t ≤ Real.sqrt (x : ℝ) := ht.2.trans hQsqrt
  have hcumulative :=
    primitiveRawMeanValueCumulative_le_equationOneOne_of_psi
      hA hpsi hx ht0 htsqrt
  calc
    primitiveRawMeanValueCumulative x t / t ^ 2 ≤
        (vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x t *
            vaughanPrimitiveMeanEquationOneOneLogPower x) / t ^ 2 :=
      div_le_div_of_nonneg_right hcumulative (sq_nonneg t)
    _ = (vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOneLogPower x) *
        (vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2) := by
      ring

private theorem integrableOn_scaled_vaughanPrimitiveMeanPolynomial_div_sq
    (A : ℝ) (x : ℕ) {Q1 Q : ℝ} (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    IntegrableOn
      (fun t ↦ (vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOneLogPower x) *
        (vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2))
      (Set.Ioc Q1 Q) := by
  have hbase : IntegrableOn
      (fun t ↦ vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2)
      (Set.Ioc Q1 Q) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hQ).mp
      (vaughanPrimitiveMeanPolynomial_div_sq_intervalIntegrable x hQ1 hQ)
  exact hbase.const_mul _

/-- The cumulative quotient is integrable on every positive source interval.
The proof uses both measurability of the floor step and norm domination by the
continuous polynomial quotient. -/
theorem integrableOn_primitiveRawMeanValueCumulative_div_sq_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x : ℕ} (hx : 4 ≤ x) {Q1 Q : ℝ}
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q)
    (hQsqrt : Q ≤ Real.sqrt (x : ℝ)) :
    IntegrableOn
      (fun t ↦ primitiveRawMeanValueCumulative x t / t ^ 2)
      (Set.Ioc Q1 Q) := by
  have hscaled :=
    integrableOn_scaled_vaughanPrimitiveMeanPolynomial_div_sq
      A x hQ1 hQ
  have hmeasurable : Measurable
      (fun t ↦ primitiveRawMeanValueCumulative x t / t ^ 2) :=
    (primitiveRawMeanValueCumulative_measurable x).div
      (measurable_id.pow_const 2)
  apply Integrable.mono_nonneg hscaled
  · exact hmeasurable.aestronglyMeasurable.restrict
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun t _ ↦
      div_nonneg (primitiveRawMeanValueCumulative_nonneg x t) (sq_nonneg t)
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun _ ht ↦
      primitiveRawMeanValueCumulative_div_sq_le_of_psi
        hA hpsi hx hQ1 hQsqrt ht

/-- Integrate the continuous equation-(1.1) pointwise envelope over a literal
real Abel interval. -/
theorem integral_primitiveRawMeanValueCumulative_div_sq_le_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x : ℕ} (hx : 4 ≤ x) {Q1 Q : ℝ}
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q)
    (hQsqrt : Q ≤ Real.sqrt (x : ℝ)) :
    (∫ t in Set.Ioc Q1 Q,
      primitiveRawMeanValueCumulative x t / t ^ 2) ≤
      (vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOneLogPower x) *
        ∫ t in Set.Ioc Q1 Q,
          vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2 := by
  have hcumulative :=
    integrableOn_primitiveRawMeanValueCumulative_div_sq_of_psi
      hA hpsi hx hQ1 hQ hQsqrt
  have hscaled :=
    integrableOn_scaled_vaughanPrimitiveMeanPolynomial_div_sq
      A x hQ1 hQ
  calc
    (∫ t in Set.Ioc Q1 Q,
        primitiveRawMeanValueCumulative x t / t ^ 2) ≤
        ∫ t in Set.Ioc Q1 Q,
          (vaughanPrimitiveMeanEquationOneOneConstant A *
              vaughanPrimitiveMeanEquationOneOneLogPower x) *
            (vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2) := by
      apply integral_mono_ae hcumulative hscaled
      exact ae_restrict_of_forall_mem measurableSet_Ioc fun _ ht ↦
        primitiveRawMeanValueCumulative_div_sq_le_of_psi
          hA hpsi hx hQ1 hQsqrt ht
    _ = (vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOneLogPower x) *
        ∫ t in Set.Ioc Q1 Q,
          vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2 := by
      rw [integral_const_mul]

/-- The literal negative lower Abel boundary is nonpositive. -/
theorem primitiveRawMeanValue_lowerBoundary_nonpos
    (x : ℕ) {Q1 : ℝ} (hQ1 : 0 ≤ Q1) :
    -(Q1⁻¹ * primitiveRawMeanValueCumulative x Q1) ≤ 0 := by
  exact neg_nonpos.mpr
    (mul_nonneg (inv_nonneg.mpr hQ1)
      (primitiveRawMeanValueCumulative_nonneg x Q1))

/-- The sign-auditable natural-upper Abel estimate before discarding the
negative cumulative boundary or the two negative polynomial endpoint terms. -/
theorem primitiveRawMeanValueAbelExpression_natUpper_le_sharp_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x Q : ℕ} (hx : 4 ≤ x) {Q1 : ℝ}
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ))
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
        Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
        ∫ t in Set.Ioc Q1 (Q : ℝ),
          primitiveRawMeanValueCumulative x t / t ^ 2 ≤
      vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanAbelSharpPolynomial x Q1 (Q : ℝ) *
          vaughanPrimitiveMeanEquationOneOneLogPower x -
        Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 := by
  have hQ0 : 0 ≤ (Q : ℝ) := (zero_le_one.trans hQ1).trans hQ
  have hendpointBound :=
    primitiveRawMeanValueCumulative_le_equationOneOne_of_psi
      hA hpsi hx hQ0 hQsqrt
  have hendpoint :
      (Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q ≤
        (Q : ℝ)⁻¹ *
          (vaughanPrimitiveMeanEquationOneOneConstant A *
            vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
              vaughanPrimitiveMeanEquationOneOneLogPower x) :=
    mul_le_mul_of_nonneg_left hendpointBound (inv_nonneg.mpr hQ0)
  have hintegral :=
    integral_primitiveRawMeanValueCumulative_div_sq_le_of_psi
      hA hpsi hx hQ1 hQ hQsqrt
  calc
    (Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
          Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
          ∫ t in Set.Ioc Q1 (Q : ℝ),
            primitiveRawMeanValueCumulative x t / t ^ 2 ≤
        (Q : ℝ)⁻¹ *
            (vaughanPrimitiveMeanEquationOneOneConstant A *
              vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
                vaughanPrimitiveMeanEquationOneOneLogPower x) -
          Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
          (vaughanPrimitiveMeanEquationOneOneConstant A *
              vaughanPrimitiveMeanEquationOneOneLogPower x) *
            ∫ t in Set.Ioc Q1 (Q : ℝ),
              vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2 := by
      linarith
    _ = vaughanPrimitiveMeanEquationOneOneConstant A *
          ((Q : ℝ)⁻¹ *
              vaughanPrimitiveMeanEquationOneOnePolynomial x Q +
            ∫ t in Set.Ioc Q1 (Q : ℝ),
              vaughanPrimitiveMeanEquationOneOnePolynomial x t / t ^ 2) *
          vaughanPrimitiveMeanEquationOneOneLogPower x -
        Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 := by
      ring
    _ = vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanAbelSharpPolynomial x Q1 (Q : ℝ) *
          vaughanPrimitiveMeanEquationOneOneLogPower x -
        Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 := by
      rw [inv_mul_polynomial_add_integral_eq_abelSharp x hQ1 hQ]

/-- Coarse natural-upper Abel estimate with the lower boundary and negative
polynomial endpoint terms safely discarded. -/
theorem primitiveRawMeanValueAbelExpression_natUpper_le_envelope_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x Q : ℕ} (hx : 4 ≤ x) {Q1 : ℝ}
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ))
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
        Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
        ∫ t in Set.Ioc Q1 (Q : ℝ),
          primitiveRawMeanValueCumulative x t / t ^ 2 ≤
      vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hsharp :=
    primitiveRawMeanValueAbelExpression_natUpper_le_sharp_of_psi
      hA hpsi hx hQ1 hQ hQsqrt
  have hlower := primitiveRawMeanValue_lowerBoundary_nonpos x
    (zero_le_one.trans hQ1)
  have henvelope :=
    vaughanPrimitiveMeanAbelSharpPolynomial_le_envelope x hQ1 hQ
  have hconstant : 0 ≤ vaughanPrimitiveMeanEquationOneOneConstant A :=
    vaughanPrimitiveMeanEquationOneOneConstant_nonneg A
  have hlogPower : 0 ≤ vaughanPrimitiveMeanEquationOneOneLogPower x :=
    vaughanPrimitiveMeanEquationOneOneLogPower_nonneg x
  calc
    (Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
          Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
          ∫ t in Set.Ioc Q1 (Q : ℝ),
            primitiveRawMeanValueCumulative x t / t ^ 2 ≤
        vaughanPrimitiveMeanEquationOneOneConstant A *
            vaughanPrimitiveMeanAbelSharpPolynomial x Q1 (Q : ℝ) *
            vaughanPrimitiveMeanEquationOneOneLogPower x -
          Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 := hsharp
    _ ≤ vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanAbelSharpPolynomial x Q1 (Q : ℝ) *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
      linarith
    _ ≤ vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left henvelope hconstant) hlogPower

/-- Unconditional natural-upper Abel estimate using Mathlib's verified
Chebyshev constant. -/
theorem primitiveRawMeanValueAbelExpression_natUpper_le_envelope
    {x Q : ℕ} (hx : 4 ≤ x) {Q1 : ℝ}
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ))
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
        Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
        ∫ t in Set.Ioc Q1 (Q : ℝ),
          primitiveRawMeanValueCumulative x t / t ^ 2 ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  apply primitiveRawMeanValueAbelExpression_natUpper_le_envelope_of_psi
    (A := Real.log 4 + 4)
  · have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz
  · exact hx
  · exact hQ1
  · exact hQ
  · exact hQsqrt

end

end BoundedGaps.Maynard
