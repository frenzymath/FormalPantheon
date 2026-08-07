import BoundedGaps.BombieriVinogradov.Analytic.CenteredProgressionCorrection
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanConductorConclusion

/-!
# Rough-modulus weighted equation (1.2)

This file composes the coefficient-one elementary progression correction with
SEM-461's centered inducing-character estimate. The resulting constant is the
transparent project replacement `1 + 5 * C(A)`.

Source: `AkbaryHambrook2013v2`, Theorem 1.3 and Section 7, printed pp. 3 and
24--25. Semantic review: `SEM-462`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

noncomputable local instance
    roughModulusAboveDecidableForVaughanPrimitiveMeanProgressionConclusion
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- The safe project coefficient for the full rough-modulus equation-(1.2)
bound. It is not identified with Akbary--Hambrook's explicit `c1`. -/
noncomputable def vaughanPrimitiveMeanEquationOneTwoConstant
    (A : ℝ) : ℝ :=
  1 + 5 * vaughanPrimitiveMeanEquationOneOneConstant A

/-- The source's elementary `Q * log(Q*x)^2` correction is absorbed by one
copy of the equation-(1.2) envelope and its exact `9/2` logarithmic power. -/
theorem vaughanPrimitiveMeanElementaryCorrection_le_abelEnvelope
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ)) :
    (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 ≤
      vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
        vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := zero_lt_one.trans_le hxone
  have hQone : (1 : ℝ) ≤ (Q : ℝ) := hQ1.trans hQ
  have hQnonneg : (0 : ℝ) ≤ (Q : ℝ) := zero_le_one.trans hQone
  have hsqrt_le_x : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hxpos.le
    · nlinarith
  have hQleX : (Q : ℝ) ≤ (x : ℝ) := hQsqrt.trans hsqrt_le_x
  have hprod_one : (1 : ℝ) ≤ ((Q * x : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    nlinarith
  have hprod_le : ((Q * x : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 := by
    rw [Nat.cast_mul]
    nlinarith
  have hlogX_nonneg : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hxone
  have hlogProd_nonneg : 0 ≤ Real.log ((Q * x : ℕ) : ℝ) :=
    Real.log_nonneg hprod_one
  have hlogProd_le :
      Real.log ((Q * x : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    calc
      Real.log ((Q * x : ℕ) : ℝ) ≤ Real.log ((x : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) hprod_le
      _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogSq :
      Real.log ((Q * x : ℕ) : ℝ) ^ 2 ≤
        4 * Real.log (x : ℝ) ^ 2 := by
    have hsquares := (sq_le_sq₀ hlogProd_nonneg (by positivity :
      0 ≤ 2 * Real.log (x : ℝ))).2 hlogProd_le
    nlinarith
  have hlogOne : 1 ≤ Real.log (x : ℝ) := one_le_log_natCast hx
  have hlogSq_le_fourth :
      Real.log (x : ℝ) ^ 2 ≤ Real.log (x : ℝ) ^ 4 := by
    calc
      Real.log (x : ℝ) ^ 2 = Real.log (x : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (x : ℝ) ^ 2 * Real.log (x : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ hlogOne)
          (sq_nonneg (Real.log (x : ℝ)))
      _ = Real.log (x : ℝ) ^ 4 := by ring
  have hsqrtLogOne : 1 ≤ Real.sqrt (Real.log (x : ℝ)) :=
    Real.one_le_sqrt.mpr hlogOne
  have hlogSq_le_L9 :
      Real.log (x : ℝ) ^ 2 ≤
        vaughanPrimitiveMeanEquationOneTwoLogPower x := by
    unfold vaughanPrimitiveMeanEquationOneTwoLogPower
    calc
      Real.log (x : ℝ) ^ 2 ≤ Real.log (x : ℝ) ^ 4 := hlogSq_le_fourth
      _ = Real.log (x : ℝ) ^ 4 * 1 := by ring
      _ ≤ Real.log (x : ℝ) ^ 4 *
          Real.sqrt (Real.log (x : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsqrtLogOne (by positivity)
  have hsqrtXOne : 1 ≤ Real.sqrt (x : ℝ) := Real.one_le_sqrt.mpr hxone
  have hL9nonneg := vaughanPrimitiveMeanEquationOneTwoLogPower_nonneg x
  have hlogSq_le_sqrt_L9 :
      Real.log (x : ℝ) ^ 2 ≤ Real.sqrt (x : ℝ) *
        vaughanPrimitiveMeanEquationOneTwoLogPower x := by
    calc
      Real.log (x : ℝ) ^ 2 ≤
          vaughanPrimitiveMeanEquationOneTwoLogPower x := hlogSq_le_L9
      _ = 1 * vaughanPrimitiveMeanEquationOneTwoLogPower x := by ring
      _ ≤ Real.sqrt (x : ℝ) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x :=
        mul_le_mul_of_nonneg_right hsqrtXOne hL9nonneg
  have hQ1pos : 0 < Q1 := zero_lt_one.trans_le hQ1
  have hexpQ : (Q : ℝ) ≤ Real.exp 1 * (Q : ℝ) := by
    calc
      (Q : ℝ) = 1 * (Q : ℝ) := by ring
      _ ≤ Real.exp 1 * (Q : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.one_le_exp (by norm_num)) hQnonneg
  have hratioOne : 1 ≤ Real.exp 1 * (Q : ℝ) / Q1 := by
    apply (le_div_iff₀ hQ1pos).2
    simpa using hQ.trans hexpQ
  have hlogRatio : 0 ≤ Real.log (Real.exp 1 * (Q : ℝ) / Q1) :=
    Real.log_nonneg hratioOne
  have hcuberoot := vaughanCubeRoot_nonneg x
  have hfirst : 0 ≤ 4 * (x : ℝ) / Q1 := by positivity
  have hthird :
      0 ≤ 18 * vaughanCubeRoot x ^ 2 * Real.sqrt (Q : ℝ) := by
    positivity
  have hfourth :
      0 ≤ 5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
        Real.log (Real.exp 1 * (Q : ℝ) / Q1) := by
    positivity
  have hcoefficient :
      4 * Real.sqrt (x : ℝ) * (Q : ℝ) ≤
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q := by
    unfold vaughanPrimitiveMeanAbelEnvelope
    linarith
  calc
    (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 ≤
        (Q : ℝ) * (4 * Real.log (x : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlogSq hQnonneg
    _ ≤ (Q : ℝ) *
        (4 * (Real.sqrt (x : ℝ) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x)) := by
      gcongr
    _ = (4 * Real.sqrt (x : ℝ) * (Q : ℝ)) *
        vaughanPrimitiveMeanEquationOneTwoLogPower x := by ring
    _ ≤ vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
        vaughanPrimitiveMeanEquationOneTwoLogPower x :=
      mul_le_mul_of_nonneg_right hcoefficient hL9nonneg

/-- Generic equation-(1.2) checkpoint before the elementary correction is
absorbed into the polynomial envelope. -/
theorem
    sum_maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_abelEnvelope_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      maxCenteredProgressionDiscrepancyUpTo x q) ≤
      (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        (5 * vaughanPrimitiveMeanEquationOneOneConstant A) *
          vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
            vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
        maxCenteredProgressionDiscrepancyUpTo x q) ≤
        (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
          ∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
            (q.totient : ℝ)⁻¹ *
              ∑ χ : DirichletCharacter ℂ q,
                inducingPrimitiveCenteredEndpointMaximum x q χ :=
      sum_maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_inducing
        x Q Q1 (by omega)
    _ ≤ (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        (5 * vaughanPrimitiveMeanEquationOneOneConstant A) *
          vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
            vaughanPrimitiveMeanEquationOneTwoLogPower x := by
      exact add_le_add le_rfl
        (sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_abelEnvelope_of_psi
          hA hpsi x Q Q1 hx hQsqrt hQ1 hQ)

/-- Generic full rough-modulus weighted discrepancy bound with the elementary
correction absorbed and the exact project coefficient exposed. -/
theorem sum_maxCenteredProgressionDiscrepancyUpTo_le_equationOneTwo_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      maxCenteredProgressionDiscrepancyUpTo x q) ≤
      vaughanPrimitiveMeanEquationOneTwoConstant A *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  have hpre :=
    sum_maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_abelEnvelope_of_psi
      hA hpsi x Q Q1 hx hQsqrt hQ1 hQ
  have helementary :=
    vaughanPrimitiveMeanElementaryCorrection_le_abelEnvelope
      x Q Q1 hx hQsqrt hQ1 hQ
  calc
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
        maxCenteredProgressionDiscrepancyUpTo x q) ≤
        (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
          (5 * vaughanPrimitiveMeanEquationOneOneConstant A) *
            vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
              vaughanPrimitiveMeanEquationOneTwoLogPower x := hpre
    _ ≤ vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x +
        (5 * vaughanPrimitiveMeanEquationOneOneConstant A) *
          vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
            vaughanPrimitiveMeanEquationOneTwoLogPower x :=
      add_le_add helementary le_rfl
    _ = vaughanPrimitiveMeanEquationOneTwoConstant A *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by
      unfold vaughanPrimitiveMeanEquationOneTwoConstant
      ring

/-- Unconditional rough-modulus weighted discrepancy bound using Mathlib's
verified global Chebyshev constant. -/
theorem sum_maxCenteredProgressionDiscrepancyUpTo_le_equationOneTwo
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      maxCenteredProgressionDiscrepancyUpTo x q) ≤
      vaughanPrimitiveMeanEquationOneTwoConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanAbelEnvelope x Q1 Q *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  refine
    sum_maxCenteredProgressionDiscrepancyUpTo_le_equationOneTwo_of_psi
      (A := Real.log 4 + 4) ?_ ?_ x Q Q1 hx hQsqrt hQ1 hQ
  · have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz

end

end BoundedGaps.Maynard
