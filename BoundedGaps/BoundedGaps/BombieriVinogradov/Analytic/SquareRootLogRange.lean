import BoundedGaps.BombieriVinogradov.Analytic.ReciprocalTotientPrefix
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
# Square-root logarithmic range bridge

This file formalizes the last logarithmic inequality in the reciprocal-
totient chain on Akbary--Hambrook2013v2, Section 7, p. 25. SEM-424's
independently proved constant `4` gives the factor `5 * log x`. The following
source step from centered to raw primitive sums remains separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable local instance roughModulusAboveDecidableForLogRange
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- The strict real logarithmic inequality used at the square-root cutoff. -/
theorem log_exp_mul_sqrt_lt_five_fourths_mul_log
    {x : ℝ} (hx : 4 ≤ x) :
    Real.log (Real.exp 1 * Real.sqrt x) <
      (5 / 4 : ℝ) * Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlogFourLe : Real.log (4 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 := by
    convert Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hlogFour : (4 / 3 : ℝ) < Real.log 4 := by
    calc
      (4 / 3 : ℝ) = 2 * (2 / 3) := by ring
      _ < 2 * Real.log 2 := by nlinarith
      _ = Real.log 4 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        ring
  have hfour : (4 : ℝ) < 3 * Real.log x := by
    nlinarith
  rw [Real.log_mul (Real.exp_ne_zero 1) (Real.sqrt_pos.2 hx0).ne',
    Real.log_exp, Real.log_sqrt hx0.le]
  nlinarith

/-- SEM-424's constant-four prefix is strictly below `5 * log x` whenever
its positive natural cutoff is at most `sqrt x`. -/
theorem four_mul_one_add_log_lt_five_mul_log_of_le_sqrt
    {x K : ℕ} (hx : 4 ≤ x) (hK : 0 < K)
    (hKsqrt : (K : ℝ) ≤ Real.sqrt (x : ℝ)) :
    4 * (1 + Real.log (K : ℝ)) <
      5 * Real.log (x : ℝ) := by
  have hx0 : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hsource := log_exp_mul_sqrt_lt_five_fourths_mul_log
    (show (4 : ℝ) ≤ x by exact_mod_cast hx)
  rw [Real.log_mul (Real.exp_ne_zero 1) (Real.sqrt_pos.2 hx0).ne',
    Real.log_exp, Real.log_sqrt hx0.le] at hsource
  have hK0 : (0 : ℝ) < K := by
    exact_mod_cast hK
  have hlogK : Real.log (K : ℝ) ≤ Real.log (Real.sqrt (x : ℝ)) :=
    Real.log_le_log hK0 hKsqrt
  rw [Real.log_sqrt hx0.le] at hlogK
  nlinarith

/-- Apply the square-root range estimate to the exact natural quotient used
by the positive multiplier prefix. -/
theorem four_mul_one_add_log_natDiv_lt_five_mul_log
    {x Q d : ℕ} (hx : 4 ≤ x) (hd : 0 < d) (hdQ : d ≤ Q)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    4 * (1 + Real.log ((Q / d : ℕ) : ℝ)) <
      5 * Real.log (x : ℝ) := by
  apply four_mul_one_add_log_lt_five_mul_log_of_le_sqrt hx
    (Nat.div_pos hdQ hd)
  have hdivQ : ((Q / d : ℕ) : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast Nat.div_le_self Q d
  exact hdivQ.trans hQsqrt

/-- Replace the exact-quotient logarithmic prefix factors by the common
`5 * log x` factor and pull it outside the conductor sum. -/
theorem sum_conductorRough_logPrefix_le_five_log
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
      (∑ ψ : primitiveCharacters d,
        primitiveCenteredEndpointMaximum x d ψ) *
        ((d.totient : ℝ)⁻¹ *
          (4 * (1 + Real.log ((Q / d : ℕ) : ℝ))))) ≤
      (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
          (d.totient : ℝ)⁻¹ *
            ∑ ψ : primitiveCharacters d,
              primitiveCenteredEndpointMaximum x d ψ := by
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ((d.totient : ℝ)⁻¹ * (5 * Real.log (x : ℝ))) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdIoc := (Finset.mem_filter.mp hdmem).1
      have hdBounds := Finset.mem_Ioc.mp hdIoc
      have hlog := four_mul_one_add_log_natDiv_lt_five_mul_log
        hx hdBounds.1 hdBounds.2 hQsqrt
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left hlog.le
        positivity
      · exact sum_primitiveCenteredEndpointMaximum_nonneg x d
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- Compose SEM-424's product-rough estimate with the common logarithmic
range bound. -/
theorem sum_productRough_factorPairs_le_five_log
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
        roughModulusAbove Q1 (p.1 * p.2) ∧ p.1 ≠ 1),
      ((p.1 * p.2).totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters p.1,
          primitiveCenteredEndpointMaximum x p.1 ψ) ≤
      (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
          (d.totient : ℝ)⁻¹ *
            ∑ ψ : primitiveCharacters d,
              primitiveCenteredEndpointMaximum x d ψ := by
  exact (sum_productRough_factorPairs_le_logPrefix x Q Q1).trans
    (sum_conductorRough_logPrefix_le_five_log x Q Q1 hx hQsqrt)

/-- Source-facing form: the original weighted all-character sum is at most
`5 * log x` times the centered primitive-conductor mass. -/
theorem sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_five_log
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) ≤
      (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
          (d.totient : ℝ)⁻¹ *
            ∑ ψ : primitiveCharacters d,
              primitiveCenteredEndpointMaximum x d ψ := by
  rw [sum_weightedInducingPrimitiveCenteredEndpointMaximum_eq_factorPairs]
  exact sum_productRough_factorPairs_le_five_log x Q Q1 hx hQsqrt

end BoundedGaps.Maynard
