import BoundedGaps.BombieriVinogradov.Analytic.RawPrimitiveMeanNormalization
import Mathlib.NumberTheory.AbelSummation

/-!
# Raw primitive Abel summation

This file formalizes the continuous partial-summation identity on
Akbary--Hambrook2013v2, Section 7, p. 25. It retains both real boundary terms
and stops before the source applies its primitive-character mean-value bound.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
open MeasureTheory

noncomputable section

noncomputable local instance roughModulusAboveDecidableForAbel (Q1 : ℝ) :
    DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- The cumulative raw primitive mean weight through the natural floor of a
real endpoint. The level-zero term is zero by SEM-427. -/
noncomputable def primitiveRawMeanValueCumulative (x : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 0 ⌊t⌋₊, primitiveRawMeanValueWeight x q

/-- The cumulative raw primitive mean weight is nonnegative. -/
theorem primitiveRawMeanValueCumulative_nonneg (x : ℕ) (t : ℝ) :
    0 ≤ primitiveRawMeanValueCumulative x t := by
  unfold primitiveRawMeanValueCumulative
  exact Finset.sum_nonneg fun q _ ↦ primitiveRawMeanValueWeight_nonneg x q

/-- At a natural real endpoint, the cumulative sum has that exact natural
upper index. -/
theorem primitiveRawMeanValueCumulative_nat (x Q : ℕ) :
    primitiveRawMeanValueCumulative x (Q : ℝ) =
      ∑ q ∈ Finset.Icc 0 Q, primitiveRawMeanValueWeight x q := by
  simp [primitiveRawMeanValueCumulative]

/-- The source's continuous partial-summation identity with literal real
lower and upper endpoints. -/
theorem sum_meanValueWeight_div_eq_rawPrimitiveAbel
    (x : ℕ) (Q1 Q : ℝ) (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ Q) :
    (∑ q ∈ Finset.Ioc ⌊Q1⌋₊ ⌊Q⌋₊,
      primitiveRawMeanValueWeight x q / (q : ℝ)) =
      Q⁻¹ * primitiveRawMeanValueCumulative x Q -
        Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
          ∫ t in Set.Ioc Q1 Q,
            primitiveRawMeanValueCumulative x t / t ^ 2 := by
  have hQ1pos : 0 < Q1 := zero_lt_one.trans_le hQ1
  have habel := sum_mul_eq_sub_sub_integral_mul
    (f := fun t : ℝ ↦ t⁻¹)
    (fun q ↦ primitiveRawMeanValueWeight x q)
    hQ1pos.le hQ
    (fun t ht ↦ differentiableAt_inv (ne_of_gt (hQ1pos.trans_le ht.1)))
    (by
      rw [show deriv (fun t : ℝ ↦ t⁻¹) = fun t ↦ -(t ^ 2)⁻¹ by
        funext t
        exact deriv_inv]
      exact (((continuousOn_id.pow 2).inv₀ (fun t ht ↦ by
        have htpos : 0 < t := hQ1pos.trans_le ht.1
        exact pow_ne_zero 2 htpos.ne')).neg).integrableOn_Icc)
  have habel' :
      (∑ q ∈ Finset.Ioc ⌊Q1⌋₊ ⌊Q⌋₊,
          (q : ℝ)⁻¹ * primitiveRawMeanValueWeight x q) =
        Q⁻¹ * primitiveRawMeanValueCumulative x Q -
          Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 -
            ∫ t in Set.Ioc Q1 Q,
              deriv (fun y : ℝ ↦ y⁻¹) t *
                primitiveRawMeanValueCumulative x t := by
    simpa [primitiveRawMeanValueCumulative] using habel
  have hleft :
      (∑ q ∈ Finset.Ioc ⌊Q1⌋₊ ⌊Q⌋₊,
          primitiveRawMeanValueWeight x q / (q : ℝ)) =
        ∑ q ∈ Finset.Ioc ⌊Q1⌋₊ ⌊Q⌋₊,
          (q : ℝ)⁻¹ * primitiveRawMeanValueWeight x q := by
    apply Finset.sum_congr rfl
    intro q _
    rw [div_eq_mul_inv, mul_comm]
  have hintegrand :
      (fun t : ℝ ↦
          deriv (fun y : ℝ ↦ y⁻¹) t *
            primitiveRawMeanValueCumulative x t) =
        fun t ↦ -(primitiveRawMeanValueCumulative x t / t ^ 2) := by
    funext t
    rw [deriv_inv]
    ring
  rw [hleft, habel', hintegrand, MeasureTheory.integral_neg]
  ring

/-- Natural-upper-endpoint specialization used by the finite Packet D
modulus range. -/
theorem sum_meanValueWeight_div_eq_rawPrimitiveAbel_natUpper
    (x Q : ℕ) (Q1 : ℝ) (hQ1 : 1 ≤ Q1)
    (hQ : Q1 ≤ (Q : ℝ)) :
    (∑ q ∈ Finset.Ioc ⌊Q1⌋₊ Q,
      primitiveRawMeanValueWeight x q / (q : ℝ)) =
      (Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
        Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
          ∫ t in Set.Ioc Q1 (Q : ℝ),
            primitiveRawMeanValueCumulative x t / t ^ 2 := by
  simpa only [Nat.floor_natCast] using
    sum_meanValueWeight_div_eq_rawPrimitiveAbel
      x Q1 (Q : ℝ) hQ1 hQ

/-- Source-facing composition through the complete Abel expression. The
negative lower boundary term is retained. -/
theorem sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_five_log_abel
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ1 : 1 ≤ Q1) (hQ : Q1 ≤ (Q : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) ≤
      (5 * Real.log (x : ℝ)) *
        ((Q : ℝ)⁻¹ * primitiveRawMeanValueCumulative x Q -
          Q1⁻¹ * primitiveRawMeanValueCumulative x Q1 +
            ∫ t in Set.Ioc Q1 (Q : ℝ),
              primitiveRawMeanValueCumulative x t / t ^ 2) := by
  rw [← sum_meanValueWeight_div_eq_rawPrimitiveAbel_natUpper
    x Q Q1 hQ1 hQ]
  exact
    sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_five_log_meanValueInterval
      x Q Q1 hx hQsqrt

end

end BoundedGaps.Maynard
