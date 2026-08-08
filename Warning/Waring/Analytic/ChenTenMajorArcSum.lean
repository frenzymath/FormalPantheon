import Waring.Analytic.ChenTenMajorArcDecayIntegration
import Waring.Analytic.ChenTenMajorArcWeightSum

/-!
# Summing the decay-weighted Chen major arcs

This file groups reduced arc indices by denominator, bounds each fiber by
Euler's totient, and sums the resulting `q^(-4/5)` weight.  It converts the
per-arc estimate into an aggregate `P^(91/10)` error.
-/

namespace Waring.Analytic

open Set MeasureTheory
open scoped BigOperators Interval

noncomputable section

set_option maxHeartbeats 2000000 in
/-- Transfer a pointwise `C*q^(-9/5)*P^9` bound to the sum over all reduced
arc indices. -/
theorem sum_chenTenArcError_le_of_pointwise
    {P : Nat} (hP : 1 ≤ P) {C : Real} (hC : 0 ≤ C)
    (error : ChenTenArcIndex P -> Real)
    (herror : ∀ i, error i <=
      C * chenTenArcWeight i.denominator * (P : Real) ^ 9) :
    (∑ i : ChenTenArcIndex P, error i) <=
      5 * C * (P : Real) ^ (91 / 10 : Real) := by
  have hsum := sum_chenTenArcWeight_le_natSqrt P hP
  have hsqrt := natSqrt_rpow_one_fifth_le P
  have hPpos : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_of_lt hP
  calc
    (∑ i : ChenTenArcIndex P, error i) <=
        ∑ i : ChenTenArcIndex P,
          C * chenTenArcWeight i.denominator * (P : Real) ^ 9 := by
      apply Finset.sum_le_sum
      intro i hi
      exact herror i
    _ = (C * (P : Real) ^ 9) *
        ∑ i : ChenTenArcIndex P, chenTenArcWeight i.denominator := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ <= (C * (P : Real) ^ 9) *
        (5 * (Nat.sqrt P : Real) ^ (1 / 5 : Real)) := by
      exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (by positivity))
    _ <= (C * (P : Real) ^ 9) *
        (5 * (P : Real) ^ (1 / 10 : Real)) := by
      gcongr
    _ = 5 * C * (P : Real) ^ (91 / 10 : Real) := by
      calc
        (C * (P : Real) ^ 9) *
            (5 * (P : Real) ^ (1 / 10 : Real)) =
            5 * C * ((P : Real) ^ (9 : Real) *
              (P : Real) ^ (1 / 10 : Real)) := by
          rw [Real.rpow_ofNat]
          ring
        _ = 5 * C * (P : Real) ^
            ((9 : Real) + 1 / 10) := by
          rw [Real.rpow_add hPpos]
        _ = 5 * C * (P : Real) ^ (91 / 10 : Real) := by norm_num

/-- The total actual-minus-modeled contribution of all reduced major arcs is
at most `5 * 10^30 * P^(91/10)`. -/
theorem norm_sum_setIntegral_chenTenRepresentationIntegrand_sub_model_le_decay
    {P : Nat} (hP : 1 <= P) (N : Nat) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        ∑ i : ChenTenArcIndex P,
          ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
            chenTenMajorArcModelIntegrand P N i z‖ <=
      5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i : ChenTenArcIndex P,
        ((∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
          ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
            chenTenMajorArcModelIntegrand P N i z)‖ <=
        ∑ i : ChenTenArcIndex P,
          ‖(∫ alpha in chenTenArc P i,
              chenTenRepresentationIntegrand P N alpha) -
            ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
              chenTenMajorArcModelIntegrand P N i z‖ :=
      norm_sum_le _ _
    _ <= 5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) := by
      apply sum_chenTenArcError_le_of_pointwise hP (by positivity)
      intro i
      simpa [chenTenArcWeight] using
        norm_setIntegral_chenTenRepresentationIntegrand_sub_model_le_decay
          hP N i

/-- After exact model separation, the same aggregate decay estimate compares
the actual major arcs with the indexed singular terms and truncated kernels. -/
theorem norm_sum_setIntegral_chenTenRepresentationIntegrand_sub_singular_le_decay
    {P : Nat} (hP : 1 <= P) (N : Nat) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        ∑ i : ChenTenArcIndex P,
          chenTenIndexedSingularTerm N i *
            chenTenTruncatedSingularIntegral P N i‖ <=
      5 * (10 : Real) ^ 30 * (P : Real) ^ (91 / 10 : Real) := by
  rw [← sum_intervalIntegral_chenTenMajorArcModelIntegrand_eq]
  exact
    norm_sum_setIntegral_chenTenRepresentationIntegrand_sub_model_le_decay
      hP N

end

end Waring.Analytic
