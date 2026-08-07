import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveCharacterInterval
import BoundedGaps.BombieriVinogradov.Analytic.ReciprocalSineAggregate

/-!
# Primitive Polya--Vinogradov interval bound

This is the direct composition of the audited pre-aggregate envelope and the
strict reciprocal-sine estimate in DavenportMNTCh23PV1980, printed p. 136.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- Primitive Polya--Vinogradov on an arbitrary translated integer interval. -/
theorem norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.zero_lt_of_lt hq
  have hsqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  calc
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
        (∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
          Real.sqrt q :=
      norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum hq chi hchi M N
    _ < ((q : ℝ) * Real.log (q : ℝ)) / Real.sqrt q :=
      div_lt_div_of_pos_right (sum_reciprocalSine_Ico_lt_mul_log hq) hsqrt
    _ = Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      apply (div_eq_iff hsqrt.ne').2
      calc
        (q : ℝ) * Real.log (q : ℝ) =
            (Real.sqrt (q : ℝ)) ^ 2 * Real.log (q : ℝ) := by
          rw [Real.sq_sqrt hqpos.le]
        _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            Real.sqrt (q : ℝ) := by ring

end BoundedGaps.Maynard
