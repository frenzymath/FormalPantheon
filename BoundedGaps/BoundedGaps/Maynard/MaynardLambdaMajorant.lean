import BoundedGaps.Maynard.ImprovedGPY.S2TauMean

noncomputable section

/-!
# A fixed-logarithmic-power lambda majorant

Maynard2013v3, equation `eq:LambdaSize` (source lines 304--316), reduces the
coefficient bound to a squarefree `tau_k(u) / phi(u)` sum. This file proves a
coarse but sufficient fixed logarithmic-power estimate for that scalar sum.
The divisor/quotient reindex from the concrete coefficient remains separate.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance lambdaMajorantDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def squarefreeTauFirstMean (k Q : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 Q,
    if Squarefree u then
      ((k ^ ω u : ℕ) : ℝ) / (Nat.totient u : ℝ)
    else 0

theorem squarefreeTauFirstMean_le_squarefreeTauMean
    {k Q : ℕ} (hk : 1 ≤ k) :
    squarefreeTauFirstMean k Q ≤ squarefreeTauMean k Q := by
  unfold squarefreeTauFirstMean squarefreeTauMean
  apply Finset.sum_le_sum
  intro u hu
  by_cases hsq : Squarefree u
  · rw [if_pos hsq, if_pos hsq]
    apply div_le_div_of_nonneg_right
    · have hone : 1 ≤ k ^ ω u := one_le_pow₀ hk
      have hsqWeight : k ^ ω u ≤ (k ^ ω u) ^ 2 := by nlinarith
      exact_mod_cast hsqWeight
    · exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hsq.ne_zero)).le
  · simp [hsq]

theorem squarefreeTauFirstMean_le_one_add_log
    {k Q : ℕ} (hk : 1 ≤ k) :
    squarefreeTauFirstMean k Q ≤
      (1 + Real.log Q) ^ (2 * k ^ 2) := by
  exact (squarefreeTauFirstMean_le_squarefreeTauMean hk).trans
    (squarefreeTauMean_le_one_add_log k Q)

end BoundedGaps.Maynard
