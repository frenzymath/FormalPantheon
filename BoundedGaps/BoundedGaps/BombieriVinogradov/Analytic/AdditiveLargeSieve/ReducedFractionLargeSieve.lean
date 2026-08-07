import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.ConsecutiveInterval
import BoundedGaps.BombieriVinogradov.Analytic.ReducedFractionFrequencies

/-!
# The additive large sieve at reduced fractions

This file specializes the consecutive-interval large sieve to all reduced
fractions with positive denominator at most `Q`. See SEM-448 and
MontgomeryVaughanLargeSieve1973, Theorem 1 and printed p. 123.
-/

open scoped BigOperators

noncomputable section

namespace BoundedGaps.Maynard

/-- The consecutive-interval additive large sieve over all reduced fractions
of denominator at most `Q`, with exact coefficient `N + Q^2`. -/
theorem sum_norm_sq_reducedFraction_stdAddChar_Ioc_le
    (Q m0 N : ℕ) (c : ℕ → ℂ) :
    (∑ z : reducedFractionIndices Q,
      ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
        c n * ZMod.stdAddChar
          ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1))‖ ^ 2) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖c n‖ ^ 2 := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    simp [reducedFractionIndices, positiveModuliUpTo]
    positivity
  · have hQpos : (0 : ℝ) < Q := by
      exact_mod_cast Nat.pos_of_ne_zero hQ
    have hdelta : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 :=
      div_pos zero_lt_one (sq_pos_of_pos hQpos)
    have hlarge := sum_norm_sq_unitAddCircleAddChar_Ioc_le
      (x := reducedFractionPoint)
      (δ := (1 : ℝ) / (Q : ℝ) ^ 2) hdelta
      (fun r s hrs => one_div_sq_le_dist_reducedFractionPoint hrs)
      m0 N c
    simp_rw [unitAddCircleAddChar_nsmul_reducedFractionPoint] at hlarge
    simpa only [inv_div, div_one] using hlarge

end BoundedGaps.Maynard
