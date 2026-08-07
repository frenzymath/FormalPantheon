import BoundedGaps.Maynard.SimplexMoments
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Quadratic-power simplex moments

The exact monomial Dirichlet formula is lifted to Maynard's
`(Σ t_i^2)^c` integrand.  Mathlib's multinomial `piAntidiag` expansion keeps
the composition sum explicit; identifying that sum with the compact `smallKG`
rows is a separate finite-combinatorial bridge.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators Pointwise

noncomputable section

def simplexQuadraticIntegrand (k b c : ℕ) (t : Fin k → ℝ) : ℝ :=
  (1 - ∑ i, t i) ^ b * (∑ i, (t i) ^ 2) ^ c

theorem simplexQuadratic_monomial_integrable (k b : ℕ) (q : Fin k → ℕ) :
    IntegrableOn (fun t : Fin k → ℝ =>
      (1 - ∑ i, t i) ^ b * ∏ i, (t i) ^ (2 * q i))
      (maynardSimplex k) := by
  rw [maynardSimplex_eq_radius]
  change IntegrableOn (maynardSimplexRadiusMonomial k 1 (fun i => 2 * q i) b)
    (maynardSimplexRadius k 1)
  exact radiusMonomial_integrableOn_one k (fun i => 2 * q i) b

theorem simplexQuadratic_integrand_expansion (k b c : ℕ) (t : Fin k → ℝ) :
    simplexQuadraticIntegrand k b c t =
      ∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
        (Nat.multinomial (Finset.univ : Finset (Fin k)) q : ℝ) *
          ((1 - ∑ i, t i) ^ b * ∏ i, (t i) ^ (2 * q i)) := by
  unfold simplexQuadraticIntegrand
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp_rw [pow_mul]
  ring

theorem simplexQuadratic_integrableOn (k b c : ℕ) :
    IntegrableOn (simplexQuadraticIntegrand k b c) (maynardSimplex k) := by
  change IntegrableOn (fun t => simplexQuadraticIntegrand k b c t)
    (maynardSimplex k)
  rw [show (fun t => simplexQuadraticIntegrand k b c t) =
      (fun t => ∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
        (Nat.multinomial (Finset.univ : Finset (Fin k)) q : ℝ) *
          ((1 - ∑ i, t i) ^ b * ∏ i, (t i) ^ (2 * q i))) by
    funext t
    exact simplexQuadratic_integrand_expansion k b c t]
  exact integrable_finsetSum _ (fun q hq =>
    (simplexQuadratic_monomial_integrable k b q).const_mul _)

set_option maxHeartbeats 2000000 in
theorem simplexQuadratic_moment_formula (k b c : ℕ) :
    (∫ t in maynardSimplex k, simplexQuadraticIntegrand k b c t) =
      ∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
        (Nat.multinomial (Finset.univ : Finset (Fin k)) q : ℝ) *
          (((∏ i, (2 * q i).factorial : ℕ) : ℝ) * b.factorial /
            (k + b + ∑ i, 2 * q i).factorial) := by
  rw [show (fun t => simplexQuadraticIntegrand k b c t) =
      (fun t => ∑ q ∈ (Finset.univ : Finset (Fin k)).piAntidiag c,
        (Nat.multinomial (Finset.univ : Finset (Fin k)) q : ℝ) *
          ((1 - ∑ i, t i) ^ b * ∏ i, (t i) ^ (2 * q i))) by
    funext t
    exact simplexQuadratic_integrand_expansion k b c t]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [integral_const_mul]
    rw [maynardSimplex_monomial_integral]
  · intro q hq
    exact (simplexQuadratic_monomial_integrable k b q).integrable.const_mul _

end
end BoundedGaps.Maynard
