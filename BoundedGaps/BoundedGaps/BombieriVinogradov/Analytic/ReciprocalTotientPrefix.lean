import BoundedGaps.Arithmetic.ReciprocalTotientPrefix
import BoundedGaps.BombieriVinogradov.Analytic.ReciprocalTotientComparison

noncomputable section

/-!
# A logarithmic reciprocal-totient prefix bound

The independently proved constant-four prefix estimate is applied at the
exact natural multiplier cutoff from the conductor reindex. The later
square-root enlargement in Akbary--Hambrook, Section 7, p. 25, remains a
separate step.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable local instance roughModulusAboveDecidableForPrefixConsumer
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- Bound every positive multiplier prefix at its exact natural quotient. -/
theorem sum_conductorRough_factoredInvTotient_le_logPrefix
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
      (∑ ψ : primitiveCharacters d,
        primitiveCenteredEndpointMaximum x d ψ) *
        ((d.totient : ℝ)⁻¹ *
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            (k.totient : ℝ)⁻¹)) ≤
      ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ((d.totient : ℝ)⁻¹ *
            (4 * (1 + Real.log ((Q / d : ℕ) : ℝ)))) := by
  apply Finset.sum_le_sum
  intro d hdmem
  have hdIoc := Finset.mem_filter.mp hdmem |>.1
  have hddata := Finset.mem_Ioc.mp hdIoc
  have hK : 0 < Q / d :=
    Nat.div_pos hddata.2 hddata.1
  have hprefix := reciprocalTotientPrefix_le_four_mul_one_add_log hK
  have hprefix' :
      (∑ k ∈ Finset.Ioc 0 (Q / d),
        (k.totient : ℝ)⁻¹) ≤
        4 * (1 + Real.log ((Q / d : ℕ) : ℝ)) := by
    simpa [reciprocalTotientPrefix] using hprefix
  apply mul_le_mul_of_nonneg_left
  · apply mul_le_mul_of_nonneg_left hprefix'
    positivity
  · exact sum_primitiveCenteredEndpointMaximum_nonneg x d

/-- Compose the product-rough conductor reduction with the prefix estimate. -/
theorem sum_productRough_factorPairs_le_logPrefix
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p =>
        roughModulusAbove Q1 (p.1 * p.2) ∧ p.1 ≠ 1),
      ((p.1 * p.2).totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters p.1,
          primitiveCenteredEndpointMaximum x p.1 ψ) ≤
      ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ((d.totient : ℝ)⁻¹ *
            (4 * (1 + Real.log ((Q / d : ℕ) : ℝ)))) := by
  exact (sum_productRough_factorPairs_le_sum_factoredInvTotient
    x Q Q1).trans
      (sum_conductorRough_factoredInvTotient_le_logPrefix x Q Q1)

end BoundedGaps.Maynard
