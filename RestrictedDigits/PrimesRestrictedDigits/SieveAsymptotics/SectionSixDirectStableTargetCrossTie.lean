import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# Square divisors from target cross ties

This preserves labelled prime-factor multiplicity in the displayed/residual tie exception from
Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Equal values at two distinct factor labels contribute a square divisor to
the complete labelled product. -/
theorem square_dvd_primeTupleProduct_of_distinct_equal
    {k : Nat} (factors : Fin k -> Nat) {i j : Fin k}
    (hij : i ≠ j) (heq : factors i = factors j) :
    factors i * factors i ∣ primeTupleProduct factors := by
  have hj : j ∈ Finset.univ.erase i := by
    exact Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hjDvd : factors j ∣ ∏ z ∈ Finset.univ.erase i, factors z :=
    Finset.dvd_prod_of_mem factors hj
  have hmul : factors i * factors j ∣
      factors i * ∏ z ∈ Finset.univ.erase i, factors z :=
    Nat.mul_dvd_mul_left (factors i) hjDvd
  rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at hmul
  rw [← heq] at hmul
  simpa only [primeTupleProduct] using hmul

/-- A displayed/off-range value tie in a canonical target tuple supplies a
prime whose square divides the represented target integer. -/
theorem sectionSixDirectStableTarget_crossTie_prime_and_square_dvd
    {ell M N : Nat} {pattern : SectionSixDirectStablePattern ell M}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (hprime : ∀ z, (factors z).Prime)
    (hproduct : primeTupleProduct factors = N)
    {i : Fin (ell + 1)} {z : Fin ((ell + pattern.1.1) + 1)}
    (hz : z ∉ Set.range pattern.canonicalDisplayedEmbedding)
    (htie : factors (pattern.canonicalDisplayedEmbedding i) = factors z) :
    (factors (pattern.canonicalDisplayedEmbedding i)).Prime ∧
      factors (pattern.canonicalDisplayedEmbedding i) *
          factors (pattern.canonicalDisplayedEmbedding i) ∣ N := by
  have hne : pattern.canonicalDisplayedEmbedding i ≠ z := by
    intro h
    exact hz ⟨i, h⟩
  refine ⟨hprime _, ?_⟩
  have hsquare := square_dvd_primeTupleProduct_of_distinct_equal
    factors hne htie
  simpa only [hproduct] using hsquare

end

end PrimesRestrictedDigits
