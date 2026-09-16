import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetCrossTie
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixCoprimeSquarefulCarrier

/-!
# Fixed-quarter carriers for target cross ties

This charges a displayed/residual prime tie at the fixed exponent one quarter in the proof of
Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152. Small squares enter the coprime Type I
carrier, while large squares enter the positive ambient carrier.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A target cross tie is charged either below the fixed quarter split by the
coprime Type I carrier, or above it by the positive ambient carrier. -/
theorem sectionSixDirectStableTarget_crossTie_mem_quarterSquarefulSplit
    {X delta : Real} {ell M N : Nat} {C : Finset Nat}
    {pattern : SectionSixDirectStablePattern ell M}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (hprime : ∀ z, (factors z).Prime)
    (hproduct : primeTupleProduct factors = N)
    (hmonotone : Monotone factors)
    (hembedding : StrictMono pattern.canonicalDisplayedEmbedding)
    (hoffRangeOrder : ∀ z,
      z ∉ Set.range pattern.canonicalDisplayedEmbedding ->
        pattern.canonicalDisplayedEmbedding 0 < z)
    (hqLowerStrict : X ^ delta <
      (factors (pattern.canonicalDisplayedEmbedding 0) : Real))
    (hNpos : 0 < N)
    (hNUpper : (N : Real) < X)
    (hNC : N ∈ C)
    (hy : 5 ≤ X ^ delta)
    {i : Fin (ell + 1)} {z : Fin ((ell + pattern.1.1) + 1)}
    (hz : z ∉ Set.range pattern.canonicalDisplayedEmbedding)
    (htie : factors (pattern.canonicalDisplayedEmbedding i) = factors z) :
    N ∈ sectionSixRepeatedCoprimeSquarefulCarrier C X delta (1 / 4) ∨
      N ∈ sectionSixRepeatedSquarefulCarrier C X (1 / 4) (1 / 2) := by
  let p : Nat := factors (pattern.canonicalDisplayedEmbedding i)
  have hpData :=
    sectionSixDirectStableTarget_crossTie_prime_and_square_dvd
      hprime hproduct hz htie
  have hpPrime : p.Prime := by
    simpa only [p] using hpData.1
  have hpSq : p * p ∣ N := by
    simpa only [p] using hpData.2
  have hE0le : ∀ j, pattern.canonicalDisplayedEmbedding 0 ≤ j := by
    intro j
    by_cases hj : j ∈ Set.range pattern.canonicalDisplayedEmbedding
    · rcases hj with ⟨a, rfl⟩
      exact hembedding.monotone (Fin.zero_le a)
    · exact (hoffRangeOrder j hj).le
  have hfiveFactor : ∀ j, 5 < (factors j : Real) := by
    intro j
    calc
      (5 : Real) ≤ X ^ delta := hy
      _ < (factors (pattern.canonicalDisplayedEmbedding 0) : Real) :=
        hqLowerStrict
      _ ≤ (factors j : Real) := by
        exact_mod_cast hmonotone (hE0le j)
  have hfactorTen : ∀ j, (factors j).Coprime 10 := by
    intro j
    rw [show 10 = 2 * 5 by norm_num, Nat.coprime_mul_iff_right]
    constructor
    · rw [(hprime j).coprime_iff_not_dvd]
      intro hjDvd
      have hjLe : factors j ≤ 2 := Nat.le_of_dvd (by norm_num) hjDvd
      have hjLeReal : (factors j : Real) ≤ 2 := by
        exact_mod_cast hjLe
      linarith [hfiveFactor j]
    · rw [(hprime j).coprime_iff_not_dvd]
      intro hjDvd
      have hjLe : factors j ≤ 5 := Nat.le_of_dvd (by norm_num) hjDvd
      have hjLeReal : (factors j : Real) ≤ 5 := by
        exact_mod_cast hjLe
      linarith [hfiveFactor j]
  have hNTen : N.Coprime 10 := by
    rw [← hproduct, primeTupleProduct, Nat.coprime_prod_left_iff]
    intro j hj
    exact hfactorTen j
  have hpLower : X ^ delta < (p : Real) := by
    calc
      X ^ delta <
          (factors (pattern.canonicalDisplayedEmbedding 0) : Real) :=
        hqLowerStrict
      _ ≤ (p : Real) := by
        exact_mod_cast hmonotone
          (hembedding.monotone (Fin.zero_le i))
  have hpUpper : (p : Real) ≤ X ^ (1 / 2 : Real) := by
    have hppNat : p * p ≤ N := Nat.le_of_dvd hNpos hpSq
    have hpp : (p : Real) ^ 2 < X := by
      calc
        (p : Real) ^ 2 = ((p * p : Nat) : Real) := by
          norm_num [pow_two]
        _ ≤ (N : Real) := by exact_mod_cast hppNat
        _ < X := hNUpper
    have hpSqrt : (p : Real) < Real.sqrt X :=
      Real.lt_sqrt_of_sq_lt hpp
    rw [Real.sqrt_eq_rpow] at hpSqrt
    exact hpSqrt.le
  rcases le_or_gt (p : Real) (X ^ (1 / 4 : Real)) with
      hpSmall | hpLarge
  · left
    exact mem_sectionSixRepeatedCoprimeSquarefulCarrier.mpr
      ⟨hNC, hNTen, p,
        mem_sievePrimeInterval.mpr ⟨hpPrime, hpLower, hpSmall⟩,
        hpSq⟩
  · right
    exact mem_sectionSixRepeatedSquarefulCarrier.mpr
      ⟨hNC, hNpos, p,
        mem_sievePrimeInterval.mpr ⟨hpPrime, hpLarge, hpUpper⟩,
        hpSq⟩

/-- Primes below the fixed quarter split have squares strictly below the
saving-100 Type I level throughout the allowed epsilon range. -/
theorem sectionSixPrimeSquare_lt_quarterTypeILevel
    {epsilon delta X : Real} {q : Nat}
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (hX : 1 < X)
    (hq : q ∈
      sievePrimeInterval (X ^ delta) (X ^ (1 / 4 : Real))) :
    ((q * q : Nat) : Real) <
      X ^ (50 / 77 - epsilon / 2) := by
  have hqUpper : (q : Real) ≤ X ^ (1 / 4 : Real) :=
    (mem_sievePrimeInterval.mp hq).2.2
  have hqNonneg : 0 ≤ (q : Real) := Nat.cast_nonneg q
  have hthresholdNonneg : 0 ≤ X ^ (1 / 4 : Real) := by
    positivity
  have hsquare :
      (q : Real) ^ 2 ≤ (X ^ (1 / 4 : Real)) ^ 2 :=
    (sq_le_sq₀ hqNonneg hthresholdNonneg).2 hqUpper
  have hbasePos : 0 < X := zero_lt_one.trans hX
  have hexponent :
      (1 / 2 : Real) < 50 / 77 - epsilon / 2 := by
    norm_num at hepsilonSmall ⊢
    linarith
  have hpower :
      X ^ (1 / 2 : Real) <
        X ^ (50 / 77 - epsilon / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt hX hexponent
  calc
    ((q * q : Nat) : Real) = (q : Real) ^ 2 := by
      norm_num [pow_two]
    _ ≤ (X ^ (1 / 4 : Real)) ^ 2 := hsquare
    _ = X ^ (1 / 2 : Real) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hbasePos.le]
      congr 1
      ring
    _ < X ^ (50 / 77 - epsilon / 2) := hpower

end

end PrimesRestrictedDigits
