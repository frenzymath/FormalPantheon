import PrimesRestrictedDigits.MajorArcs.Factorization
import PrimesRestrictedDigits.MajorArcs.ResiduePhaseSum

/-!
# Exact M2 regrouping on the original last-prime carrier

This repairs the transition after Eq. (11.2) of `MAYNARD-PRD-PUBLISHED` by
pruning to reduced residues before either last-prime lower bound is removed.
No relaxed-carrier estimate is proved here.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The phase sum over the actual last-prime carrier in Eq. (11.2), retaining
both lower bounds and the strict product cutoff. -/
noncomputable def majorArcLastPrimePhaseSum
    (X : Nat) {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (m : Nat) (theta : Real) : Complex :=
  ∑ p ∈ majorArcLastPrimes X a delta eta with m * p < X,
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) * theta)

/-- One residue fiber of the actual last-prime phase sum. -/
noncomputable def majorArcLastPrimePhaseResidueSum
    (X : Nat) {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (m q residue : Nat) (theta : Real) : Complex :=
  ∑ p ∈ majorArcLastPrimes X a delta eta with
      m * p < X ∧ p ≡ residue [MOD q],
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) * theta)

/-- Every original last prime is coprime to a denominator dividing the
power-of-ten scale once the first lower bound is greater than five. -/
theorem majorArcLastPrime_coprime_of_dvd_powerTen
    {X K q k p : Nat} {a : Fin k → Real} {delta eta : Real}
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hq : q ∣ X)
    (hp : p ∈ majorArcLastPrimes X a delta eta) :
    Nat.Coprime p q := by
  have hpInfo := mem_majorArcLastPrimes_iff.mp hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE hpInfo.1
  rw [hpPrime.coprime_iff_not_dvd]
  intro hpq
  have hppow : p ∣ 10 ^ K := hpq.trans (by simpa [hpower] using hq)
  have hpten : p ∣ 10 := hpPrime.dvd_of_dvd_pow hppow
  have hpprod : p ∣ 2 * 5 := by
    norm_num at hpten ⊢
    exact hpten
  have hpLargeNat : 5 < p := by
    exact_mod_cast hlarge.trans_le hpInfo.2.1
  rcases hpPrime.dvd_mul.mp hpprod with hpTwo | hpFive
  · have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpTwo
    omega
  · have hpLe : p ≤ 5 := Nat.le_of_dvd (by norm_num) hpFive
    omega

/-- Summing Eq. (11.2) over `n < X` gives the exact last-prime convolution.
The product-zero prefix is removed only through its proved zero weight. -/
theorem majorArcRegionWeightedPhaseSum_eq_projected_lastPrimeSum
    {X k : Nat} (a : Fin k → Real) (delta eta theta : Real)
    (hX : 1 < X) :
    majorArcWeightedPhaseSum (Finset.range X)
        (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
        theta =
      ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          majorArcLastPrimePhaseSum X a delta eta m theta := by
  let W := fun m => projectedPrimeBoxWeightAtProduct X a delta m
  let L := majorArcLastPrimes X a delta eta
  let e := fun n : Nat => majorArcPhase ((n : Real) * theta)
  have hfactor (n : Nat) (hn : n < X) :
      (majorArcRegionWeightAtProduct X a delta eta n : Complex) =
        ∑ m ∈ Finset.range X,
          ∑ p ∈ L with m * p = n,
            (W m : Complex) * (Real.log (p : Real) : Complex) := by
    dsimp [W, L]
    rw [majorArcRegionWeightAtProduct_eq_projected_convolution
      a delta eta hX hn]
    push_cast
    rfl
  have hpositiveSubset : Finset.Ico 1 X ⊆ Finset.range X := by
    intro m hm
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
  unfold majorArcWeightedPhaseSum
  change (∑ n ∈ Finset.range X,
      (majorArcRegionWeightAtProduct X a delta eta n : Complex) * e n) = _
  calc
    (∑ n ∈ Finset.range X,
        (majorArcRegionWeightAtProduct X a delta eta n : Complex) * e n) =
        ∑ n ∈ Finset.range X,
          ∑ m ∈ Finset.range X,
            ∑ p ∈ L with m * p = n,
              (W m : Complex) * (Real.log (p : Real) : Complex) * e n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hfactor n (Finset.mem_range.mp hn), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]
    _ = ∑ m ∈ Finset.range X,
        ∑ p ∈ L with m * p < X,
          (W m : Complex) * (Real.log (p : Real) : Complex) * e (m * p) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_range]
    _ = ∑ m ∈ Finset.range X,
        (W m : Complex) *
          majorArcLastPrimePhaseSum X a delta eta m theta := by
      apply Finset.sum_congr rfl
      intro m hm
      unfold majorArcLastPrimePhaseSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [e]
      ring
    _ = ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          majorArcLastPrimePhaseSum X a delta eta m theta := by
      dsimp [W]
      symm
      apply Finset.sum_subset hpositiveSubset
      intro m hmRange hmNotPositive
      have hm0 : m = 0 := by
        have hmLt := Finset.mem_range.mp hmRange
        have hmNotOne : ¬1 ≤ m := by
          intro hmOne
          exact hmNotPositive (Finset.mem_Ico.mpr ⟨hmOne, hmLt⟩)
        omega
      subst m
      rw [projectedPrimeBoxWeightAtProduct_zero]
      norm_num

/-- The actual last-prime phase sum is exactly the sum of its reduced residue
fibers. In particular, the modulus-one residue `0` is retained. -/
theorem majorArcLastPrimePhaseSum_eq_sum_reducedResidues
    {X K q k : Nat} {a : Fin k → Real} {delta eta : Real}
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X) (hq : 0 < q)
    (m : Nat) (theta : Real) :
    majorArcLastPrimePhaseSum X a delta eta m theta =
      ∑ r ∈ majorArcReducedResidues q,
        majorArcLastPrimePhaseResidueSum X a delta eta m q r theta := by
  let L := (majorArcLastPrimes X a delta eta).filter fun p => m * p < X
  let term := fun p : Nat =>
    (Real.log (p : Real) : Complex) *
      majorArcPhase (((m * p : Nat) : Real) * theta)
  have hmaps : ∀ p ∈ L, p % q ∈ Finset.range q := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.mod_lt p hq)
  have hall :
      majorArcLastPrimePhaseSum X a delta eta m theta =
        ∑ r ∈ Finset.range q,
          majorArcLastPrimePhaseResidueSum X a delta eta m q r theta := by
    unfold majorArcLastPrimePhaseSum
    change (∑ p ∈ L, term p) = _
    rw [← Finset.sum_fiberwise_of_maps_to hmaps term]
    apply Finset.sum_congr rfl
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    unfold majorArcLastPrimePhaseResidueSum
    change (∑ p ∈ L.filter (fun p => p % q = r), term p) = _
    apply Finset.sum_congr
    · ext p
      simp [L, Nat.ModEq, Nat.mod_eq_of_lt hrq, and_assoc, and_comm]
    · intro p hp
      rfl
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r hrange hrnotReduced
  unfold majorArcLastPrimePhaseResidueSum
  apply Finset.sum_eq_zero
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpLast, hpCutoff, hpMod⟩
  have hpCoprime : Nat.Coprime p q :=
    majorArcLastPrime_coprime_of_dvd_powerTen hlarge hpower hqdiv hpLast
  have hrCoprime : Nat.Coprime r q := by
    rw [Nat.coprime_iff_gcd_eq_one, ← hpMod.gcd_eq]
    exact Nat.coprime_iff_gcd_eq_one.mp hpCoprime
  exact (hrnotReduced (Finset.mem_filter.mpr ⟨hrange, hrCoprime⟩)).elim

/-- The source region transform is exactly a projected-product sum of reduced
original last-prime fibers. -/
theorem majorArcRegionWeightedPhaseSum_eq_projected_reducedLastPrimeSum
    {X K q k : Nat} {a : Fin k → Real} {delta eta : Real}
    (hX : 1 < X) (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X) (hq : 0 < q)
    (theta : Real) :
    majorArcWeightedPhaseSum (Finset.range X)
        (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
        theta =
      ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          ∑ r ∈ majorArcReducedResidues q,
            majorArcLastPrimePhaseResidueSum
              X a delta eta m q r theta := by
  rw [majorArcRegionWeightedPhaseSum_eq_projected_lastPrimeSum
    a delta eta theta hX]
  apply Finset.sum_congr rfl
  intro m hm
  rw [majorArcLastPrimePhaseSum_eq_sum_reducedResidues
    hlarge hpower hqdiv hq m theta]

/-- Signed affine specialization used by the repaired M2 class. Neither
integer needs a sign or size hypothesis at this exact stage. -/
theorem majorArcRegionWeightedPhaseSum_signed_eq_projected_reducedLastPrimeSum
    {X K q k : Nat} {a : Fin k → Real} {delta eta : Real}
    (hX : 1 < X) (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X) (hq : 0 < q)
    (b c : Int) :
    majorArcWeightedPhaseSum (Finset.range X)
        (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
        ((b : Real) / (q : Real) + (c : Real) / (X : Real)) =
      ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          ∑ r ∈ majorArcReducedResidues q,
            majorArcLastPrimePhaseResidueSum X a delta eta m q r
              ((b : Real) / (q : Real) + (c : Real) / (X : Real)) :=
  majorArcRegionWeightedPhaseSum_eq_projected_reducedLastPrimeSum
    hX hlarge hpower hqdiv hq _

end PrimesRestrictedDigits
