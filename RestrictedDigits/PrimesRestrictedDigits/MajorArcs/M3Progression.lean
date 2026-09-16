import PrimesRestrictedDigits.MajorArcs.M3Convolution
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrimeLogProgression

/-!
# The weighted M3 progression estimate

This proves the arithmetic-progression calculation on
`MAYNARD-PRD-PUBLISHED`, pp. 188--189, directly from the strict global
prime-log estimate. The original last-prime carrier is represented as the
difference of two strict prefix sums.
-/

open scoped BigOperators
open Filter

namespace PrimesRestrictedDigits

/-- On every supported prefix, the maximum last-prime lower cutoff lies below
the strict product cutoff. -/
theorem majorArcLastPrimeLowerCutoff_le_div_of_projectedWeight
    {X k m : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) <= 2 / eta)
    (hdelta0 : 0 <= delta) (hdelta : delta <= eta ^ 2 / 12)
    (hm : 0 < m)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0) :
    majorArcLastPrimeLowerCutoff X a delta eta <=
      (X : Real) / (m : Real) := by
  let x : Real := X
  have hxOne' : (1 : Real) < (X : Real) := by exact_mod_cast hX
  have hxOne : 1 < x := by simpa [x] using hxOne'
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hmPos : (0 : Real) < m := by exact_mod_cast hm
  have hmSupport := projectedPrimeBoxWeightAtProduct_support_bounds
    hX heta hsum hell hdelta0 hdelta hweight
  have hk : (k : Real) <= 2 / eta := by
    calc
      (k : Real) <= ((k + 1 : Nat) : Real) := by
        exact_mod_cast Nat.le_succ k
      _ <= 2 / eta := hell
  have hkdelta : (k : Real) * delta <= eta / 6 :=
    natCast_mul_delta_le_eta_div_six heta hk hdelta0 hdelta
  apply max_le
  · rw [le_div_iff₀ hmPos]
    calc
      x ^ (eta / 4) * (m : Real) <=
          x ^ (eta / 4) *
            x ^ ((∑ i, a i) + (k : Real) * delta) :=
        mul_le_mul_of_nonneg_left (by simpa [x] using hmSupport.1)
          (Real.rpow_nonneg hxPos.le _)
      _ = x ^ (eta / 4 + ((∑ i, a i) + (k : Real) * delta)) := by
        rw [← Real.rpow_add hxPos]
      _ <= x ^ (1 : Real) := by
        apply Real.rpow_le_rpow_of_exponent_le hxOne.le
        linarith
      _ = x := Real.rpow_one x
  · rw [le_div_iff₀ hmPos]
    calc
      x ^ (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta) *
          (m : Real) <=
        x ^ (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta) *
          x ^ ((∑ i, a i) + (k : Real) * delta) :=
        mul_le_mul_of_nonneg_left (by simpa [x] using hmSupport.1)
          (Real.rpow_nonneg hxPos.le _)
      _ = x ^ (1 - delta) := by
        rw [← Real.rpow_add hxPos]
        congr 1
        push_cast
        ring
      _ <= x ^ (1 : Real) := by
        apply Real.rpow_le_rpow_of_exponent_le hxOne.le
        linarith
      _ = x := Real.rpow_one x

/-- One actual last-prime product-residue fiber is exactly the difference of
two strict prime-log progression sums. -/
theorem majorArcLastPrimeProductResidueLogSum_eq_prefix_sub
    {X k m q r : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hm : 0 < m) (hq : 0 < q) (hmq : Nat.Coprime m q)
    (hLU : majorArcLastPrimeLowerCutoff X a delta eta <=
      (X : Real) / (m : Real)) :
    majorArcLastPrimeProductResidueLogSum X a delta eta m q r =
      primeLogProgressionSum q (majorArcPrefixInverseResidue q m r)
          ((X : Real) / (m : Real)) -
        primeLogProgressionSum q (majorArcPrefixInverseResidue q m r)
          (majorArcLastPrimeLowerCutoff X a delta eta) := by
  let b := majorArcPrefixInverseResidue q m r
  let U : Real := (X : Real) / (m : Real)
  let L := majorArcLastPrimeLowerCutoff X a delta eta
  let P : Nat -> Prop := fun p => p.Prime ∧ p ≡ b [MOD q]
  let upper := (naturalLeftClosedRightOpenInterval 0 U).filter P
  let lower := (naturalLeftClosedRightOpenInterval 0 L).filter P
  have hsubset : lower ⊆ upper := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpInterval, hpP⟩
    refine Finset.mem_filter.mpr ⟨?_, hpP⟩
    have hpBounds := mem_naturalLeftClosedRightOpenInterval.mp hpInterval
    apply mem_naturalLeftClosedRightOpenInterval.mpr
    exact ⟨hpBounds.1,
      hpBounds.2.trans_le (by simpa [L, U] using hLU)⟩
  have hcarrier : upper \ lower =
      (majorArcLastPrimes X a delta eta).filter
        (fun p => m * p < X ∧ m * p ≡ r [MOD q]) := by
    apply Finset.ext
    intro p
    dsimp [upper, lower]
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpUpper, hpPrime, hpMod⟩, hpNotLower⟩
      have hpUpperBounds :=
        mem_naturalLeftClosedRightOpenInterval.mp hpUpper
      have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
      have hmPos : (0 : Real) < m := by exact_mod_cast hm
      have hpMul : (p : Real) * (m : Real) < (X : Real) :=
        (lt_div_iff₀ hmPos).mp (by simpa [U] using hpUpperBounds.2)
      have hpCutoffReal : ((m * p : Nat) : Real) < (X : Real) := by
        push_cast
        simpa [mul_comm] using hpMul
      have hpCutoff : m * p < X := by exact_mod_cast hpCutoffReal
      have hpLower : L <= (p : Real) := by
        apply le_of_not_gt
        intro hpLt
        apply hpNotLower
        refine ⟨mem_naturalLeftClosedRightOpenInterval.mpr
          ⟨hpPos.le, hpLt⟩, ?_⟩
        exact ⟨hpPrime, hpMod⟩
      have hpLeX : p <= X := by
        calc
          p <= m * p := Nat.le_mul_of_pos_left p hm
          _ <= X := hpCutoff.le
      have hpLast : p ∈ majorArcLastPrimes X a delta eta := by
        rw [mem_majorArcLastPrimes_iff]
        dsimp [L, majorArcLastPrimeLowerCutoff] at hpLower
        have hparts := max_le_iff.mp hpLower
        exact ⟨Nat.mem_primesLE.mpr ⟨hpLeX, hpPrime⟩,
          hparts.1, hparts.2⟩
      exact ⟨hpLast, hpCutoff,
        (mul_modEq_iff_modEq_prefixInverseResidue hq hmq).2 hpMod⟩
    · rintro ⟨hpLast, hpCutoff, hpProductMod⟩
      have hpInfo := mem_majorArcLastPrimes_iff.mp hpLast
      have hpPrime := Nat.prime_of_mem_primesLE hpInfo.1
      have hmPos : (0 : Real) < m := by exact_mod_cast hm
      have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
      have hpUpperReal : (p : Real) < U := by
        dsimp [U]
        rw [lt_div_iff₀ hmPos]
        exact_mod_cast (by simpa [mul_comm] using hpCutoff)
      have hpLower : L <= (p : Real) := by
        dsimp [L, majorArcLastPrimeLowerCutoff]
        exact max_le hpInfo.2.1 hpInfo.2.2
      have hpMod : p ≡ b [MOD q] :=
        (mul_modEq_iff_modEq_prefixInverseResidue hq hmq).1 hpProductMod
      refine ⟨⟨mem_naturalLeftClosedRightOpenInterval.mpr
        ⟨hpPos.le, hpUpperReal⟩, hpPrime, hpMod⟩, ?_⟩
      intro hpLowerMem
      have hpLowerBounds :=
        mem_naturalLeftClosedRightOpenInterval.mp hpLowerMem.1
      exact (not_lt_of_ge hpLower) hpLowerBounds.2
  have hsum :
      (∑ p ∈ upper \ lower, Real.log (p : Real)) =
        (∑ p ∈ upper, Real.log (p : Real)) -
          ∑ p ∈ lower, Real.log (p : Real) :=
    Finset.sum_sdiff_eq_sub hsubset
  unfold majorArcLastPrimeProductResidueLogSum
  rw [← hcarrier, hsum]
  simp [upper, lower, P, U, L, b, primeLogProgressionSum]

end PrimesRestrictedDigits
