import PrimesRestrictedDigits.SieveDecomposition.Definitions

/-!
# Exact weak-fiber Buchstab identity

This repairs the strict-only least-prime-factor recurrences printed in
`MAYNARD-PRD-PUBLISHED`, Section 6. The outer carriers remain strictly sifted;
after factoring the least prime, the cofactor is only weakly sifted at that
prime.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The exact finite carrier of primes in the real interval `(z1, z2]`. -/
noncomputable def sievePrimeInterval (z1 z2 : Real) : Finset Nat := by
  classical
  exact (Finset.range (Nat.ceil z2 + 1)).filter fun p =>
    p.Prime ∧ z1 < (p : Real) ∧ (p : Real) <= z2

@[simp] theorem mem_sievePrimeInterval
    {z1 z2 : Real} {p : Nat} :
    p ∈ sievePrimeInterval z1 z2 <->
      p.Prime ∧ z1 < (p : Real) ∧ (p : Real) <= z2 := by
  classical
  unfold sievePrimeInterval
  rw [Finset.mem_filter]
  constructor
  · exact fun hp => hp.2
  · intro hp
    refine ⟨Finset.mem_range.mpr ?_, hp⟩
    have hpCeil : p <= Nat.ceil z2 := by
      exact_mod_cast hp.2.2.trans (Nat.le_ceil z2)
    omega

/-- Elements that are weakly but not strictly sifted at the prime threshold.
These are exactly the elements whose least prime factor is `p`. -/
noncomputable def weakPrimeThresholdFiber
    (C : Finset Nat) (p : Nat) : Finset Nat :=
  weakSiftedCarrier C (p : Real) \
    strictSiftedCarrier C (p : Real)

@[simp] theorem mem_weakPrimeThresholdFiber
    {C : Finset Nat} {p n : Nat} :
    n ∈ weakPrimeThresholdFiber C p <->
      n ∈ C ∧ weakRoughPredicate (p : Real) n ∧
        ¬strictRoughPredicate (p : Real) n := by
  rw [weakPrimeThresholdFiber, Finset.mem_sdiff,
    mem_weakSiftedCarrier, mem_strictSiftedCarrier]
  constructor
  · rintro ⟨⟨hnC, hnWeak⟩, hnNot⟩
    exact ⟨hnC, hnWeak, fun hnStrict => hnNot ⟨hnC, hnStrict⟩⟩
  · rintro ⟨hnC, hnWeak, hnNotStrict⟩
    exact ⟨⟨hnC, hnWeak⟩, fun hnStrict => hnNotStrict hnStrict.2⟩

/-- A prime-threshold fiber is the corresponding `Nat.minFac` fiber. -/
theorem weakPrimeThresholdFiber_eq_filter_minFac
    (C : Finset Nat) {p : Nat} (hp : p.Prime) :
    weakPrimeThresholdFiber C p = C.filter fun n => n.minFac = p := by
  classical
  ext n
  rw [mem_weakPrimeThresholdFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hnC, hnWeak, hnNotStrict⟩
    have hn1 : n ≠ 1 := by
      intro hn
      subst n
      exact hnNotStrict (strictRoughPredicate_one (p : Real))
    simp only [strictRoughPredicate] at hnNotStrict
    push Not at hnNotStrict
    obtain ⟨r, hr, hrd, hrp⟩ := hnNotStrict
    have hMinPrime := Nat.minFac_prime hn1
    have hMinDvd := Nat.minFac_dvd n
    have hMinLeR : n.minFac <= r :=
      Nat.minFac_le_of_dvd hr.two_le hrd
    have hrLeP : r <= p := by exact_mod_cast hrp
    have hpLeMin : p <= n.minFac := by
      exact_mod_cast hnWeak n.minFac hMinPrime hMinDvd
    exact ⟨hnC, Nat.le_antisymm (hMinLeR.trans hrLeP) hpLeMin⟩
  · rintro ⟨hnC, hMin⟩
    have hn1 : n ≠ 1 := by
      intro hn
      subst n
      exact hp.ne_one
        (hMin.symm.trans (Nat.minFac_eq_one_iff.mpr rfl))
    have hMinPrime := Nat.minFac_prime hn1
    have hMinDvd := Nat.minFac_dvd n
    refine ⟨hnC, ?_, ?_⟩
    · intro r hr hrd
      exact_mod_cast (show p <= r by
        rw [← hMin]
        exact Nat.minFac_le_of_dvd hr.two_le hrd)
    · intro hStrict
      have hpStrict := hStrict p hp (by simpa [← hMin] using hMinDvd)
      exact (lt_irrefl (p : Real)) hpStrict

/-- The threshold fiber is multiplication by `p` from the weakly sifted
dilation, including repeated least prime factors. -/
theorem weakPrimeThresholdFiber_eq_dilation
    (C : Finset Nat) {p : Nat} (hp : p.Prime) :
    weakPrimeThresholdFiber C p =
      (weakSiftedCarrier (sieveDilation C ⟨p, hp.pos⟩)
        (p : Real)).map
          ⟨fun m => m * p, mul_left_injective₀ hp.ne_zero⟩ := by
  simpa only [weakPrimeThresholdFiber] using
    weakSiftedCarrier_sdiff_strict_eq_primeFiber C hp

/-- Distinct primes give disjoint least-prime-factor fibers. -/
theorem weakPrimeThresholdFiber_pairwiseDisjoint
    (C : Finset Nat) (z1 z2 : Real) :
    (sievePrimeInterval z1 z2 : Set Nat).PairwiseDisjoint
      (weakPrimeThresholdFiber C) := by
  classical
  intro p hpMem q hqMem hpq
  have hp := (mem_sievePrimeInterval.mp hpMem).1
  have hq := (mem_sievePrimeInterval.mp hqMem).1
  change Disjoint (weakPrimeThresholdFiber C p)
    (weakPrimeThresholdFiber C q)
  rw [weakPrimeThresholdFiber_eq_filter_minFac C hp,
    weakPrimeThresholdFiber_eq_filter_minFac C hq]
  rw [Finset.disjoint_left]
  intro n hnp hnq
  rw [Finset.mem_filter] at hnp hnq
  exact hpq (hnp.2.symm.trans hnq.2)

/-- The high-threshold strict carrier is disjoint from every removed prime
fiber. -/
theorem strictSiftedCarrier_disjoint_buchstabFibers
    (C : Finset Nat) {z1 z2 : Real} :
    Disjoint (strictSiftedCarrier C z2)
      ((sievePrimeInterval z1 z2).biUnion
        (weakPrimeThresholdFiber C)) := by
  classical
  rw [Finset.disjoint_left]
  intro n hnStrict hnFibers
  rcases Finset.mem_biUnion.mp hnFibers with ⟨p, hpMem, hnp⟩
  have hpData := mem_sievePrimeInterval.mp hpMem
  rw [weakPrimeThresholdFiber_eq_filter_minFac C hpData.1,
    Finset.mem_filter] at hnp
  have hpDvd : p ∣ n := by
    rw [← hnp.2]
    exact Nat.minFac_dvd n
  have hz2p := (mem_strictSiftedCarrier.mp hnStrict).2 p hpData.1 hpDvd
  exact (not_lt_of_ge hpData.2.2) hz2p

/-- Raising a strict threshold removes exactly the disjoint weak fibers at
the intervening primes. -/
theorem strictSiftedCarrier_union_buchstabFibers
    (C : Finset Nat) {z1 z2 : Real} (hz : z1 <= z2) :
    strictSiftedCarrier C z2 ∪
        (sievePrimeInterval z1 z2).biUnion
          (weakPrimeThresholdFiber C) =
      strictSiftedCarrier C z1 := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_union.mp hn with hnStrict | hnFiber
    · rw [mem_strictSiftedCarrier] at hnStrict ⊢
      exact ⟨hnStrict.1, fun p hp hpd =>
        hz.trans_lt (hnStrict.2 p hp hpd)⟩
    · rcases Finset.mem_biUnion.mp hnFiber with ⟨p, hpMem, hnp⟩
      have hpData := mem_sievePrimeInterval.mp hpMem
      rw [mem_weakPrimeThresholdFiber] at hnp
      rw [mem_strictSiftedCarrier]
      exact ⟨hnp.1, fun r hr hrd =>
        hpData.2.1.trans_le (hnp.2.1 r hr hrd)⟩
  · intro hnLow
    by_cases hnHigh : n ∈ strictSiftedCarrier C z2
    · exact Finset.mem_union.mpr (Or.inl hnHigh)
    · apply Finset.mem_union.mpr
      apply Or.inr
      have hnLowData := mem_strictSiftedCarrier.mp hnLow
      have hn1 : n ≠ 1 := by
        intro hn
        subst n
        apply hnHigh
        simpa using hnLowData.1
      have hp := Nat.minFac_prime hn1
      have hpDvd := Nat.minFac_dvd n
      have hpLower : z1 < (n.minFac : Real) :=
        hnLowData.2 n.minFac hp hpDvd
      have hnNotRough : ¬strictRoughPredicate z2 n := by
        intro hrough
        exact hnHigh (mem_strictSiftedCarrier.mpr ⟨hnLowData.1, hrough⟩)
      simp only [strictRoughPredicate] at hnNotRough
      push Not at hnNotRough
      obtain ⟨q, hq, hqd, hqUpper⟩ := hnNotRough
      have hpUpper : (n.minFac : Real) <= z2 := by
        calc
          (n.minFac : Real) <= (q : Real) := by
            exact_mod_cast Nat.minFac_le_of_dvd hq.two_le hqd
          _ <= z2 := hqUpper
      apply Finset.mem_biUnion.mpr
      refine ⟨n.minFac,
        mem_sievePrimeInterval.mpr ⟨hp, hpLower, hpUpper⟩, ?_⟩
      rw [weakPrimeThresholdFiber_eq_filter_minFac C hp,
        Finset.mem_filter]
      exact ⟨hnLowData.1, rfl⟩

/-- Reindex one threshold fiber by its weakly sifted cofactor carrier. -/
theorem sum_weakPrimeThresholdFiber_eq_dilation
    {M : Type*} [AddCommMonoid M]
    (C : Finset Nat) {p : Nat} (hp : p.Prime) (w : Nat -> M) :
    (∑ n ∈ weakPrimeThresholdFiber C p, w n) =
      ∑ m ∈ weakSiftedCarrier (sieveDilation C ⟨p, hp.pos⟩)
          (p : Real), w (m * p) := by
  rw [weakPrimeThresholdFiber_eq_dilation C hp]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro m _
  rfl

/-- Weighted finite Buchstab identity in threshold-fiber form. -/
theorem sum_strictSiftedCarrier_buchstab
    {M : Type*} [AddCommMonoid M]
    (C : Finset Nat) {z1 z2 : Real} (hz : z1 <= z2)
    (w : Nat -> M) :
    (∑ n ∈ strictSiftedCarrier C z2, w n) +
        ∑ p ∈ sievePrimeInterval z1 z2,
          ∑ n ∈ weakPrimeThresholdFiber C p, w n =
      ∑ n ∈ strictSiftedCarrier C z1, w n := by
  classical
  have hpair := weakPrimeThresholdFiber_pairwiseDisjoint C z1 z2
  have hdisjoint :=
    strictSiftedCarrier_disjoint_buchstabFibers C (z1 := z1) (z2 := z2)
  calc
    (∑ n ∈ strictSiftedCarrier C z2, w n) +
          ∑ p ∈ sievePrimeInterval z1 z2,
            ∑ n ∈ weakPrimeThresholdFiber C p, w n =
        (∑ n ∈ strictSiftedCarrier C z2, w n) +
          ∑ n ∈ (sievePrimeInterval z1 z2).biUnion
            (weakPrimeThresholdFiber C), w n := by
      rw [Finset.sum_biUnion hpair]
    _ = ∑ n ∈ strictSiftedCarrier C z2 ∪
          (sievePrimeInterval z1 z2).biUnion
            (weakPrimeThresholdFiber C), w n :=
      (Finset.sum_union hdisjoint).symm
    _ = ∑ n ∈ strictSiftedCarrier C z1, w n := by
      rw [strictSiftedCarrier_union_buchstabFibers C hz]

/-- Cardinal form of the exact weak-fiber Buchstab identity. -/
theorem card_strictSiftedCarrier_buchstab
    (C : Finset Nat) {z1 z2 : Real} (hz : z1 <= z2) :
    (strictSiftedCarrier C z2).card +
        ∑ p ∈ sievePrimeInterval z1 z2,
          (weakPrimeThresholdFiber C p).card =
      (strictSiftedCarrier C z1).card := by
  simpa using sum_strictSiftedCarrier_buchstab
    (M := Nat) C hz (fun _ => 1)

end PrimesRestrictedDigits
