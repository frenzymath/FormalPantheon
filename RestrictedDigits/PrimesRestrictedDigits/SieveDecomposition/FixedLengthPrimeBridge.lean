import PrimesRestrictedDigits.SieveDecomposition.SectionSixCutoffs
import PrimesRestrictedDigits.SieveDecomposition.SectionSixWeight
import PrimesRestrictedDigits.SieveDecomposition.RoughBridge

/-!
# Fixed-length prime and rough-carrier bridge

This file gives the exact finite interpretation of the Section 6 weighted sifted sums at the
first and fourth cutoffs. The admitted unit and primes at or below the square-root cutoff
remain explicit correction carriers.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 138--139, Eqs. (6.3)--(6.4).
-/

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def paddedRestrictedPrimes
    (digit : Fin 10) (length : Nat) : Finset Nat :=
  (paddedRestrictedNumbers digit length).filter Nat.Prime

noncomputable def paddedRestrictedPrimeCount
    (digit : Fin 10) (length : Nat) : Nat :=
  (paddedRestrictedPrimes digit length).card

noncomputable def paddedRestrictedSmallPrimes
    (digit : Fin 10) (length : Nat) (z : Real) : Finset Nat :=
  (paddedRestrictedPrimes digit length).filter
    (fun p => (p : Real) <= z)

noncomputable def paddedRestrictedLargePrimes
    (digit : Fin 10) (length : Nat) (z : Real) : Finset Nat :=
  (paddedRestrictedPrimes digit length).filter
    (fun p => z < (p : Real))

noncomputable def paddedRestrictedUnitCarrier
    (digit : Fin 10) (length : Nat) : Finset Nat :=
  (paddedRestrictedNumbers digit length).filter (fun n => n = 1)

@[simp] theorem mem_paddedRestrictedPrimes
    {digit : Fin 10} {length n : Nat} :
    n ∈ paddedRestrictedPrimes digit length ↔
      n ∈ paddedRestrictedNumbers digit length ∧ n.Prime := by
  simp [paddedRestrictedPrimes]

@[simp] theorem mem_paddedRestrictedSmallPrimes
    {digit : Fin 10} {length n : Nat} {z : Real} :
    n ∈ paddedRestrictedSmallPrimes digit length z ↔
      n ∈ paddedRestrictedNumbers digit length ∧ n.Prime ∧
        (n : Real) <= z := by
  simp only [paddedRestrictedSmallPrimes, Finset.mem_filter,
    mem_paddedRestrictedPrimes]
  tauto

@[simp] theorem mem_paddedRestrictedLargePrimes
    {digit : Fin 10} {length n : Nat} {z : Real} :
    n ∈ paddedRestrictedLargePrimes digit length z ↔
      n ∈ paddedRestrictedNumbers digit length ∧ n.Prime ∧
        z < (n : Real) := by
  simp only [paddedRestrictedLargePrimes, Finset.mem_filter,
    mem_paddedRestrictedPrimes]
  tauto

@[simp] theorem mem_paddedRestrictedUnitCarrier
    {digit : Fin 10} {length n : Nat} :
    n ∈ paddedRestrictedUnitCarrier digit length ↔
      n ∈ paddedRestrictedNumbers digit length ∧ n = 1 := by
  simp [paddedRestrictedUnitCarrier]

private theorem sectionSix_powTen_ge_four
    {length : Nat} (hlength : 1 <= length) :
    (4 : Real) <= ((10 ^ length : Nat) : Real) := by
  have hten : 10 <= 10 ^ length := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 10) hlength)
  exact_mod_cast (show 4 <= 10 ^ length by omega)

theorem strictRoughPredicate_sqrt_iff_eq_one_or_prime
    {X : Real} {n : Nat} (hX : 4 <= X) (hnX : (n : Real) < X) :
    strictRoughPredicate (Real.sqrt X) n ↔
      n = 1 ∨ (n.Prime ∧ Real.sqrt X < (n : Real)) := by
  have hX0 : 0 <= X := by linarith
  have hsqrtTwo : (2 : Real) <= Real.sqrt X := by
    rw [Real.le_sqrt (by norm_num) hX0]
    norm_num
    exact hX
  constructor
  · intro hrough
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    right
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      have := strictRoughPredicate_zero.mp hrough
      linarith
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hnprime : n.Prime
    · exact ⟨hnprime, hrough n hnprime dvd_rfl⟩
    · have hqprime : n.minFac.Prime := Nat.minFac_prime hn1
      have hqrough : Real.sqrt X < (n.minFac : Real) :=
        hrough n.minFac hqprime (Nat.minFac_dvd n)
      have hqsqNat : n.minFac ^ 2 <= n :=
        Nat.minFac_sq_le_self hnpos hnprime
      have hqsqReal : (n.minFac : Real) ^ 2 <= (n : Real) := by
        exact_mod_cast hqsqNat
      have hsqrtSq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX0
      have : X < (n.minFac : Real) ^ 2 := by
        nlinarith [Real.sqrt_nonneg X]
      linarith
  · rintro (rfl | ⟨hnprime, hnlarge⟩)
    · exact strictRoughPredicate_one _
    · intro p hp hpd
      have hpn : p = n :=
        (Nat.prime_dvd_prime_iff_eq hp hnprime).mp hpd
      simpa [hpn] using hnlarge

theorem strictSiftedCarrier_paddedRestrictedNumbers_zFour
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    strictSiftedCarrier (paddedRestrictedNumbers digit length)
        (sectionSixZFour ((10 ^ length : Nat) : Real)) =
      paddedRestrictedUnitCarrier digit length ∪
        paddedRestrictedLargePrimes digit length
          (sectionSixZFour ((10 ^ length : Nat) : Real)) := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 4 <= X := sectionSix_powTen_ge_four hlength
  ext n
  constructor
  · intro hn
    rw [mem_strictSiftedCarrier] at hn
    have hnX : (n : Real) < X := by
      change (n : Real) < ((10 ^ length : Nat) : Real)
      exact_mod_cast (mem_paddedRestrictedNumbers.mp hn.1).1
    have hclass :=
      (strictRoughPredicate_sqrt_iff_eq_one_or_prime hX hnX).mp hn.2
    rw [Finset.mem_union]
    rcases hclass with hn1 | ⟨hnprime, hnlarge⟩
    · left
      exact mem_paddedRestrictedUnitCarrier.mpr ⟨hn.1, hn1⟩
    · right
      exact mem_paddedRestrictedLargePrimes.mpr
        ⟨hn.1, hnprime, hnlarge⟩
  · intro hn
    rw [Finset.mem_union] at hn
    rw [mem_strictSiftedCarrier]
    rcases hn with hnunit | hnlarge
    · have hnunitData := mem_paddedRestrictedUnitCarrier.mp hnunit
      refine ⟨hnunitData.1, ?_⟩
      rw [sectionSixZFour]
      have hnX : (n : Real) < X := by
        change (n : Real) < ((10 ^ length : Nat) : Real)
        exact_mod_cast (mem_paddedRestrictedNumbers.mp hnunitData.1).1
      exact (strictRoughPredicate_sqrt_iff_eq_one_or_prime hX hnX).mpr
        (Or.inl hnunitData.2)
    · have hnlargeData := mem_paddedRestrictedLargePrimes.mp hnlarge
      refine ⟨hnlargeData.1, ?_⟩
      rw [sectionSixZFour]
      have hnX : (n : Real) < X := by
        change (n : Real) < ((10 ^ length : Nat) : Real)
        exact_mod_cast (mem_paddedRestrictedNumbers.mp hnlargeData.1).1
      exact (strictRoughPredicate_sqrt_iff_eq_one_or_prime hX hnX).mpr
        (Or.inr ⟨hnlargeData.2.1, hnlargeData.2.2⟩)

theorem paddedRestrictedUnitCarrier_disjoint_largePrimes
    (digit : Fin 10) (length : Nat) (z : Real) :
    Disjoint (paddedRestrictedUnitCarrier digit length)
      (paddedRestrictedLargePrimes digit length z) := by
  classical
  rw [Finset.disjoint_left]
  intro n hnunit hnlarge
  have hnunitData := mem_paddedRestrictedUnitCarrier.mp hnunit
  have hnlargeData := mem_paddedRestrictedLargePrimes.mp hnlarge
  exact Nat.not_prime_one (hnunitData.2 ▸ hnlargeData.2.1)

theorem paddedRestrictedPrimes_eq_small_union_large
    (digit : Fin 10) (length : Nat) (z : Real) :
    paddedRestrictedPrimes digit length =
      paddedRestrictedSmallPrimes digit length z ∪
        paddedRestrictedLargePrimes digit length z := by
  classical
  ext n
  simp only [Finset.mem_union, mem_paddedRestrictedSmallPrimes,
    mem_paddedRestrictedLargePrimes, mem_paddedRestrictedPrimes]
  constructor
  · intro hn
    rcases le_or_gt (n : Real) z with hnz | hnz
    · exact Or.inl ⟨hn.1, hn.2, hnz⟩
    · exact Or.inr ⟨hn.1, hn.2, hnz⟩
  · rintro (⟨hn, hp, _⟩ | ⟨hn, hp, _⟩) <;> exact ⟨hn, hp⟩

theorem paddedRestrictedSmallPrimes_disjoint_largePrimes
    (digit : Fin 10) (length : Nat) (z : Real) :
    Disjoint (paddedRestrictedSmallPrimes digit length z)
      (paddedRestrictedLargePrimes digit length z) := by
  classical
  rw [Finset.disjoint_left]
  intro n hnsmall hnlarge
  exact (not_lt_of_ge (mem_paddedRestrictedSmallPrimes.mp hnsmall).2.2)
    (mem_paddedRestrictedLargePrimes.mp hnlarge).2.2

theorem paddedRestrictedPrimeCount_eq_sectionSixSiftedSum_zFour
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z4 : Real := sectionSixZFour X
    (paddedRestrictedPrimeCount digit length : Real) =
      sectionSixSiftedSum digit length 1 z4 +
        ((restrictedDigitDensity digit : Real) *
          (((paddedRestrictedNumbers digit length).card : Real) / X)) *
          (maynardStrictRoughCount X z4 : Real) +
        ((paddedRestrictedSmallPrimes digit length z4).card : Real) -
        ((paddedRestrictedUnitCarrier digit length).card : Real) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let z4 : Real := sectionSixZFour X
  change (paddedRestrictedPrimeCount digit length : Real) =
    sectionSixSiftedSum digit length 1 z4 +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) / X)) *
        (maynardStrictRoughCount X z4 : Real) +
      ((paddedRestrictedSmallPrimes digit length z4).card : Real) -
      ((paddedRestrictedUnitCarrier digit length).card : Real)
  have hX : 4 <= X := sectionSix_powTen_ge_four hlength
  have hz4 : 2 <= z4 := by
    dsimp only [z4, sectionSixZFour]
    rw [Real.le_sqrt (by norm_num) (by linarith : 0 <= X)]
    norm_num
    exact hX
  have hroughSet :
      strictSiftedCarrier (paddedRestrictedNumbers digit length) z4 =
        paddedRestrictedUnitCarrier digit length ∪
          paddedRestrictedLargePrimes digit length z4 := by
    simpa only [X, z4] using
      strictSiftedCarrier_paddedRestrictedNumbers_zFour digit hlength
  have hroughCard :
      (strictSiftedCarrier
        (paddedRestrictedNumbers digit length) z4).card =
        (paddedRestrictedUnitCarrier digit length).card +
          (paddedRestrictedLargePrimes digit length z4).card := by
    rw [hroughSet, Finset.card_union_of_disjoint
      (paddedRestrictedUnitCarrier_disjoint_largePrimes digit length z4)]
  have hprimeCard :
      paddedRestrictedPrimeCount digit length =
        (paddedRestrictedSmallPrimes digit length z4).card +
          (paddedRestrictedLargePrimes digit length z4).card := by
    rw [paddedRestrictedPrimeCount,
      paddedRestrictedPrimes_eq_small_union_large,
      Finset.card_union_of_disjoint
        (paddedRestrictedSmallPrimes_disjoint_largePrimes digit length z4)]
  have hambientCard :
      (strictSiftedCarrier (maynardAmbientCarrier X) z4).card =
        maynardStrictRoughCount X z4 := by
    have h := card_strictSiftedCarrier_sieveDilation_maynardAmbientCarrier
      (X := X) (z := z4) (1 : PNat) hz4
    norm_num at h
    simpa only [sieveDilation_one] using h
  have hsift := sectionSixSiftedSum_eq_card_sub_density_mul_card
    digit length (1 : PNat) z4
  rw [sieveDilation_one, sieveDilation_one, hambientCard] at hsift
  have hroughCardReal :
      ((strictSiftedCarrier
        (paddedRestrictedNumbers digit length) z4).card : Real) =
        ((paddedRestrictedUnitCarrier digit length).card : Real) +
          ((paddedRestrictedLargePrimes digit length z4).card : Real) := by
    exact_mod_cast hroughCard
  have hprimeCardReal :
      (paddedRestrictedPrimeCount digit length : Real) =
        ((paddedRestrictedSmallPrimes digit length z4).card : Real) +
          ((paddedRestrictedLargePrimes digit length z4).card : Real) := by
    exact_mod_cast hprimeCard
  rw [hroughCardReal] at hsift
  rw [hprimeCardReal]
  linarith

theorem paddedRestrictedPrimeCount_le_zOne_sifted_add_small
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    paddedRestrictedPrimeCount digit length <=
      (strictSiftedCarrier (paddedRestrictedNumbers digit length)
        (sectionSixZOne epsilon X)).card +
      (paddedRestrictedSmallPrimes digit length
        (sectionSixZFour X)).card := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z4 : Real := sectionSixZFour X
  change paddedRestrictedPrimeCount digit length <=
    (strictSiftedCarrier (paddedRestrictedNumbers digit length) z1).card +
      (paddedRestrictedSmallPrimes digit length z4).card
  have hXone : 1 < X :=
    lt_of_lt_of_le (by norm_num : (1 : Real) < 4)
      (sectionSix_powTen_ge_four hlength)
  have hcut := sectionSix_cutoffs_strict hepsilon hepsilonSmall hXone
  have hz1z4 : z1 < z4 :=
    hcut.1.trans (hcut.2.1.trans hcut.2.2.1)
  have hsub : paddedRestrictedPrimes digit length ⊆
      strictSiftedCarrier (paddedRestrictedNumbers digit length) z1 ∪
        paddedRestrictedSmallPrimes digit length z4 := by
    intro p hp
    rw [Finset.mem_union]
    have hpData := mem_paddedRestrictedPrimes.mp hp
    by_cases hpSmall : (p : Real) <= z4
    · right
      exact mem_paddedRestrictedSmallPrimes.mpr
        ⟨hpData.1, hpData.2, hpSmall⟩
    · left
      rw [mem_strictSiftedCarrier]
      refine ⟨hpData.1, ?_⟩
      intro q hq hqp
      have hqpEq : q = p :=
        (Nat.prime_dvd_prime_iff_eq hq hpData.2).mp hqp
      subst q
      exact hz1z4.trans (lt_of_not_ge hpSmall)
  calc
    paddedRestrictedPrimeCount digit length =
        (paddedRestrictedPrimes digit length).card := rfl
    _ <= (strictSiftedCarrier
        (paddedRestrictedNumbers digit length) z1 ∪
          paddedRestrictedSmallPrimes digit length z4).card :=
      Finset.card_le_card hsub
    _ <= (strictSiftedCarrier
        (paddedRestrictedNumbers digit length) z1).card +
          (paddedRestrictedSmallPrimes digit length z4).card :=
      Finset.card_union_le _ _

theorem paddedRestrictedPrimeCount_le_sectionSixSiftedSum_zOne_add_small
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z4 : Real := sectionSixZFour X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) / X)
    (paddedRestrictedPrimeCount digit length : Real) <=
      sectionSixSiftedSum digit length 1 z1 +
        lambda *
          ((strictSiftedCarrier (maynardAmbientCarrier X) z1).card : Real) +
        ((paddedRestrictedSmallPrimes digit length z4).card : Real) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z4 : Real := sectionSixZFour X
  change (paddedRestrictedPrimeCount digit length : Real) <=
    sectionSixSiftedSum digit length 1 z1 +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) / X)) *
        ((strictSiftedCarrier (maynardAmbientCarrier X) z1).card : Real) +
      ((paddedRestrictedSmallPrimes digit length z4).card : Real)
  have hnat := paddedRestrictedPrimeCount_le_zOne_sifted_add_small
    hepsilon hepsilonSmall digit hlength
  change paddedRestrictedPrimeCount digit length <=
    (strictSiftedCarrier (paddedRestrictedNumbers digit length) z1).card +
      (paddedRestrictedSmallPrimes digit length z4).card at hnat
  have hreal : (paddedRestrictedPrimeCount digit length : Real) <=
      ((strictSiftedCarrier
        (paddedRestrictedNumbers digit length) z1).card : Real) +
        ((paddedRestrictedSmallPrimes digit length z4).card : Real) := by
    exact_mod_cast hnat
  have hsift := sectionSixSiftedSum_eq_card_sub_density_mul_card
    digit length (1 : PNat) z1
  rw [sieveDilation_one, sieveDilation_one] at hsift
  change sectionSixSiftedSum digit length 1 z1 =
    ((strictSiftedCarrier
      (paddedRestrictedNumbers digit length) z1).card : Real) -
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) / X)) *
        ((strictSiftedCarrier (maynardAmbientCarrier X) z1).card : Real) at hsift
  linarith

theorem
    paddedRestrictedPrimeCount_le_sectionSixSiftedSum_zOne_rough_add_small
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (hz1 : 2 <= sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real)) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z4 : Real := sectionSixZFour X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) / X)
    (paddedRestrictedPrimeCount digit length : Real) <=
      sectionSixSiftedSum digit length 1 z1 +
        lambda * (maynardStrictRoughCount X z1 : Real) +
        ((paddedRestrictedSmallPrimes digit length z4).card : Real) := by
  have h :=
    paddedRestrictedPrimeCount_le_sectionSixSiftedSum_zOne_add_small
      hepsilon hepsilonSmall digit hlength
  dsimp only at h ⊢
  rw [strictSiftedCarrier_maynardAmbientCarrier_eq hz1] at h
  simpa only [maynardStrictRoughCount] using h

theorem card_paddedRestrictedUnitCarrier_le_one
    (digit : Fin 10) (length : Nat) :
    (paddedRestrictedUnitCarrier digit length).card <= 1 := by
  have hsub : paddedRestrictedUnitCarrier digit length ⊆ {1} := by
    intro n hn
    have hnData := mem_paddedRestrictedUnitCarrier.mp hn
    simpa only [Finset.mem_singleton] using hnData.2
  simpa using Finset.card_le_card hsub

theorem card_paddedRestrictedSmallPrimes_le_floor_add_one
    (digit : Fin 10) (length : Nat) {z : Real} (hz : 0 <= z) :
    (paddedRestrictedSmallPrimes digit length z).card <=
      Nat.floor z + 1 := by
  have hzFloor : z < ((Nat.floor z + 1 : Nat) : Real) :=
    (Nat.floor_lt hz).mp (Nat.lt_succ_self (Nat.floor z))
  have hsub : paddedRestrictedSmallPrimes digit length z ⊆
      Finset.range (Nat.floor z + 1) := by
    intro p hp
    rw [Finset.mem_range]
    have hpReal : (p : Real) < ((Nat.floor z + 1 : Nat) : Real) :=
      (mem_paddedRestrictedSmallPrimes.mp hp).2.2.trans_lt hzFloor
    exact_mod_cast hpReal
  simpa using Finset.card_le_card hsub

theorem paddedRestrictedPrimeCount_eq_restrictedPrimeCount_of_ne_zero
    {digit : Fin 10} (hdigit : digit.val ≠ 0) (length : Nat) :
    paddedRestrictedPrimeCount digit length =
      restrictedPrimeCount digit ((10 ^ length : Nat) : Real) := by
  rw [paddedRestrictedPrimeCount, paddedRestrictedPrimes,
    restrictedPrimeCount,
    restrictedNumbers_eq_paddedRestrictedNumbers_of_ne_zero hdigit]

end

end PrimesRestrictedDigits
