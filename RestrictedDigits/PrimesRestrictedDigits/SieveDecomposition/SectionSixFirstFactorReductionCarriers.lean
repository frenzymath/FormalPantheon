import PrimesRestrictedDigits.SieveDecomposition.FixedLengthPrimeBridge
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLedger

/-!
# First Section 6 factor-reduction carriers

This file realizes the factor increase as an exact difference of strict sifted carriers and
classifies every nonempty cofactor as an ordered prime factor. No asymptotic estimate is used
here.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140, Eq. (6.4).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Cofactors gained when the once-dilated threshold is lowered from `p` to
`min(p,sqrt(X/p))`. -/
def sectionSixFirstFactorTail
    (C : Finset Nat) (length p : Nat) : Finset Nat :=
  strictSiftedCarrier (sieveDilation C (Nat.toPNat' p))
      (sectionSixFirstFactorThreshold length p) \
    strictSiftedCarrier (sieveDilation C (Nat.toPNat' p)) (p : Real)

/-- Original represented values belonging to one factor tail. -/
def sectionSixFirstFactorRepresentedTail
    (C : Finset Nat) (length p : Nat) : Finset Nat :=
  (sectionSixFirstFactorTail C length p).image fun m => m * p

/-- Total raw tail cardinality over a finite outer-prime carrier. -/
def sectionSixFirstFactorTailSum
    (C : Finset Nat) (length : Nat) (primes : Finset Nat) : Real :=
  ∑ p ∈ primes,
    ((sectionSixFirstFactorTail C length p).card : Real)

/-- Positive base-carrier count over a prime interval. The length parameter
keeps this raw count aligned with the signed fixed-length notation. -/
def sectionSixFirstFactorBaseCountSum
    (C : Finset Nat) (_length : Nat) (z a b : Real) : Real :=
  ∑ p ∈ sievePrimeInterval a b,
    ((strictSiftedCarrier
      (sieveDilation C (Nat.toPNat' p)) z).card : Real)

/-- The union of the low and high outer-prime intervals in Eq. (6.5). -/
def sectionSixFirstFactorOuterPrimes
    (epsilon : Real) (length : Nat) : Finset Nat :=
  let X : Real := ((10 ^ length : Nat) : Real)
  sievePrimeInterval (sectionSixZOne epsilon X)
      (sectionSixZTwo epsilon X) ∪
    sievePrimeInterval (sectionSixZThree epsilon X)
      (sectionSixZFour X)

/-- Outer primes weakly below the fixed factor-reduction split. -/
def sectionSixFirstFactorFarPrimes
    (epsilon tau : Real) (length : Nat) : Finset Nat :=
  let X : Real := ((10 ^ length : Nat) : Real)
  (sectionSixFirstFactorOuterPrimes epsilon length).filter
    fun p => (p : Real) <= X ^ (1 / 2 - tau)

/-- Outer primes strictly above the fixed factor-reduction split. -/
def sectionSixFirstFactorNearPrimes
    (epsilon tau : Real) (length : Nat) : Finset Nat :=
  let X : Real := ((10 ^ length : Nat) : Real)
  (sectionSixFirstFactorOuterPrimes epsilon length).filter
    fun p => X ^ (1 / 2 - tau) < (p : Real)

private theorem sectionSixFirst_strictSiftedCarrier_threshold_subset
    (C : Finset Nat) {z0 z1 : Real} (hz : z0 <= z1) :
    strictSiftedCarrier C z1 ⊆ strictSiftedCarrier C z0 := by
  intro n hn
  rw [mem_strictSiftedCarrier] at hn ⊢
  refine ⟨hn.1, ?_⟩
  intro q hq hqn
  exact hz.trans_lt (hn.2 q hq hqn)

private theorem sectionSixFirst_card_sub_eq_sdiff
    {s t : Finset Nat} (h : t ⊆ s) :
    (s.card : Real) - (t.card : Real) = ((s \ t).card : Real) := by
  have hcard := Finset.card_sdiff_add_card_eq_card h
  have hcardReal : (((s \ t).card : Nat) : Real) + (t.card : Real) =
      (s.card : Real) := by
    exact_mod_cast hcard
  linarith

/-- One signed factor summand is exactly requested tail cardinality minus its
weighted ambient counterpart. -/
theorem sectionSixFirstFactorTerm_eq_tailDiscrepancy
    (digit : Fin 10) (length : Nat) {p : Nat} (hp : p.Prime) :
    sectionSixSiftedSum digit length (Nat.toPNat' p)
          (sectionSixFirstFactorThreshold length p) -
        sectionSixStrictPrimeTerm digit length 1 p =
      ((sectionSixFirstFactorTail
        (paddedRestrictedNumbers digit length) length p).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
          ((sectionSixFirstFactorTail
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              length p).card : Real) := by
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length 1 hp]
  simp only [one_mul]
  rw [sectionSixSiftedSum_eq_card_sub_density_mul_card,
    sectionSixSiftedSum_eq_card_sub_density_mul_card]
  have hthreshold :
      sectionSixFirstFactorThreshold length p <= (p : Real) :=
    min_le_left _ _
  have hA := sectionSixFirst_strictSiftedCarrier_threshold_subset
    (sieveDilation (paddedRestrictedNumbers digit length) (Nat.toPNat' p))
    hthreshold
  have hB := sectionSixFirst_strictSiftedCarrier_threshold_subset
    (sieveDilation
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
      (Nat.toPNat' p)) hthreshold
  have hAcard := sectionSixFirst_card_sub_eq_sdiff hA
  have hBcard := sectionSixFirst_card_sub_eq_sdiff hB
  calc
    _ =
        (((strictSiftedCarrier
          (sieveDilation (paddedRestrictedNumbers digit length)
            (Nat.toPNat' p))
          (sectionSixFirstFactorThreshold length p)).card : Real) -
        ((strictSiftedCarrier
          (sieveDilation (paddedRestrictedNumbers digit length)
            (Nat.toPNat' p)) (p : Real)).card : Real)) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
          (((strictSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              (Nat.toPNat' p))
            (sectionSixFirstFactorThreshold length p)).card : Real) -
          ((strictSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              (Nat.toPNat' p)) (p : Real)).card : Real)) := by ring
    _ = _ := by
      rw [hAcard, hBcard]
      rfl

/-- A nonempty factor tail consists exactly of a prime cofactor `m`, ordered
by `m<=p`, whose represented value belongs to the original carrier. -/
theorem mem_sectionSixFirstFactorTail_iff
    {C : Finset Nat} {length p m : Nat} (hp : p.Prime)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hquot : (4 : Real) <=
      ((10 ^ length : Nat) : Real) / (p : Real)) :
    m ∈ sectionSixFirstFactorTail C length p <->
      m * p ∈ C ∧ m.Prime ∧
        sectionSixFirstFactorThreshold length p < (m : Real) ∧ m <= p := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let Y : Real := X / (p : Real)
  have hpPos : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  constructor
  · intro hm
    rw [sectionSixFirstFactorTail, Finset.mem_sdiff] at hm
    have hmLow := mem_strictSiftedCarrier.mp hm.1
    have hmC : m * p ∈ C := by
      simpa [Nat.toPNat'_coe, hp.pos] using
        (mem_sieveDilation.mp hmLow.1)
    have hmAmbient := mem_maynardAmbientCarrier.mp (hC hmC)
    have hmY : (m : Real) < Y := by
      dsimp only [Y, X]
      rw [lt_div_iff₀ hpPos]
      exact_mod_cast hmAmbient
    by_cases hpsqrt : (p : Real) <= Real.sqrt Y
    · have hthreshold : sectionSixFirstFactorThreshold length p = (p : Real) := by
        simp only [sectionSixFirstFactorThreshold]
        exact min_eq_left hpsqrt
      have : m ∈ strictSiftedCarrier
          (sieveDilation C (Nat.toPNat' p)) (p : Real) := by
        simpa only [hthreshold] using hm.1
      exact (hm.2 this).elim
    · have hsqrtp : Real.sqrt Y < (p : Real) := lt_of_not_ge hpsqrt
      have hthreshold :
          sectionSixFirstFactorThreshold length p = Real.sqrt Y := by
        simp only [sectionSixFirstFactorThreshold, X, Y]
        exact min_eq_right hsqrtp.le
      have hmRough : strictRoughPredicate (Real.sqrt Y) m := by
        simpa only [hthreshold] using hmLow.2
      have hmClass :=
        (strictRoughPredicate_sqrt_iff_eq_one_or_prime
          (by simpa only [Y, X] using hquot) hmY).mp hmRough
      rcases hmClass with rfl | ⟨hmPrime, hmSqrt⟩
      · have hmAtP : 1 ∈ strictSiftedCarrier
            (sieveDilation C (Nat.toPNat' p)) (p : Real) := by
          rw [one_mem_strictSiftedCarrier]
          exact hmLow.1
        exact (hm.2 hmAtP).elim
      · have hmp : m <= p := by
          by_contra hnot
          have hpm : (p : Real) < (m : Real) := by
            exact_mod_cast (lt_of_not_ge hnot)
          apply hm.2
          rw [mem_strictSiftedCarrier]
          refine ⟨hmLow.1, ?_⟩
          intro q hq hqm
          have hqmEq : q = m :=
            (Nat.prime_dvd_prime_iff_eq hq hmPrime).mp hqm
          simpa only [hqmEq] using hpm
        exact ⟨hmC, hmPrime, by simpa only [hthreshold] using hmSqrt, hmp⟩
  · rintro ⟨hmC, hmPrime, hmThreshold, hmp⟩
    rw [sectionSixFirstFactorTail, Finset.mem_sdiff]
    constructor
    · rw [mem_strictSiftedCarrier, mem_sieveDilation]
      refine ⟨by simpa [Nat.toPNat'_coe, hp.pos] using hmC, ?_⟩
      intro q hq hqm
      have hqmEq : q = m :=
        (Nat.prime_dvd_prime_iff_eq hq hmPrime).mp hqm
      simpa only [hqmEq] using hmThreshold
    · intro hmAtP
      have hrough := (mem_strictSiftedCarrier.mp hmAtP).2 m hmPrime dvd_rfl
      exact (not_lt_of_ge (by exact_mod_cast hmp)) hrough

/-- Multiplication by a positive outer prime preserves the tail cardinality. -/
theorem card_sectionSixFirstFactorRepresentedTail
    (C : Finset Nat) (length : Nat) {p : Nat} (hp : p.Prime) :
    (sectionSixFirstFactorRepresentedTail C length p).card =
      (sectionSixFirstFactorTail C length p).card := by
  unfold sectionSixFirstFactorRepresentedTail
  rw [Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_right hp.pos hab

end

end PrimesRestrictedDigits
