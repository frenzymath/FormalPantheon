import PrimesRestrictedDigits.SieveAsymptotics.DecimalDimensionOneProduct
import PrimesRestrictedDigits.SieveAsymptotics.IwaniecDensity

/-!
# Finite decimal sieve density ratios

This identifies the quotient of two finite cutoff densities with Iwaniec's inverse Euler
product on `[w,z)` and applies the decimal dimension-one bound.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem reciprocal_prime_factor_pos {p : Nat} (hp : p.Prime) :
    0 < 1 - (p : Real)⁻¹ := by
  have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hpOne)

/-- Every finite density with reciprocal prime local weights is positive. -/
theorem sieveDensityBelow_reciprocal_pos
    (P : Finset Nat) (z : Real) (hprime : ∀ p ∈ P, p.Prime) :
    0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z := by
  rw [sieveDensityBelow]
  apply Finset.prod_pos
  intro p hp
  exact reciprocal_prime_factor_pos (hprime p (Finset.mem_filter.mp hp).1)

/-- Split a strict finite density prefix at the exact half-open interval
`[w,z)`. No sign or primality assumption is required. -/
theorem sieveDensityBelow_eq_mul_intervalProduct
    (P : Finset Nat) (nu : Nat -> Real) {w z : Real} (hwz : w <= z) :
    sieveDensityBelow P nu z =
      sieveDensityBelow P nu w *
        ∏ p ∈ P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z), (1 - nu p) := by
  have hdisjoint : Disjoint
      (P.filter (fun p : Nat => (p : Real) < w))
      (P.filter (fun p : Nat => w <= (p : Real) ∧ (p : Real) < z)) := by
    rw [Finset.disjoint_left]
    intro p hpw hpInterval
    simp only [Finset.mem_filter] at hpw hpInterval
    linarith
  have hpartition :
      P.filter (fun p : Nat => (p : Real) < z) =
        P.filter (fun p : Nat => (p : Real) < w) ∪
          P.filter (fun p : Nat =>
            w <= (p : Real) ∧ (p : Real) < z) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hp
      by_cases hpw : (p : Real) < w
      · exact Or.inl ⟨hp.1, hpw⟩
      · exact Or.inr ⟨hp.1, le_of_not_gt hpw, hp.2⟩
    · rintro (⟨hpP, hpw⟩ | ⟨hpP, _, hpz⟩)
      · exact ⟨hpP, hpw.trans_le hwz⟩
      · exact ⟨hpP, hpz⟩
  rw [sieveDensityBelow, hpartition, Finset.prod_union hdisjoint,
    sieveDensityBelow]

/-- At reciprocal prime weights, the ratio of two cutoff densities is the
inverse Euler product on `[w,z)`. -/
theorem sieveDensityBelow_div_eq_intervalInverseProduct
    (P : Finset Nat) {w z : Real} (hwz : w <= z)
    (hprime : ∀ p ∈ P, p.Prime) :
    sieveDensityBelow P (fun p => (p : Real)⁻¹) w /
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z =
      ∏ p ∈ P.filter (fun p : Nat =>
        w <= (p : Real) ∧ (p : Real) < z),
        (1 - (p : Real)⁻¹)⁻¹ := by
  let A := P.filter (fun p : Nat => (p : Real) < w)
  let B := P.filter (fun p : Nat =>
    w <= (p : Real) ∧ (p : Real) < z)
  have hApos : 0 < ∏ p ∈ A, (1 - (p : Real)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    exact reciprocal_prime_factor_pos
      (hprime p (Finset.mem_filter.mp hp).1)
  have hBpos : 0 < ∏ p ∈ B, (1 - (p : Real)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    exact reciprocal_prime_factor_pos
      (hprime p (Finset.mem_filter.mp hp).1)
  have hdecomp := sieveDensityBelow_eq_mul_intervalProduct
    P (fun p => (p : Real)⁻¹) hwz
  change sieveDensityBelow P (fun p => (p : Real)⁻¹) z =
      sieveDensityBelow P (fun p => (p : Real)⁻¹) w *
        ∏ p ∈ B, (1 - (p : Real)⁻¹) at hdecomp
  change sieveDensityBelow P (fun p => (p : Real)⁻¹) w /
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z =
    ∏ p ∈ B, (1 - (p : Real)⁻¹)⁻¹
  rw [hdecomp, Finset.prod_inv_distrib]
  have hVw : sieveDensityBelow P (fun p => (p : Real)⁻¹) w =
      ∏ p ∈ A, (1 - (p : Real)⁻¹) := rfl
  rw [hVw]
  field_simp [ne_of_gt hApos, ne_of_gt hBpos]

/-- Reciprocal-prime cutoff densities decrease as the real cutoff grows. -/
theorem antitone_sieveDensityBelow_reciprocal
    (P : Finset Nat) (hprime : ∀ p ∈ P, p.Prime) :
    Antitone (sieveDensityBelow P (fun p => (p : Real)⁻¹)) := by
  intro w z hwz
  let B := P.filter (fun p : Nat =>
    w <= (p : Real) ∧ (p : Real) < z)
  have hBnonneg : ∀ p ∈ B, 0 <= 1 - (p : Real)⁻¹ := by
    intro p hp
    exact (reciprocal_prime_factor_pos
      (hprime p (Finset.mem_filter.mp hp).1)).le
  have hBle : ∀ p ∈ B, 1 - (p : Real)⁻¹ <= 1 := by
    intro p hp
    have hpPrime := hprime p (Finset.mem_filter.mp hp).1
    have hpPos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have : 0 <= (p : Real)⁻¹ := (inv_pos.mpr hpPos).le
    linarith
  calc
    sieveDensityBelow P (fun p => (p : Real)⁻¹) z =
        sieveDensityBelow P (fun p => (p : Real)⁻¹) w *
          ∏ p ∈ B, (1 - (p : Real)⁻¹) := by
      simpa [B] using sieveDensityBelow_eq_mul_intervalProduct
        P (fun p => (p : Real)⁻¹) hwz
    _ <= sieveDensityBelow P (fun p => (p : Real)⁻¹) w * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.prod_le_one hBnonneg hBle
      · exact (sieveDensityBelow_reciprocal_pos P w hprime).le
    _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) w := mul_one _

/-- A finite set of decimal-admissible primes contributes no more than the
complete decimal-prime inverse product on the same interval. -/
theorem sieveDensityRatio_le_decimalIntervalPrimeInverseProduct
    (P : Finset Nat) {w z : Real} (hwz : w <= z)
    (hprime : ∀ p ∈ P, p.Prime) (hdecimal : ∀ p ∈ P, ¬p ∣ 10) :
    sieveDensityBelow P (fun p => (p : Real)⁻¹) w /
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z <=
      decimalIntervalPrimeInverseProduct w z := by
  rw [sieveDensityBelow_div_eq_intervalInverseProduct P hwz hprime]
  let S := P.filter (fun p : Nat =>
    w <= (p : Real) ∧ (p : Real) < z)
  let T := (naturalLeftClosedRightOpenInterval w z).filter
    (fun p => p.Prime ∧ ¬p ∣ 10)
  change (∏ p ∈ S, (1 - (p : Real)⁻¹)⁻¹) <=
    ∏ p ∈ T, (1 - (p : Real)⁻¹)⁻¹
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨mem_naturalLeftClosedRightOpenInterval.mpr hpData.2, ?_⟩
    exact ⟨hprime p hpData.1, hdecimal p hpData.1⟩
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact inv_nonneg.mpr
      (reciprocal_prime_factor_pos (hprime p hpData.1)).le
  · intro p hpT hpS
    have hpPrime := (Finset.mem_filter.mp hpT).2.1
    have hfactor := reciprocal_prime_factor_pos hpPrime
    apply (one_le_inv₀ hfactor).mpr
    have hpPos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have : 0 < (p : Real)⁻¹ := inv_pos.mpr hpPos
    linarith

/-- One dimension-one coefficient, chosen before the finite prime set and both
cutoffs, bounds every decimal reciprocal density ratio. -/
theorem exists_decimalSieveDensityRatio_bound :
    ∃ K : Real, 2 <= K ∧ ∀ (P : Finset Nat) (w z : Real),
      (∀ p ∈ P, p.Prime) -> (∀ p ∈ P, ¬p ∣ 10) ->
      2 <= w -> w < z ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) w /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z <
        (Real.log z / Real.log w) * (1 + K / Real.log w) := by
  obtain ⟨K, hK, hbound⟩ := exists_decimalDimensionOneProduct_bound
  refine ⟨K, hK, ?_⟩
  intro P w z hprime hdecimal hw hwz
  exact (sieveDensityRatio_le_decimalIntervalPrimeInverseProduct P hwz.le
    hprime hdecimal).trans_lt (hbound w z hw hwz)

end PrimesRestrictedDigits
