import PrimesRestrictedDigits.BasicEstimates.DivisorSubpolynomial
import PrimesRestrictedDigits.LatticeEstimates.HybridSums
import PrimesRestrictedDigits.PrimeNumberTheorem.DecimalSmooth

/-!
# Decimal-smooth factor bands in the lattice estimate

This file proves the smooth-divisor cardinality input used after published Lemma 14.4 in the
proof of Proposition 13.3.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The source band `d ~ D`, restricted to products of powers of two and
five. -/
noncomputable def latticeSmoothFactorTenBand (D : Nat) : Finset Nat := by
  classical
  exact (latticeFactorTenBand D).filter IsDecimalSmooth

theorem mem_latticeSmoothFactorTenBand_iff {D d : Nat} :
    d ∈ latticeSmoothFactorTenBand D ↔
      d ∈ latticeFactorTenBand D ∧ IsDecimalSmooth d := by
  simp [latticeSmoothFactorTenBand]

/-- Every decimal-smooth natural at most `10^k` divides `10^(4*k)`. A larger
cover than `10^k` is necessary because, for example, `8 ~ 10` but `8 ∤ 10`;
the factor four is a convenient uniform choice. -/
theorem dvd_ten_pow_four_mul_of_isDecimalSmooth_le
    {k d : Nat} (hdSmooth : IsDecimalSmooth d) (hd : d ≤ 10 ^ k) :
    d ∣ 10 ^ (4 * k) := by
  obtain ⟨a, b, rfl⟩ :=
    (isDecimalSmooth_iff_exists_two_pow_mul_five_pow d).1 hdSmooth
  have htwo : 2 ^ a ≤ 10 ^ k := by
    calc
      2 ^ a = 2 ^ a * 1 := by simp
      _ ≤ 2 ^ a * 5 ^ b := by
        exact Nat.mul_le_mul_left _ (Nat.one_le_pow b 5 (by norm_num))
      _ ≤ 10 ^ k := hd
  have htwoScale : 10 ^ k ≤ 2 ^ (4 * k) := by
    calc
      10 ^ k ≤ 16 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = (2 ^ 4) ^ k := by norm_num
      _ = 2 ^ (4 * k) := (pow_mul 2 4 k).symm
  have ha : a ≤ 4 * k :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1
      (htwo.trans htwoScale)
  have hfive : 5 ^ b ≤ 10 ^ k := by
    calc
      5 ^ b = 1 * 5 ^ b := by simp
      _ ≤ 2 ^ a * 5 ^ b := by
        exact Nat.mul_le_mul_right _ (Nat.one_le_pow a 2 (by norm_num))
      _ ≤ 10 ^ k := hd
  have hfiveScale : 10 ^ k ≤ 5 ^ (2 * k) := by
    calc
      10 ^ k ≤ 25 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = (5 ^ 2) ^ k := by norm_num
      _ = 5 ^ (2 * k) := (pow_mul 5 2 k).symm
  have hb : b ≤ 4 * k := by
    have hbTwo : b ≤ 2 * k :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1
        (hfive.trans hfiveScale)
    omega
  have htwoDvd : 2 ^ a ∣ 2 ^ (4 * k) := Nat.pow_dvd_pow 2 ha
  have hfiveDvd : 5 ^ b ∣ 5 ^ (4 * k) := Nat.pow_dvd_pow 5 hb
  simpa only [show (10 : Nat) = 2 * 5 by norm_num, mul_pow] using
    Nat.mul_dvd_mul htwoDvd hfiveDvd

/-- The exact smooth factor-ten band at scale `10^k` is covered by one
finite divisor set. -/
theorem latticeSmoothFactorTenBand_subset_divisors_four_mul (k : Nat) :
    latticeSmoothFactorTenBand (10 ^ k) ⊆ (10 ^ (4 * k)).divisors := by
  intro d hd
  have hdata := mem_latticeSmoothFactorTenBand_iff.mp hd
  rw [Nat.mem_divisors]
  exact ⟨dvd_ten_pow_four_mul_of_isDecimalSmooth_le hdata.2
      (mem_latticeFactorTenBand_iff.mp hdata.1).2.1,
    by positivity⟩

private theorem ten_pow_four_mul_rpow_quarter
    (sigma : Real) (k : Nat) :
    (((10 ^ (4 * k) : Nat) : Real) ^ (sigma / 4)) =
      (((10 ^ k : Nat) : Real) ^ sigma) := by
  calc
    (((10 ^ (4 * k) : Nat) : Real) ^ (sigma / 4)) =
        (((10 : Real) ^ (4 * k)) ^ (sigma / 4)) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    _ = (((10 : Real) ^ ((4 * k : Nat) : Real)) ^ (sigma / 4)) := by
      rw [Real.rpow_natCast]
    _ = (10 : Real) ^ (((4 * k : Nat) : Real) * (sigma / 4)) :=
      (Real.rpow_mul (by norm_num : (0 : Real) ≤ 10) _ _).symm
    _ = (10 : Real) ^ ((k : Real) * sigma) := by
      congr 1
      push_cast
      ring
    _ = (((10 : Real) ^ (k : Real)) ^ sigma) :=
      Real.rpow_mul (by norm_num : (0 : Real) ≤ 10) _ _
    _ = (((10 : Real) ^ k) ^ sigma) := by rw [Real.rpow_natCast]
    _ = (((10 ^ k : Nat) : Real) ^ sigma) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]

/-- The number of decimal-smooth naturals in one factor-ten band is bounded
by a fixed multiple of every positive power of its decimal scale. -/
theorem exists_card_latticeSmoothFactorTenBand_le
    (sigma : Real) (hsigma : 0 < sigma) :
    ∃ C : Real, 0 < C ∧ ∀ k : Nat,
      ((latticeSmoothFactorTenBand (10 ^ k)).card : Real) ≤
        C * (((10 ^ k : Nat) : Real) ^ sigma) := by
  obtain ⟨C, hC, hdivisors⟩ :=
    card_divisors_le_const_mul_rpow (sigma / 4) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro k
  have hcard :
      (latticeSmoothFactorTenBand (10 ^ k)).card ≤
        (10 ^ (4 * k)).divisors.card :=
    Finset.card_le_card (latticeSmoothFactorTenBand_subset_divisors_four_mul k)
  have hcardReal :
      ((latticeSmoothFactorTenBand (10 ^ k)).card : Real) ≤
        ((10 ^ (4 * k)).divisors.card : Real) := by
    exact_mod_cast hcard
  calc
    ((latticeSmoothFactorTenBand (10 ^ k)).card : Real) ≤
        ((10 ^ (4 * k)).divisors.card : Real) := hcardReal
    _ ≤ C * (((10 ^ (4 * k) : Nat) : Real) ^ (sigma / 4)) :=
      hdivisors (10 ^ (4 * k))
    _ = C * (((10 ^ k : Nat) : Real) ^ sigma) := by
      rw [ten_pow_four_mul_rpow_quarter]

end

end PrimesRestrictedDigits
