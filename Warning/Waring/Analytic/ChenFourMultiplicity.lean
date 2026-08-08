import Waring.Analytic.PolynomialSums

/-!
# Multiplicity weights in Chen's Lemma 4

This file proves the common arithmetic endpoint of the derivative-root cases
in Chen's prime-power induction [CHEN1964-EN, pp. 1549-1550].
-/

namespace Waring.Analytic

open scoped BigOperators

private theorem eleven_rpow_neg_three_fifths_le :
    (11 : Real) ^ (-(3 / 5) : Real) ≤ 1 / 4 := by
  rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : Real) ≤ 1 / 4) (by norm_num : (5 : Nat) ≠ 0)]
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 11)]
  norm_num [Real.rpow_neg_ofNat]

private theorem eleven_rpow_neg_two_fifths_le :
    (11 : Real) ^ (-(2 / 5) : Real) ≤ 1 / 2 := by
  rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : Real) ≤ 1 / 2) (by norm_num : (5 : Nat) ≠ 0)]
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 11)]
  norm_num [Real.rpow_neg_ofNat]

private theorem eleven_rpow_neg_one_fifth_le :
    (11 : Real) ^ (-(1 / 5) : Real) ≤ 3 / 4 := by
  rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : Real) ≤ 3 / 4) (by norm_num : (5 : Nat) ≠ 0)]
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 11)]
  norm_num [Real.rpow_neg_ofNat]

/-- A critical residue of multiplicity `m` consumes at most the fraction
`m/4` of the normalized induction bound. -/
theorem chen_four_stationaryWeight_le_quarter (p m sigma : Nat)
    (hp : 11 ≤ p) (hmPos : 1 ≤ m) (hmFour : m ≤ 4)
    (hsigma : sigma ≤ m + 1) :
    (p : Real) ^ ((sigma : Real) / 5 - 1) ≤ (m : Real) / 4 := by
  have hpOne : (1 : Real) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hpEleven : (11 : Real) ≤ p := by exact_mod_cast hp
  have hexponent :
      (sigma : Real) / 5 - 1 ≤ ((m : Real) - 4) / 5 := by
    have hsigmaReal : (sigma : Real) ≤ m + 1 := by exact_mod_cast hsigma
    linarith
  calc
    (p : Real) ^ ((sigma : Real) / 5 - 1) ≤
        (p : Real) ^ (((m : Real) - 4) / 5) :=
      Real.rpow_le_rpow_of_exponent_le hpOne hexponent
    _ ≤ (11 : Real) ^ (((m : Real) - 4) / 5) := by
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hpEleven (by
        have hmReal : (m : Real) ≤ 4 := by exact_mod_cast hmFour
        linarith)
    _ ≤ (m : Real) / 4 := by
      interval_cases m <;> norm_num at hmPos ⊢
      · exact eleven_rpow_neg_three_fifths_le
      · exact eleven_rpow_neg_two_fifths_le
      · exact eleven_rpow_neg_one_fifth_le

/-- Since the derivative-root multiplicities sum to at most four, all
normalized stationary weights together are at most one. -/
theorem sum_chen_four_stationaryWeight_le_one {ι : Type*}
    (p : Nat) (s : Finset ι) (multiplicity sigma : ι → Nat)
    (hp : 11 ≤ p)
    (hmPos : ∀ i ∈ s, 1 ≤ multiplicity i)
    (hmSum : ∑ i ∈ s, multiplicity i ≤ 4)
    (hsigma : ∀ i ∈ s, sigma i ≤ multiplicity i + 1) :
    ∑ i ∈ s, (p : Real) ^ ((sigma i : Real) / 5 - 1) ≤ 1 := by
  calc
    ∑ i ∈ s, (p : Real) ^ ((sigma i : Real) / 5 - 1) ≤
        ∑ i ∈ s, (multiplicity i : Real) / 4 := by
      apply Finset.sum_le_sum
      intro i hi
      apply chen_four_stationaryWeight_le_quarter p (multiplicity i) (sigma i)
        hp (hmPos i hi) _ (hsigma i hi)
      exact (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (multiplicity j)) hi).trans
        hmSum
    _ = ((∑ i ∈ s, multiplicity i : Nat) : Real) / 4 := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ 1 := by
      have hmSumReal : (((∑ i ∈ s, multiplicity i : Nat) : Nat) : Real) ≤ 4 := by
        exact_mod_cast hmSum
      linarith

end Waring.Analytic
