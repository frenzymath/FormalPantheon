import BoundedGaps.BombieriVinogradov.Analytic.SquareNonprincipalZeroFreeRegion
import BoundedGaps.BombieriVinogradov.Analytic.SquarePrincipalFixedCharacter
import BoundedGaps.BombieriVinogradov.Analytic.SquarePrincipalCharacterUniqueness

/-!
# Structure and uniqueness of nonprincipal exceptional zeros

This module composes the square-nonprincipal exclusion with the separately
audited square-principal reality, simplicity, fixed-character uniqueness, and
cross-character uniqueness theorems. It states only the nonprincipal
constituent-zero conclusion, not uniqueness of an analytic zero of the full
product over characters.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 119--121,
Theorem 12.3. Independent comparison: `ElkiesM229NearlyZeroFree2018`, printed
pp. 3--4. Semantic review: `SEM-489`.
-/

noncomputable section

namespace BoundedGaps.Maynard

private lemma near_one_of_le
    {m M : ℕ} {L beta : ℝ} (hm : 1 ≤ m) (hmM : m ≤ M)
    (hL : 0 < L)
    (hnear : 1 - 1 / ((M : ℝ) ^ 2 * L) ≤ beta) :
    1 - 1 / ((m : ℝ) ^ 2 * L) ≤ beta := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hcast : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hsquare : (m : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (M : ℝ), sq_nonneg (m : ℝ)]
  have hden : (m : ℝ) ^ 2 * L ≤ (M : ℝ) ^ 2 * L :=
    mul_le_mul_of_nonneg_right hsquare hL.le
  have hinv : 1 / ((M : ℝ) ^ 2 * L) ≤
      1 / ((m : ℝ) ^ 2 * L) :=
    one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hmpos) hL) hden
  linarith

/-- A nonprincipal near-one zero belongs to a square-principal character and
is real and simple. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_sq_eq_one_real_simple :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (rho : ℂ),
          IsNonprincipalNontrivialLFunctionZero chi rho →
            1 - 1 / ((M : ℝ) ^ 2 *
              Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re →
              chi ^ 2 = 1 ∧
                rho.im = 0 ∧
                  analyticOrderNatAt
                    (DirichletCharacter.LFunction chi) rho = 1 := by
  obtain ⟨Mnonquad, hMnonquad, hnonquad⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_re_lt_of_sq_ne_one
  obtain ⟨Mreal, hMreal, hreal⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_real_simple_of_sq_eq_one
  let M := max Mnonquad Mreal
  have hMtwo : 2 ≤ M := hMnonquad.trans (le_max_left _ _)
  refine ⟨M, hMtwo, ?_⟩
  intro q _ chi rho hrho hnear
  let L : ℝ := Real.log ((q : ℝ) * (|rho.im| + 2))
  have hLpos : 0 < L := by
    dsimp [L]
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two (two_le_level_height (q := q) rho.im))
  have hnearNonquad :
      1 - 1 / ((Mnonquad : ℝ) ^ 2 * L) ≤ rho.re := by
    apply near_one_of_le (one_le_two.trans hMnonquad)
      (le_max_left _ _) hLpos
    simpa only [M, L] using hnear
  have hsquare : chi ^ 2 = 1 := by
    by_contra hsquare
    have hleft := hnonquad q chi rho hsquare hrho
    exact (not_lt_of_ge (by simpa only [L] using hnearNonquad)) hleft
  have hnearReal :
      1 - 1 / ((Mreal : ℝ) ^ 2 * L) ≤ rho.re := by
    apply near_one_of_le (one_le_two.trans hMreal)
      (le_max_right _ _) hLpos
    simpa only [M, L] using hnear
  have hrealSimple := hreal q chi rho hsquare hrho
    (by simpa only [L] using hnearReal)
  exact ⟨hsquare, hrealSimple.1, hrealSimple.2⟩

/-- Any two nonprincipal constituent zero pairs in one near-one region are
equal componentwise. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_and_zero_eq :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi1 chi2 : DirichletCharacter ℂ q) (rho1 rho2 : ℂ),
          IsNonprincipalNontrivialLFunctionZero chi1 rho1 →
            IsNonprincipalNontrivialLFunctionZero chi2 rho2 →
              1 - 1 / ((M : ℝ) ^ 2 *
                Real.log ((q : ℝ) * (|rho1.im| + 2))) ≤ rho1.re →
                1 - 1 / ((M : ℝ) ^ 2 *
                  Real.log ((q : ℝ) * (|rho2.im| + 2))) ≤ rho2.re →
                  chi1 = chi2 ∧ rho1 = rho2 := by
  obtain ⟨Mshape, hMshape, hshape⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_sq_eq_one_real_simple
  obtain ⟨Mchar, hMchar, hchar⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_of_sq_eq_one
  obtain ⟨Mzero, hMzero, hzero⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_eq_of_sq_eq_one
  let M := max Mshape (max Mchar Mzero)
  have hMtwo : 2 ≤ M := hMshape.trans (le_max_left _ _)
  refine ⟨M, hMtwo, ?_⟩
  intro q _ chi1 chi2 rho1 rho2 hrho1 hrho2 hnear1 hnear2
  let L1 : ℝ := Real.log ((q : ℝ) * (|rho1.im| + 2))
  let L2 : ℝ := Real.log ((q : ℝ) * (|rho2.im| + 2))
  have hL1pos : 0 < L1 := by
    dsimp [L1]
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two (two_le_level_height (q := q) rho1.im))
  have hL2pos : 0 < L2 := by
    dsimp [L2]
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two (two_le_level_height (q := q) rho2.im))
  have hnearShape1 :
      1 - 1 / ((Mshape : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le (one_le_two.trans hMshape)
      (le_max_left _ _) hL1pos
    simpa only [M, L1] using hnear1
  have hnearShape2 :
      1 - 1 / ((Mshape : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le (one_le_two.trans hMshape)
      (le_max_left _ _) hL2pos
    simpa only [M, L2] using hnear2
  have hshape1 := hshape q chi1 rho1 hrho1
    (by simpa only [L1] using hnearShape1)
  have hshape2 := hshape q chi2 rho2 hrho2
    (by simpa only [L2] using hnearShape2)
  have hMcharM : Mchar ≤ M :=
    (le_max_left Mchar Mzero).trans (le_max_right Mshape _)
  have hMzeroM : Mzero ≤ M :=
    (le_max_right Mchar Mzero).trans (le_max_right Mshape _)
  have hnearChar1 :
      1 - 1 / ((Mchar : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le (one_le_two.trans hMchar) hMcharM hL1pos
    simpa only [M, L1] using hnear1
  have hnearChar2 :
      1 - 1 / ((Mchar : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le (one_le_two.trans hMchar) hMcharM hL2pos
    simpa only [M, L2] using hnear2
  have hcharEq := hchar q chi1 chi2 rho1 rho2 hshape1.1 hshape2.1
    hrho1 hrho2 (by simpa only [L1] using hnearChar1)
      (by simpa only [L2] using hnearChar2)
  have hnearZero1 :
      1 - 1 / ((Mzero : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le (one_le_two.trans hMzero) hMzeroM hL1pos
    simpa only [M, L1] using hnear1
  have hnearZero2 :
      1 - 1 / ((Mzero : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le (one_le_two.trans hMzero) hMzeroM hL2pos
    simpa only [M, L2] using hnear2
  refine ⟨hcharEq, ?_⟩
  subst chi2
  exact hzero q chi1 rho1 rho2 hshape1.1 hrho1 hrho2
    (by simpa only [L1] using hnearZero1)
    (by simpa only [L2] using hnearZero2)

end BoundedGaps.Maynard
