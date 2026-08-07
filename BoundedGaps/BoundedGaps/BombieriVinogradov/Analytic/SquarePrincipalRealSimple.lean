import BoundedGaps.BombieriVinogradov.Analytic.SquarePrincipalNonreal
import BoundedGaps.BombieriVinogradov.Analytic.SquarePrincipalRealMultiplicity

/-!
# Real and simple near-one zeros of square-principal characters

This module combines the absolute witnesses for nonreal-zero exclusion and
real-zero simplicity. Enlarging the natural witness only narrows the near-one
region, so their maximum satisfies both conclusions.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 119--121,
Theorem 12.3 and equations (12.2)--(12.6). Independent comparison:
`ElkiesM229NearlyZeroFree2018`, pp. 2--3. Semantic review: `SEM-486`.
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

/-- A near-one nontrivial zero of a square-principal character is real and
simple. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_real_simple_of_sq_eq_one :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (rho : ℂ),
          chi ^ 2 = 1 →
            IsNonprincipalNontrivialLFunctionZero chi rho →
              1 - 1 / ((M : ℝ) ^ 2 *
                Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re →
                rho.im = 0 ∧
                  analyticOrderNatAt
                    (DirichletCharacter.LFunction chi) rho = 1 := by
  obtain ⟨Mnonreal, hMnonreal, hnonreal⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_im_eq_zero_of_sq_eq_one
  obtain ⟨Msimple, hMsimple, hsimple⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_order_eq_one_of_sq_eq_one_of_im_eq_zero
  let M := max Mnonreal Msimple
  have hMtwo : 2 ≤ M := hMnonreal.trans (le_max_left _ _)
  refine ⟨M, hMtwo, ?_⟩
  intro q _ chi rho hsquare hrho hnear
  let L : ℝ := Real.log ((q : ℝ) * (|rho.im| + 2))
  have hscale : (2 : ℝ) ≤ (q : ℝ) * (|rho.im| + 2) :=
    two_le_level_height (q := q) rho.im
  have hLpos : 0 < L := by
    dsimp [L]
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two hscale)
  have hnearNonreal :
      1 - 1 / ((Mnonreal : ℝ) ^ 2 * L) ≤ rho.re := by
    apply near_one_of_le (one_le_two.trans hMnonreal) (le_max_left _ _) hLpos
    simpa only [M, L] using hnear
  have him := hnonreal q chi rho hsquare hrho
    (by simpa only [L] using hnearNonreal)
  have hnearSimple :
      1 - 1 / ((Msimple : ℝ) ^ 2 * L) ≤ rho.re := by
    apply near_one_of_le (one_le_two.trans hMsimple) (le_max_right _ _) hLpos
    simpa only [M, L] using hnear
  exact ⟨him, hsimple q chi rho hsquare hrho him
    (by simpa only [L] using hnearSimple)⟩

end BoundedGaps.Maynard
