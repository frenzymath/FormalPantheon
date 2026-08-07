import BoundedGaps.BombieriVinogradov.Analytic.SquarePrincipalRealSimple
import BoundedGaps.BombieriVinogradov.Analytic.SquarePrincipalRealUniqueness

/-!
# Fixed-character uniqueness in the square-principal near-one region

This module combines the absolute reality and real-pair uniqueness witnesses.
It fills the same-character two-distinct-real-zero case omitted before the
different-character argument on printed p. 121 of
`KoukoulopoulosDistributionPrimesPrelim2022`. Semantic review: `SEM-487`.
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

/-- Two near-one nontrivial zeros of one square-principal character are
equal. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_eq_of_sq_eq_one :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (rho1 rho2 : ℂ),
          chi ^ 2 = 1 →
            IsNonprincipalNontrivialLFunctionZero chi rho1 →
              IsNonprincipalNontrivialLFunctionZero chi rho2 →
                1 - 1 / ((M : ℝ) ^ 2 *
                  Real.log ((q : ℝ) * (|rho1.im| + 2))) ≤ rho1.re →
                  1 - 1 / ((M : ℝ) ^ 2 *
                    Real.log ((q : ℝ) * (|rho2.im| + 2))) ≤ rho2.re →
                    rho1 = rho2 := by
  obtain ⟨Mreal, hMreal, hreal⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_real_simple_of_sq_eq_one
  obtain ⟨Mpair, hMpair, hpair⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_eq_of_sq_eq_one_of_im_eq_zero
  let M := max Mreal Mpair
  have hMtwo : 2 ≤ M := hMreal.trans (le_max_left _ _)
  refine ⟨M, hMtwo, ?_⟩
  intro q _ chi rho1 rho2 hsquare hrho1 hrho2 hnear1 hnear2
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
  have hnearReal1 : 1 - 1 / ((Mreal : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le (one_le_two.trans hMreal) (le_max_left _ _) hL1pos
    simpa only [M, L1] using hnear1
  have hnearReal2 : 1 - 1 / ((Mreal : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le (one_le_two.trans hMreal) (le_max_left _ _) hL2pos
    simpa only [M, L2] using hnear2
  have him1 := (hreal q chi rho1 hsquare hrho1
    (by simpa only [L1] using hnearReal1)).1
  have him2 := (hreal q chi rho2 hsquare hrho2
    (by simpa only [L2] using hnearReal2)).1
  have hnearPair1 : 1 - 1 / ((Mpair : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le (one_le_two.trans hMpair) (le_max_right _ _) hL1pos
    simpa only [M, L1] using hnear1
  have hnearPair2 : 1 - 1 / ((Mpair : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le (one_le_two.trans hMpair) (le_max_right _ _) hL2pos
    simpa only [M, L2] using hnear2
  exact hpair q chi rho1 rho2 hsquare hrho1 hrho2 him1 him2
    (by simpa only [L1] using hnearPair1)
    (by simpa only [L2] using hnearPair2)

end BoundedGaps.Maynard
