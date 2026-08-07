import BoundedGaps.BombieriVinogradov.Analytic.ThreeFourOne
import BoundedGaps.BombieriVinogradov.Analytic.ImprimitiveLFunctionTransport
import BoundedGaps.BombieriVinogradov.Analytic.ZeroFreeRegionArithmetic

/-!
# Square-nonprincipal Dirichlet zero-free region

The phase-retaining `3-4-1` inequality rules out a zero close to one when the
square of the character is nonprincipal. The selected-zero estimate is used
once with the given zero and once with an empty selection for the squared
character.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 119--121,
Theorem 12.3 and equations (12.2)--(12.6), square-nonprincipal branch.
Independent comparison: `ElkiesM229NearlyZeroFree2018`, pp. 1--3.
Semantic review: `SEM-484`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private lemma re_inv_same_height (sigma : ℝ) (rho : ℂ) :
    (((((sigma : ℂ) + rho.im * I) - rho)⁻¹).re) =
      (sigma - rho.re)⁻¹ := by
  have heq :
      ((sigma : ℂ) + rho.im * I) - rho =
        ((sigma - rho.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  calc
    (((((sigma : ℂ) + rho.im * I) - rho)⁻¹).re) =
        (((sigma - rho.re : ℝ) : ℂ)⁻¹).re := by rw [heq]
    _ = ((((sigma - rho.re)⁻¹ : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_inv]
    _ = (sigma - rho.re)⁻¹ := Complex.ofReal_re _

/-- Nontrivial zeros of a character whose square is nonprincipal stay an
absolute logarithmic distance to the left of one. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_re_lt_of_sq_ne_one :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (rho : ℂ),
          chi ^ 2 ≠ 1 →
            IsNonprincipalNontrivialLFunctionZero chi rho →
              rho.re <
                1 - 1 / ((M : ℝ) ^ 2 *
                  Real.log ((q : ℝ) * (|rho.im| + 2))) := by
  obtain ⟨A, hA, hselected⟩ :=
    exists_nat_selectedNonprincipalNontrivialZeros_sum_sub_le_re_logDeriv_LFunction
  obtain ⟨C, hC, hzeta⟩ :=
    exists_pos_neg_logDeriv_riemannZeta_re_lt_inv_sub_one_add
  let K : ℝ := (16 * (A : ℝ) + 3) / 3
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  let B : ℝ := max 2
    (max (1 / Real.log 2) (4 + 6 * K + 3 * C / Real.log 2))
  obtain ⟨M, hM⟩ := exists_nat_gt B
  let m : ℝ := M
  have hMtwoReal : (2 : ℝ) < m := by
    dsimp [m]
    exact (le_max_left 2
      (max (1 / Real.log 2)
        (4 + 6 * K + 3 * C / Real.log 2))).trans_lt (by simpa [B] using hM)
  have hMtwo : 2 ≤ M := by
    have hcast : (2 : ℝ) ≤ (M : ℝ) := by
      simpa [m] using hMtwoReal.le
    exact_mod_cast hcast
  have hMinvLog : 1 / Real.log 2 < m := by
    dsimp [m]
    have hle :
        1 / Real.log 2 ≤ B :=
      (le_max_left (1 / Real.log 2)
        (4 + 6 * K + 3 * C / Real.log 2)).trans
          (le_max_right 2 _)
    exact hle.trans_lt hM
  have hMthreshold :
      4 + 6 * K + 3 * C / Real.log 2 < m := by
    dsimp [m]
    have hle :
        4 + 6 * K + 3 * C / Real.log 2 ≤ B :=
      (le_max_right (1 / Real.log 2)
        (4 + 6 * K + 3 * C / Real.log 2)).trans
          (le_max_right 2 _)
    exact hle.trans_lt hM
  have hmLogTwo : 1 < m * Real.log 2 := by
    calc
      1 = (1 / Real.log 2) * Real.log 2 := by
        field_simp
      _ < m * Real.log 2 :=
        mul_lt_mul_of_pos_right hMinvLog hlogTwo
  have hcoefficient :
      3 * C / Real.log 2 < m - 4 - 6 * K := by
    linarith
  refine ⟨M, hMtwo, ?_⟩
  intro q _ chi rho hsquare hrho
  let Q : ℝ := (q : ℝ) * (|rho.im| + 2)
  let L : ℝ := Real.log Q
  let sigma : ℝ := 1 + 1 / (m * L)
  have hQtwo : (2 : ℝ) ≤ Q := by
    simpa [Q] using two_le_level_height (q := q) rho.im
  have hlogLower : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log zero_lt_two hQtwo
  have hLpos : 0 < L := hlogTwo.trans_le hlogLower
  have hmpos : 0 < m := by linarith
  have hmLpos : 0 < m * L := mul_pos hmpos hLpos
  have hmLone : 1 < m * L :=
    hmLogTwo.trans_le (mul_le_mul_of_nonneg_left hlogLower hmpos.le)
  have hsigma_one : 1 < sigma := by
    dsimp [sigma]
    have : 0 < 1 / (m * L) := one_div_pos.mpr hmLpos
    linarith
  have hsigma_two : sigma < 2 := by
    dsimp [sigma]
    have hinv : (m * L)⁻¹ < 1 := (inv_lt_one₀ hmLpos).2 hmLone
    rw [one_div]
    linarith
  obtain ⟨hchi, hzero, hrho_pos, hrho_one⟩ :=
    (isNonprincipalNontrivialLFunctionZero_iff chi rho).1 hrho
  by_contra hcontra
  have hbeta : 1 - 1 / (m ^ 2 * L) ≤ rho.re := by
    simpa [m, L, Q] using le_of_not_gt hcontra
  have hreciprocal :
      (m - 1) * L ≤ (sigma - rho.re)⁻¹ := by
    simpa [sigma] using mul_sub_one_le_inv_one_add_inv_sub
      (m := m) (L := L) (beta := rho.re) hMtwoReal.le hLpos hbeta hrho_one
  let Z : ℂ →₀ ℕ := Finsupp.single rho 1
  have hZsupport :
      ∀ z ∈ Z.support,
        IsNonprincipalNontrivialLFunctionZero chi z ∧
          |z.im - rho.im| ≤ 1 := by
    intro z hz
    rw [Finsupp.support_single rho one_ne_zero] at hz
    simp only [Finset.mem_singleton] at hz
    subst z
    exact ⟨hrho, by simp⟩
  have horder :
      1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction chi) rho := by
    have hdiv := one_le_divisor_LFunction_of_zero
      (U := Set.univ) (s := rho) hchi (Set.mem_univ rho) hzero
    rw [divisor_LFunction_apply_eq_analyticOrderNatAt
      hchi (Set.mem_univ rho)] at hdiv
    exact_mod_cast hdiv
  have hZmult :
      ∀ z : ℂ,
        Z z ≤ analyticOrderNatAt (DirichletCharacter.LFunction chi) z := by
    intro z
    by_cases hz : z = rho
    · subst z
      simpa [Z] using horder
    · simp [Z, hz]
  have hchiRaw := hselected q chi hchi rho.im sigma Z
    hsigma_one.le hsigma_two.le hZsupport hZmult
  have hZsum :
      Z.sum (fun z n =>
          (n : ℝ) *
            (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) =
        (sigma - rho.re)⁻¹ := by
    calc
      Z.sum (fun z n =>
          (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) =
          ((1 : ℕ) : ℝ) *
            (((((sigma : ℂ) + rho.im * I) - rho)⁻¹).re) := by
        dsimp [Z]
        exact Finsupp.sum_single_index (a := rho) (b := 1)
          (h := fun (z : ℂ) (n : ℕ) =>
            (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re))
          (by norm_num)
      _ = (sigma - rho.re)⁻¹ := by
        rw [Nat.cast_one, one_mul, re_inv_same_height]
  change Z.sum (fun z n =>
      (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) -
      (16 * (A : ℝ) + 3) * L / 3 ≤
    (logDeriv (DirichletCharacter.LFunction chi)
      ((sigma : ℂ) + rho.im * I)).re at hchiRaw
  have hresidual : (16 * (A : ℝ) + 3) * L / 3 = K * L := by
    dsimp [K]
    ring
  rw [hZsum, hresidual] at hchiRaw
  have hchiLower :
      (m - 1) * L - K * L ≤
        (logDeriv (DirichletCharacter.LFunction chi)
          ((sigma : ℂ) + rho.im * I)).re := by
    linarith
  have hsquareRaw := hselected q (chi ^ 2) hsquare (2 * rho.im) sigma 0
    hsigma_one.le hsigma_two.le (by simp) (by simp)
  rw [Finsupp.sum_zero_index] at hsquareRaw
  change 0 - (16 * (A : ℝ) + 3) *
      Real.log ((q : ℝ) * (|2 * rho.im| + 2)) / 3 ≤
    (logDeriv (DirichletCharacter.LFunction (chi ^ 2))
      ((sigma : ℂ) + ((2 * rho.im : ℝ) : ℂ) * I)).re at hsquareRaw
  have hsquareResidual :
      (16 * (A : ℝ) + 3) *
          Real.log ((q : ℝ) * (|2 * rho.im| + 2)) / 3 =
        K * Real.log ((q : ℝ) * (|2 * rho.im| + 2)) := by
    dsimp [K]
    ring
  rw [hsquareResidual, zero_sub] at hsquareRaw
  have hdoubleLog :
      Real.log ((q : ℝ) * (|2 * rho.im| + 2)) ≤ 2 * L := by
    simpa [L, Q] using log_doubled_height_le_two_mul_log (q := q) rho.im
  have hsquareLower :
      -2 * K * L ≤
        (logDeriv (DirichletCharacter.LFunction (chi ^ 2))
          ((sigma : ℂ) + ((2 * rho.im : ℝ) : ℂ) * I)).re := by
    have hmul := mul_le_mul_of_nonneg_left hdoubleLog hKpos.le
    nlinarith
  have hphase :=
    three_four_one_zeta_neg_logDeriv_LFunction_nonneg
      chi hsigma_one rho.im
  have hevalOne :
      (sigma : ℂ) + I * rho.im = (sigma : ℂ) + rho.im * I := by ring
  have hevalTwo :
      (sigma : ℂ) + I * (2 * rho.im : ℝ) =
        (sigma : ℂ) + ((2 * rho.im : ℝ) : ℂ) * I := by ring
  rw [hevalOne, hevalTwo] at hphase
  simp only [Complex.neg_re] at hphase
  have hpole : (sigma - 1)⁻¹ = m * L := by
    have heq : sigma - 1 = (m * L)⁻¹ := by
      dsimp [sigma]
      rw [one_div]
      ring
    rw [heq, inv_inv]
  have hzetaBound := hzeta sigma hsigma_one hsigma_two
  rw [hpole] at hzetaBound
  have hzetaBound' :
      -(logDeriv riemannZeta (sigma : ℂ)).re < m * L + C := by
    simpa only [Complex.neg_re] using hzetaBound
  have hphaseUpper :
      4 * (logDeriv (DirichletCharacter.LFunction chi)
          ((sigma : ℂ) + rho.im * I)).re +
        (logDeriv (DirichletCharacter.LFunction (chi ^ 2))
          ((sigma : ℂ) + ((2 * rho.im : ℝ) : ℂ) * I)).re ≤
        3 * (-(logDeriv riemannZeta (sigma : ℂ)).re) := by
    linarith only [hphase]
  have hupper :
      4 * (logDeriv (DirichletCharacter.LFunction chi)
          ((sigma : ℂ) + rho.im * I)).re +
        (logDeriv (DirichletCharacter.LFunction (chi ^ 2))
          ((sigma : ℂ) + ((2 * rho.im : ℝ) : ℂ) * I)).re <
        3 * m * L + 3 * C := by
    calc
      _ ≤ 3 * (-(logDeriv riemannZeta (sigma : ℂ)).re) := hphaseUpper
      _ < 3 * (m * L + C) :=
        mul_lt_mul_of_pos_left hzetaBound' (by norm_num)
      _ = 3 * m * L + 3 * C := by ring
  have hlower :
      (4 * m - 4 - 6 * K) * L ≤
        4 * (logDeriv (DirichletCharacter.LFunction chi)
            ((sigma : ℂ) + rho.im * I)).re +
          (logDeriv (DirichletCharacter.LFunction (chi ^ 2))
            ((sigma : ℂ) + ((2 * rho.im : ℝ) : ℂ) * I)).re := by
    nlinarith
  have hcoefficient_pos : 0 < m - 4 - 6 * K :=
    (div_pos (mul_pos (by norm_num) hC) hlogTwo).trans hcoefficient
  have hcoefficientLog :
      3 * C < (m - 4 - 6 * K) * Real.log 2 := by
    calc
      3 * C = (3 * C / Real.log 2) * Real.log 2 := by
        field_simp
      _ < (m - 4 - 6 * K) * Real.log 2 :=
        mul_lt_mul_of_pos_right hcoefficient hlogTwo
  have hscaleCoefficient :
      (m - 4 - 6 * K) * Real.log 2 ≤
        (m - 4 - 6 * K) * L :=
    mul_le_mul_of_nonneg_left hlogLower hcoefficient_pos.le
  have hcontradiction :
      3 * m * L + 3 * C < (4 * m - 4 - 6 * K) * L := by
    nlinarith
  linarith

end BoundedGaps.Maynard
