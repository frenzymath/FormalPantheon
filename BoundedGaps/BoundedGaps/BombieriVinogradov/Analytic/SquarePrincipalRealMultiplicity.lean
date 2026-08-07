import BoundedGaps.BombieriVinogradov.Analytic.ThreeFourOne
import BoundedGaps.BombieriVinogradov.Analytic.ImprimitiveLFunctionTransport
import BoundedGaps.BombieriVinogradov.Analytic.PrincipalLFunctionHeightPole
import BoundedGaps.BombieriVinogradov.Analytic.ZeroFreeRegionArithmetic

/-!
# Simplicity of real near-one zeros of square-principal characters

If a real nonprincipal zero had analytic order at least two, selecting two
copies of it in the local logarithmic-derivative estimate would contradict
the `3-4-1` upper bound. The principal doubled-height pole is exactly the
same-height pole because the zero has imaginary part zero.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 119--121,
especially equations (12.2)--(12.6). Independent comparison:
`ElkiesM229NearlyZeroFree2018`, pp. 2--3. Semantic review: `SEM-486`.
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

private lemma re_inv_add_two_mul_I (x t : ℝ) :
    ((((x : ℂ) + (2 * t : ℝ) * I)⁻¹).re) =
      x / (x ^ 2 + 4 * t ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, zero_mul,
    I_im, mul_one, sub_zero, add_im, mul_im, add_zero]
  ring

private lemma one_le_LFunction_order_of_nonprincipal_zero
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsNonprincipalNontrivialLFunctionZero chi rho) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction chi) rho := by
  obtain ⟨hchi, hzero, _, _⟩ :=
    (isNonprincipalNontrivialLFunctionZero_iff chi rho).1 hrho
  have hdiv := one_le_divisor_LFunction_of_zero
    (U := Set.univ) (s := rho) hchi (Set.mem_univ rho) hzero
  rw [divisor_LFunction_apply_eq_analyticOrderNatAt
    hchi (Set.mem_univ rho)] at hdiv
  exact_mod_cast hdiv

/-- A real near-one nontrivial zero of a square-principal character has
ordinary analytic order one. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_order_eq_one_of_sq_eq_one_of_im_eq_zero :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (rho : ℂ),
          chi ^ 2 = 1 →
            IsNonprincipalNontrivialLFunctionZero chi rho →
              rho.im = 0 →
                1 - 1 / ((M : ℝ) ^ 2 *
                  Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re →
                  analyticOrderNatAt
                    (DirichletCharacter.LFunction chi) rho = 1 := by
  obtain ⟨A, hA, hselected⟩ :=
    exists_nat_selectedNonprincipalNontrivialZeros_sum_sub_le_re_logDeriv_LFunction
  obtain ⟨B, hB, hprincipal⟩ :=
    exists_nat_neg_logDeriv_principal_LFunction_re_le_pole_add_log
  obtain ⟨C, hC, hzeta⟩ :=
    exists_pos_neg_logDeriv_riemannZeta_re_lt_inv_sub_one_add
  let K : ℝ := (16 * (A : ℝ) + 3) / 3
  let J : ℝ := 16 * (B : ℝ) + 1
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hJpos : 0 < J := by dsimp [J]; positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  let R : ℝ := 2 * (4 + 4 * K + 2 * J + 3 * C / Real.log 2)
  let D : ℝ := max 2 (max (1 / Real.log 2) R)
  obtain ⟨M, hM⟩ := exists_nat_gt D
  let m : ℝ := M
  have hmTwo : (2 : ℝ) < m := by
    dsimp [m]
    exact (le_max_left 2 (max (1 / Real.log 2) R)).trans_lt
      (by simpa [D] using hM)
  have hMtwo : 2 ≤ M := by
    have hcast : (2 : ℝ) ≤ (M : ℝ) := by simpa [m] using hmTwo.le
    exact_mod_cast hcast
  have hmInvLog : 1 / Real.log 2 < m := by
    dsimp [m]
    exact ((le_max_left (1 / Real.log 2) R).trans
      (le_max_right 2 _)).trans_lt (by simpa [D] using hM)
  have hmThreshold : R < m := by
    dsimp [m]
    exact ((le_max_right (1 / Real.log 2) R).trans
      (le_max_right 2 _)).trans_lt (by simpa [D] using hM)
  have hmLogTwo : 1 < m * Real.log 2 := by
    calc
      1 = (1 / Real.log 2) * Real.log 2 := by field_simp
      _ < m * Real.log 2 := mul_lt_mul_of_pos_right hmInvLog hlogTwo
  have hmargin :
      3 * C / Real.log 2 < m / 2 - 4 - 4 * K - 2 * J := by
    dsimp [R] at hmThreshold
    linarith
  refine ⟨M, hMtwo, ?_⟩
  intro q _ chi rho hsquare hrho hgamma hbeta
  by_contra horderNe
  let Q : ℝ := (q : ℝ) * (|rho.im| + 2)
  let L : ℝ := Real.log Q
  let a : ℝ := 1 / (m * L)
  let sigma : ℝ := 1 + a
  let x : ℝ := sigma - rho.re
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
  have haPos : 0 < a := by dsimp [a]; positivity
  have haLtOne : a < 1 := by
    dsimp [a]
    rw [one_div]
    exact (inv_lt_one₀ hmLpos).2 hmLone
  have hsigmaOne : 1 < sigma := by dsimp [sigma]; linarith
  have hsigmaTwo : sigma < 2 := by dsimp [sigma]; linarith
  obtain ⟨hchi, hzero, hrhoPos, hrhoOne⟩ :=
    (isNonprincipalNontrivialLFunctionZero_iff chi rho).1 hrho
  have hbeta' : 1 - 1 / (m ^ 2 * L) ≤ rho.re := by
    simpa only [m, L, Q] using hbeta
  have hreciprocal : (m - 1) * L ≤ x⁻¹ := by
    simpa [x, sigma, a] using mul_sub_one_le_inv_one_add_inv_sub
      (m := m) (L := L) (beta := rho.re) hmTwo.le hLpos
        hbeta' hrhoOne
  have horderOne := one_le_LFunction_order_of_nonprincipal_zero hrho
  have horderTwo :
      2 ≤ analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho := by
    exact (Nat.two_le_iff _).2
      ⟨Nat.one_le_iff_ne_zero.mp horderOne, horderNe⟩
  let Ztwo : ℂ →₀ ℕ := Finsupp.single rho 2
  have hZtwoSupport :
      ∀ z ∈ Ztwo.support,
        IsNonprincipalNontrivialLFunctionZero chi z ∧
          |z.im - rho.im| ≤ 1 := by
    intro z hz
    rw [Finsupp.support_single rho (by norm_num : (2 : ℕ) ≠ 0)] at hz
    simp only [Finset.mem_singleton] at hz
    subst z
    exact ⟨hrho, by simp⟩
  have hZtwoMult :
      ∀ z : ℂ,
        Ztwo z ≤ analyticOrderNatAt
          (DirichletCharacter.LFunction chi) z := by
    intro z
    by_cases hz : z = rho
    · subst z
      simpa [Ztwo] using horderTwo
    · simp [Ztwo, hz]
  have htwoRaw := hselected q chi hchi rho.im sigma Ztwo
    hsigmaOne.le hsigmaTwo.le hZtwoSupport hZtwoMult
  have hZtwoSum :
      Ztwo.sum (fun z n =>
        (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) =
          2 * x⁻¹ := by
    calc
      _ = ((2 : ℕ) : ℝ) *
          (((((sigma : ℂ) + rho.im * I) - rho)⁻¹).re) := by
        dsimp [Ztwo]
        exact Finsupp.sum_single_index (a := rho) (b := 2)
          (h := fun (z : ℂ) (n : ℕ) =>
            (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re))
          (by norm_num)
      _ = 2 * x⁻¹ := by rw [Nat.cast_ofNat, re_inv_same_height]
  change Ztwo.sum (fun z n =>
      (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) -
      (16 * (A : ℝ) + 3) * L / 3 ≤
    (logDeriv (DirichletCharacter.LFunction chi)
      ((sigma : ℂ) + rho.im * I)).re at htwoRaw
  have hresidual : (16 * (A : ℝ) + 3) * L / 3 = K * L := by
    dsimp [K]
    ring
  rw [hZtwoSum, hresidual] at htwoRaw
  have hchiLower :
      2 * (m - 1) * L - K * L ≤
        (logDeriv (DirichletCharacter.LFunction chi)
          ((sigma : ℂ) + rho.im * I)).re := by
    linarith
  let sTwo : ℂ := (sigma : ℂ) + (2 * rho.im : ℝ) * I
  have hsTwoNe : sTwo ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp [sTwo] at hre
    linarith
  have hprincipalRaw := hprincipal q sTwo
    (by simpa [sTwo] using hsigmaOne.le)
    (by simpa [sTwo] using hsigmaTwo.le) hsTwoNe
  have hsTwoSub : sTwo - 1 =
      (a : ℂ) + (2 * rho.im : ℝ) * I := by
    apply Complex.ext <;> simp [sTwo, sigma]
  have hpoleRe : ((sTwo - 1)⁻¹).re = m * L := by
    rw [hsTwoSub, re_inv_add_two_mul_I, hgamma]
    norm_num
    dsimp [a]
    field_simp [hmpos.ne', hLpos.ne']
  have hdoubleLog :
      Real.log ((q : ℝ) * (|2 * rho.im| + 2)) ≤ 2 * L := by
    simpa [L, Q] using log_doubled_height_le_two_mul_log (q := q) rho.im
  have hsTwoIm : sTwo.im = 2 * rho.im := by simp [sTwo]
  have hprincipalLower :
      -m * L - 2 * J * L ≤
        (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := by
    have hraw :
        (-logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re ≤
          ((sTwo - 1)⁻¹).re +
            J * Real.log ((q : ℝ) * (|2 * rho.im| + 2)) := by
      simpa [hsquare, J, hsTwoIm] using hprincipalRaw
    rw [hpoleRe] at hraw
    simp only [Complex.neg_re] at hraw
    have hJlog := mul_le_mul_of_nonneg_left hdoubleLog hJpos.le
    calc
      -m * L - 2 * J * L ≤
          -m * L -
            J * Real.log ((q : ℝ) * (|2 * rho.im| + 2)) := by
        nlinarith only [hJlog]
      _ ≤ (logDeriv
          (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := by
        linarith only [hraw]
  have hphase := three_four_one_zeta_neg_logDeriv_LFunction_nonneg
    chi hsigmaOne rho.im
  have hevalOne :
      (sigma : ℂ) + I * rho.im = (sigma : ℂ) + rho.im * I := by ring
  have hevalTwo :
      (sigma : ℂ) + I * (2 * rho.im : ℝ) = sTwo := by
    dsimp [sTwo]
    ring
  rw [hevalOne, hevalTwo] at hphase
  simp only [Complex.neg_re] at hphase
  have hpoleSigma : (sigma - 1)⁻¹ = m * L := by
    have heq : sigma - 1 = (m * L)⁻¹ := by
      dsimp [sigma, a]
      rw [one_div]
      ring
    rw [heq, inv_inv]
  have hzetaBound := hzeta sigma hsigmaOne hsigmaTwo
  rw [hpoleSigma] at hzetaBound
  have hzetaBound' :
      -(logDeriv riemannZeta (sigma : ℂ)).re < m * L + C := by
    simpa only [Complex.neg_re] using hzetaBound
  have hupper :
      4 * (logDeriv (DirichletCharacter.LFunction chi)
          ((sigma : ℂ) + rho.im * I)).re +
        (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re <
          3 * m * L + 3 * C := by
    have hphaseUpper :
        4 * (logDeriv (DirichletCharacter.LFunction chi)
            ((sigma : ℂ) + rho.im * I)).re +
          (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re ≤
            3 * (-(logDeriv riemannZeta (sigma : ℂ)).re) := by
      linarith only [hphase]
    calc
      _ ≤ 3 * (-(logDeriv riemannZeta (sigma : ℂ)).re) := hphaseUpper
      _ < 3 * (m * L + C) :=
        mul_lt_mul_of_pos_left hzetaBound' (by norm_num)
      _ = 3 * m * L + 3 * C := by ring
  have hmarginPos : 0 < m / 2 - 4 - 4 * K - 2 * J :=
    (div_pos (mul_pos (by norm_num) hC) hlogTwo).trans hmargin
  have hmarginLog :
      3 * C < (m / 2 - 4 - 4 * K - 2 * J) * L := by
    calc
      3 * C = (3 * C / Real.log 2) * Real.log 2 := by field_simp
      _ < (m / 2 - 4 - 4 * K - 2 * J) * Real.log 2 :=
        mul_lt_mul_of_pos_right hmargin hlogTwo
      _ ≤ (m / 2 - 4 - 4 * K - 2 * J) * L :=
        mul_le_mul_of_nonneg_left hlogLower hmarginPos.le
  have hlower :
      (7 * m - 8 - 4 * K - 2 * J) * L ≤
        4 * (logDeriv (DirichletCharacter.LFunction chi)
            ((sigma : ℂ) + rho.im * I)).re +
          (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := by
    nlinarith only [hchiLower, hprincipalLower]
  have hstrict :
      3 * m * L + 3 * C <
        (7 * m - 8 - 4 * K - 2 * J) * L := by
    nlinarith only [hmarginLog, hmTwo, hLpos]
  exact (not_lt_of_ge hlower) (hupper.trans hstrict)

end BoundedGaps.Maynard
