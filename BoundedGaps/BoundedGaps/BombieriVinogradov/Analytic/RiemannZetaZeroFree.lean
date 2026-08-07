import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaSelectedSubdivisor
import BoundedGaps.BombieriVinogradov.Analytic.ThreeFourOne
import BoundedGaps.BombieriVinogradov.Analytic.ZeroFreeRegionArithmetic

/-!
# Quantitative Riemann-zeta zero-free region

This module is the zeta-only predecessor of the principal-character and
product branches. It combines the same-height selected radius-two divisor,
the all-zeta `3-4-1` inequality, and a separate small-height neighborhood
argument.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84 and
86--88, Lemma 8.2(b), Theorem 8.3, and equation (8.6). Semantic review:
`SEM-491`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Metric Set

private lemma riemannZeta_zero_regularized
    {rho : ℂ} (hzero : riemannZeta rho = 0) :
    riemannZeta₁ rho = 0 := by
  have hrho1 : rho ≠ 1 := by
    intro h
    subst rho
    exact riemannZeta_one_ne_zero hzero
  have hfactor := riemannZeta_eq_inv_sub_mul hrho1
  rw [hzero] at hfactor
  exact (mul_eq_zero.mp hfactor.symm).resolve_left
    (inv_ne_zero (sub_ne_zero.mpr hrho1))

private lemma analyticOnNhd_riemannZeta₁_zeroFree :
    AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
  differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ

private lemma analyticOrderAt_riemannZeta₁_ne_top_zeroFree (rho : ℂ) :
    analyticOrderAt riemannZeta₁ rho ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho
    (fun z => analyticOnNhd_riemannZeta₁_zeroFree z (mem_univ z))]
  intro hzero
  have hone := congrFun hzero 1
  change riemannZeta₁ 1 = 0 at hone
  rw [riemannZeta₁_one] at hone
  exact one_ne_zero hone

private lemma one_le_analyticOrderNatAt_riemannZeta₁_of_zero
    {rho : ℂ} (hzero : riemannZeta₁ rho = 0) :
    1 ≤ analyticOrderNatAt riemannZeta₁ rho := by
  have horder : analyticOrderAt riemannZeta₁ rho ≠ 0 :=
    (differentiable_riemannZeta₁.analyticAt rho).analyticOrderAt_ne_zero.mpr hzero
  have hfinite := analyticOrderAt_riemannZeta₁_ne_top_zeroFree rho
  have hcast : (1 : ℕ∞) ≤ analyticOrderAt riemannZeta₁ rho :=
    Order.one_le_iff_ne_zero.mpr horder
  rw [← Nat.cast_analyticOrderNatAt hfinite] at hcast
  exact_mod_cast hcast

private lemma dist_sq_riemannZeta_zero_one
    {rho : ℂ} :
    dist rho 1 ^ 2 = (1 - rho.re) ^ 2 + rho.im ^ 2 := by
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, sub_zero]
  ring

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

private lemma pole_re_le_of_im_ge
    {a gamma delta : ℝ} (ha : 0 ≤ a) (ha_one : a ≤ 1) (hdelta : 0 < delta)
    (hgamma : delta / 2 ≤ |gamma|) :
    (((a : ℂ) + gamma * I)⁻¹).re ≤ 4 / delta ^ 2 := by
  rw [Complex.inv_re]
  have hsq : delta ^ 2 / 4 ≤ gamma ^ 2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ delta / 2)
      (abs_nonneg gamma)).2 hgamma
    have h' : (delta / 2) ^ 2 ≤ gamma ^ 2 := by simpa [sq_abs] using h
    nlinarith
  have hden : delta ^ 2 / 4 ≤ a ^ 2 + gamma ^ 2 := by
    nlinarith [sq_nonneg a]
  have hdenpos : 0 < a ^ 2 + gamma ^ 2 := by
    have : 0 < delta ^ 2 / 4 := by positivity
    linarith
  have hfrac : a / (a ^ 2 + gamma ^ 2) ≤ a / (delta ^ 2 / 4) :=
    div_le_div_of_nonneg_left ha (by positivity) hden
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
    Complex.normSq_apply]
  norm_num
  have hpow : a * a + gamma * gamma = a ^ 2 + gamma ^ 2 := by ring
  rw [hpow]
  calc
    a / (a ^ 2 + gamma ^ 2) ≤ a / (delta ^ 2 / 4) := hfrac
    _ ≤ 4 / delta ^ 2 := by
      have hbound : a / (delta ^ 2 / 4) ≤ 1 / (delta ^ 2 / 4) := by
        exact div_le_div_of_nonneg_right ha_one (by positivity)
      calc
        a / (delta ^ 2 / 4) ≤ 1 / (delta ^ 2 / 4) := hbound
        _ = 4 / delta ^ 2 := by field_simp [hdelta.ne']

/-! The quantitative theorem is below; its constants are chosen after the two
height branches and are deliberately not exposed. -/

theorem exists_nat_riemannZeta_zero_re_lt :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ rho : ℂ,
        riemannZeta rho = 0 →
          rho.re <
            1 - 1 / ((M : ℝ) ^ 2 *
              Real.log (|rho.im| + 2)) := by
  obtain ⟨Aselect, hAselect, hselected⟩ :=
    exists_nat_selected_radiusTwo_subdivisor_sum_sub_pole_le_re_logDeriv_riemannZeta
  obtain ⟨Azeta, hAzeta, hzetaBound⟩ :=
    exists_nat_neg_logDeriv_riemannZeta_re_le_pole_add_log
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnear : {s : ℂ | riemannZeta s ≠ 0} ∈ nhds (1 : ℂ) := by
    simpa only [Filter.eventually_iff] using
      riemannZeta_eventually_ne_zero_nhds_one
  obtain ⟨delta, hdelta, hdeltaBall⟩ := Metric.mem_nhds_iff.mp hnear
  let d : ℝ := min delta 1
  have hdpos : 0 < d := lt_min hdelta zero_lt_one
  have hdle_one : d ≤ 1 := min_le_right _ _
  have hdle_delta : d ≤ delta := min_le_left _ _
  let P : ℝ := 4 / d ^ 2
  let E : ℝ := 64 * (Aselect : ℝ) +
    80 * (Azeta : ℝ) + 5 * P / Real.log 2
  let B : ℝ := max 2 (max (2 / (d * Real.log 2)) (4 + E))
  obtain ⟨M, hM⟩ := exists_nat_gt B
  let m : ℝ := M
  have hMtwoReal : (2 : ℝ) < m := by
    dsimp [m]
    exact (show (2 : ℝ) ≤ B from le_max_left _ _).trans_lt hM
  have hMtwo : 2 ≤ M := by
    have hcast : (2 : ℝ) ≤ (M : ℝ) := by
      simpa [m] using hMtwoReal.le
    exact_mod_cast hcast
  have hMsmall : 2 / (d * Real.log 2) < m := by
    dsimp [m]
    have hle : 2 / (d * Real.log 2) ≤ B :=
      (le_max_left (2 / (d * Real.log 2)) (4 + E)).trans
        (le_max_right 2 _)
    exact hle.trans_lt hM
  have hMcoef : 4 + E < m := by
    dsimp [m]
    have hle : 4 + E ≤ B :=
      (le_max_right (2 / (d * Real.log 2)) (4 + E)).trans
        (le_max_right 2 _)
    exact hle.trans_lt hM
  refine ⟨M, hMtwo, ?_⟩
  intro rho hzero
  have hregularized : riemannZeta₁ rho = 0 :=
    riemannZeta_zero_regularized hzero
  have hbetaOne : rho.re < 1 :=
    riemannZeta₁_zero_re_lt_one hregularized
  let L : ℝ := Real.log (|rho.im| + 2)
  have hLlog : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg rho.im])
  have hLpos : 0 < L := hlogTwo.trans_le hLlog
  have hdmLogTwo : 2 < d * m * Real.log 2 := by
    have hprodpos : 0 < d * Real.log 2 := mul_pos hdpos hlogTwo
    have hmul := mul_lt_mul_of_pos_right hMsmall hprodpos
    have hcancel :
        (2 / (d * Real.log 2)) * (d * Real.log 2) = 2 := by
      field_simp [ne_of_gt hprodpos]
    rw [hcancel] at hmul
    nlinarith [hmul]
  have hmLogTwo : 1 < m * Real.log 2 := by
    have hnonneg : 0 ≤ m * Real.log 2 := by positivity
    have hle : d * (m * Real.log 2) ≤ 1 * (m * Real.log 2) :=
      mul_le_mul_of_nonneg_right hdle_one hnonneg
    rw [one_mul] at hle
    nlinarith [hdmLogTwo, hle]
  by_cases hsmall : |rho.im| < d / 2
  · have hdist : d ≤ dist rho (1 : ℂ) := by
      by_contra hnot
      have hltD : dist rho (1 : ℂ) < d := lt_of_not_ge hnot
      have hlt : dist rho (1 : ℂ) < delta :=
        hltD.trans_le hdle_delta
      exact (hdeltaBall (by simpa [Metric.mem_ball] using hlt)) hzero
    have hdistNonneg : 0 ≤ dist rho (1 : ℂ) := dist_nonneg
    have hdistSq : d ^ 2 ≤ dist rho (1 : ℂ) ^ 2 :=
      (sq_le_sq₀ (by positivity) hdistNonneg).2 hdist
    have hgap : d / 2 < 1 - rho.re := by
      have himsq : rho.im ^ 2 < (d / 2) ^ 2 := by
        simpa [sq_abs] using
          ((sq_lt_sq₀ (abs_nonneg rho.im) (by positivity)).2 hsmall)
      rw [dist_sq_riemannZeta_zero_one] at hdistSq
      nlinarith
    have hden : 0 < (m : ℝ) ^ 2 * Real.log (|rho.im| + 2) := by
      positivity
    have hrecip :
        1 / (m ^ 2 * Real.log (|rho.im| + 2)) < d / 2 := by
      have hlog : Real.log 2 ≤ Real.log (|rho.im| + 2) := hLlog
      have hmul : 2 < d * (m ^ 2 * Real.log (|rho.im| + 2)) := by
        have hmone : 1 ≤ m := by linarith
        have hmsq : m ≤ m ^ 2 := by nlinarith
        have hml : m * Real.log 2 ≤ m ^ 2 *
            Real.log (|rho.im| + 2) := by
          have hfirst : m * Real.log 2 ≤ m *
              Real.log (|rho.im| + 2) :=
            mul_le_mul_of_nonneg_left hlog (zero_le_one.trans hmone)
          have hsecond : m * Real.log (|rho.im| + 2) ≤
              m ^ 2 * Real.log (|rho.im| + 2) := by
            exact mul_le_mul_of_nonneg_right hmsq hLpos.le
          exact hfirst.trans hsecond
        have hprod : d * m * Real.log 2 ≤
            d * (m ^ 2 * Real.log (|rho.im| + 2)) := by
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left hml hdpos.le)
        exact hdmLogTwo.trans_le hprod
      have hpos : 0 < d * (m ^ 2 * Real.log (|rho.im| + 2)) := by positivity
      apply (div_lt_iff₀ hden).2
      nlinarith
    have hgap' :
        1 / (m ^ 2 * Real.log (|rho.im| + 2)) < 1 - rho.re :=
      hrecip.trans hgap
    dsimp [m] at hgap'
    linarith
  · have hlarge : d / 2 ≤ |rho.im| := le_of_not_gt hsmall
    let a : ℝ := 1 / (m * L)
    let sigma : ℝ := 1 + a
    have hmpos : 0 < m := by linarith
    have hmLpos : 0 < m * L := mul_pos hmpos hLpos
    have hmLone : 1 < m * L :=
      hmLogTwo.trans_le (mul_le_mul_of_nonneg_left hLlog hmpos.le)
    have haPos : 0 < a := by
      dsimp [a]
      exact one_div_pos.mpr hmLpos
    have haLtOne : a < 1 := by
      dsimp [a]
      rw [one_div]
      exact (inv_lt_one₀ hmLpos).2 hmLone
    have hsigmaOne : 1 < sigma := by
      dsimp [sigma]
      linarith
    have hsigmaTwo : sigma < 2 := by
      dsimp [sigma]
      linarith
    by_contra hcontra
    have hbeta : 1 - 1 / (m ^ 2 * L) ≤ rho.re := by
      simpa [m, L] using le_of_not_gt hcontra
    have hreciprocal :
        (m - 1) * L ≤ (sigma - rho.re)⁻¹ := by
      simpa [sigma, a] using mul_sub_one_le_inv_one_add_inv_sub
        (m := m) (L := L) (beta := rho.re) hMtwoReal.le hLpos
          hbeta hbetaOne
    have hmSqLone : 1 < m ^ 2 * L := by
      have hprod : 0 < (m - 1) * (m * L - 1) :=
        mul_pos (by linarith) (by linarith)
      nlinarith
    have hbetaPos : 0 < rho.re := by
      have hinv : 1 / (m ^ 2 * L) < 1 := by
        rw [one_div]
        exact (inv_lt_one₀ (by positivity)).2 hmSqLone
      linarith
    let Z : ℂ →₀ ℕ := Finsupp.single rho 1
    have horder : 1 ≤ analyticOrderNatAt riemannZeta₁ rho :=
      one_le_analyticOrderNatAt_riemannZeta₁_of_zero hregularized
    have hdistCenter :
        dist rho ((2 : ℂ) + rho.im * I) ≤ 2 := by
      have heq :
          dist rho ((2 : ℂ) + rho.im * I) = |rho.re - 2| := by
        rw [Complex.dist_eq]
        have hdiff : rho - ((2 : ℂ) + rho.im * I) =
            ((rho.re - 2 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [hdiff, norm_real, Real.norm_eq_abs]
      rw [heq, abs_of_nonpos (by linarith)]
      linarith
    have hZmult :
        ∀ z : ℂ,
          Z z ≤ if dist z ((2 : ℂ) + rho.im * I) ≤ 2 then
            analyticOrderNatAt riemannZeta₁ z else 0 := by
      intro z
      by_cases hz : z = rho
      · subst z
        rw [if_pos hdistCenter]
        simpa [Z] using horder
      · simp [Z, hz]
    have hselectedRaw := hselected rho.im sigma Z
      hsigmaOne hsigmaTwo.le hZmult
    have hZsum :
        Z.sum (fun z n =>
          (n : ℝ) *
            (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) =
          (sigma - rho.re)⁻¹ := by
      calc
        _ = ((1 : ℕ) : ℝ) *
            (((((sigma : ℂ) + rho.im * I) - rho)⁻¹).re) := by
          dsimp [Z]
          exact Finsupp.sum_single_index (a := rho) (b := 1)
            (h := fun (z : ℂ) (n : ℕ) =>
              (n : ℝ) *
                (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re))
            (by norm_num)
        _ = (sigma - rho.re)⁻¹ := by
          rw [Nat.cast_one, one_mul, re_inv_same_height]
    let sOne : ℂ := (sigma : ℂ) + rho.im * I
    have hsOneSub : sOne - 1 = (a : ℂ) + rho.im * I := by
      apply Complex.ext <;> simp [sOne, sigma]
    have hpoleOne : ((sOne - 1)⁻¹).re ≤ P := by
      rw [hsOneSub]
      dsimp [P]
      exact pole_re_le_of_im_ge haPos.le haLtOne.le hdpos hlarge
    change Z.sum (fun z n =>
        (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) -
        ((sOne - 1)⁻¹).re - 16 * (Aselect : ℝ) * L ≤
      (logDeriv riemannZeta sOne).re at hselectedRaw
    rw [hZsum] at hselectedRaw
    have hmiddle :
        (-logDeriv riemannZeta sOne).re ≤
          P - (sigma - rho.re)⁻¹ + 16 * (Aselect : ℝ) * L := by
      simp only [Complex.neg_re]
      linarith
    have hpoleSigma : (sigma - 1)⁻¹ = m * L := by
      have heq : sigma - 1 = (m * L)⁻¹ := by
        dsimp [sigma, a]
        rw [one_div]
        ring
      rw [heq, inv_inv]
    have hrealRaw := hzetaBound (sigma : ℂ)
      (by simpa using hsigmaOne.le) (by simpa using hsigmaTwo.le)
      (by exact_mod_cast ne_of_gt hsigmaOne)
    have hsubSigma : (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) := by
      norm_cast
    rw [hsubSigma, ← Complex.ofReal_inv, Complex.ofReal_re] at hrealRaw
    simp only [Complex.ofReal_im, abs_zero, zero_add] at hrealRaw
    rw [hpoleSigma] at hrealRaw
    have hreal :
        (-logDeriv riemannZeta (sigma : ℂ)).re ≤
          m * L + 16 * (Azeta : ℝ) * L := by
      have herror := mul_le_mul_of_nonneg_left hLlog
        (by positivity : 0 ≤ 16 * (Azeta : ℝ))
      linarith
    let sTwo : ℂ := (sigma : ℂ) + (2 * rho.im : ℝ) * I
    have hsTwoSub : sTwo - 1 = (a : ℂ) + (2 * rho.im : ℝ) * I := by
      apply Complex.ext <;> simp [sTwo, sigma]
    have hlargeTwo : d / 2 ≤ |2 * rho.im| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [abs_nonneg rho.im]
    have hpoleTwo : ((sTwo - 1)⁻¹).re ≤ P := by
      rw [hsTwoSub]
      dsimp [P]
      exact pole_re_le_of_im_ge haPos.le haLtOne.le hdpos hlargeTwo
    have hsTwoNe : sTwo ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp [sTwo] at hre
      linarith
    have hdoubleRaw := hzetaBound sTwo
      (by simpa [sTwo] using hsigmaOne.le)
      (by simpa [sTwo] using hsigmaTwo.le) hsTwoNe
    have hdoubleLog :
        Real.log (|2 * rho.im| + 2) ≤ 2 * L := by
      simpa [L] using
        log_doubled_height_le_two_mul_log (q := 1) rho.im
    have hdouble :
        (-logDeriv riemannZeta sTwo).re ≤
          P + 32 * (Azeta : ℝ) * L := by
      have hsTwoIm : sTwo.im = 2 * rho.im := by simp [sTwo]
      rw [hsTwoIm] at hdoubleRaw
      have herror := mul_le_mul_of_nonneg_left hdoubleLog
        (by positivity : 0 ≤ 16 * (Azeta : ℝ))
      nlinarith
    have hphase := three_four_one_zeta_neg_logDeriv_LFunction_nonneg
      (1 : DirichletCharacter ℂ 1) hsigmaOne rho.im
    simp only [DirichletCharacter.LFunction_modOne_eq] at hphase
    have hevalOne :
        (sigma : ℂ) + I * rho.im = sOne := by
      dsimp [sOne]
      ring
    have hevalTwo :
        (sigma : ℂ) + I * (2 * rho.im : ℝ) = sTwo := by
      dsimp [sTwo]
      ring
    rw [hevalOne, hevalTwo] at hphase
    have hupper :
        4 * (sigma - rho.re)⁻¹ ≤
          3 * m * L +
            (64 * (Aselect : ℝ) + 80 * (Azeta : ℝ)) * L + 5 * P := by
      nlinarith only [hphase, hreal, hmiddle, hdouble]
    have hPnonneg : 0 ≤ P := by
      dsimp [P]
      positivity
    have hPabsorb :
        5 * P ≤ (5 * P / Real.log 2) * L := by
      calc
        5 * P = (5 * P / Real.log 2) * Real.log 2 := by
          field_simp [hlogTwo.ne']
        _ ≤ (5 * P / Real.log 2) * L :=
          mul_le_mul_of_nonneg_left hLlog (by positivity)
    have hupperE :
        4 * (sigma - rho.re)⁻¹ ≤ 3 * m * L + E * L := by
      dsimp [E]
      nlinarith only [hupper, hPabsorb]
    have hlower := mul_le_mul_of_nonneg_left hreciprocal
      (by norm_num : (0 : ℝ) ≤ 4)
    have hineq : 4 * ((m - 1) * L) ≤ 3 * m * L + E * L :=
      hlower.trans hupperE
    have hcoef : 0 < m - 4 - E := by
      linarith only [hMcoef]
    have hmargin : 0 < (m - 4 - E) * L := mul_pos hcoef hLpos
    nlinarith only [hineq, hmargin]

end BoundedGaps.Maynard
