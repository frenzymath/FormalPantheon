import BoundedGaps.BombieriVinogradov.Analytic.ThreeFourOne
import BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionConjugation
import BoundedGaps.BombieriVinogradov.Analytic.PrincipalLFunctionHeightPole
import BoundedGaps.BombieriVinogradov.Analytic.ZeroFreeRegionArithmetic

/-!
# Excluding nonreal near-one zeros of square-principal characters

The principal doubled-height pole is small when the zero has sufficiently
large height. At small nonzero height, the conjugate zero supplies a second
selected reciprocal whose coefficient-four contribution absorbs that pole.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 119--121,
with the p. 121 conjugate denominator corrected from `gamma^2` to
`4*gamma^2`. Independent comparison: `ElkiesM229NearlyZeroFree2018`, pp. 2--3.
Semantic review: `SEM-486`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex
open scoped ComplexConjugate

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

private lemma re_inv_conjugate_height (sigma : ℝ) (rho : ℂ) :
    (((((sigma : ℂ) + rho.im * I) - conj rho)⁻¹).re) =
      (sigma - rho.re) /
        ((sigma - rho.re) ^ 2 + 4 * rho.im ^ 2) := by
  have heq :
      ((sigma : ℂ) + rho.im * I) - conj rho =
        ((sigma - rho.re : ℝ) : ℂ) + (2 * rho.im : ℝ) * I := by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [heq, re_inv_add_two_mul_I]

private lemma principal_pole_le_half_inv
    {a t : ℝ} (ha : 0 < a) (hlarge : a ≤ 2 * |t|) :
    a / (a ^ 2 + 4 * t ^ 2) ≤ 1 / (2 * a) := by
  have hsquare : a ^ 2 ≤ 4 * t ^ 2 := by
    have := (sq_le_sq₀ ha.le (by positivity : 0 ≤ 2 * |t|)).2 hlarge
    calc
      a ^ 2 ≤ (2 * |t|) ^ 2 := this
      _ = 4 * t ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have hden : 2 * a ^ 2 ≤ a ^ 2 + 4 * t ^ 2 := by linarith
  calc
    a / (a ^ 2 + 4 * t ^ 2) ≤ a / (2 * a ^ 2) :=
      div_le_div_of_nonneg_left ha.le (by positivity) hden
    _ = 1 / (2 * a) := by field_simp [ha.ne']

private lemma principal_pole_le_four_mul_conjugate
    {a x t : ℝ} (ha : 0 < a) (hax : a ≤ x)
    (hxa : x ≤ 3 * a / 2) :
    a / (a ^ 2 + 4 * t ^ 2) ≤
      4 * (x / (x ^ 2 + 4 * t ^ 2)) := by
  have hx : 0 < x := ha.trans_le hax
  have hdenA : 0 < a ^ 2 + 4 * t ^ 2 := by positivity
  have hdenX : 0 < x ^ 2 + 4 * t ^ 2 := by positivity
  rw [show 4 * (x / (x ^ 2 + 4 * t ^ 2)) =
      (4 * x) / (x ^ 2 + 4 * t ^ 2) by ring,
    div_le_div_iff₀ hdenA hdenX]
  have hxaFour : x ≤ 4 * a := hxa.trans (by linarith)
  have hfirst : a * x ^ 2 ≤ 4 * x * a ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ha.le hx.le) (sub_nonneg.mpr hxaFour)]
  have hsecond : 4 * a * t ^ 2 ≤ 16 * x * t ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hax) (sq_nonneg t)]
  nlinarith

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

/-- A square-principal nonprincipal zero in the near-one region has zero
imaginary part. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_im_eq_zero_of_sq_eq_one :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (rho : ℂ),
          chi ^ 2 = 1 →
            IsNonprincipalNontrivialLFunctionZero chi rho →
              1 - 1 / ((M : ℝ) ^ 2 *
                Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re →
                rho.im = 0 := by
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
  intro q _ chi rho hsquare hrho hbeta
  by_contra hgamma
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
  have hax : a < x := by dsimp [x, sigma]; linarith
  have hxa : x ≤ 3 * a / 2 := by
    have hmhalf : 1 / m ≤ (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num) hmTwo.le
    have hnear : 1 - rho.re ≤ 1 / (m ^ 2 * L) := by
      linarith only [hbeta']
    have haRelation : 1 / (m ^ 2 * L) = a / m := by
      dsimp [a]
      field_simp [hmpos.ne', hLpos.ne']
    rw [haRelation] at hnear
    have : a / m ≤ a / 2 := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hmhalf haPos.le
    dsimp [x, sigma]
    linarith
  let Zone : ℂ →₀ ℕ := Finsupp.single rho 1
  have hZoneSupport :
      ∀ z ∈ Zone.support,
        IsNonprincipalNontrivialLFunctionZero chi z ∧
          |z.im - rho.im| ≤ 1 := by
    intro z hz
    rw [Finsupp.support_single rho one_ne_zero] at hz
    simp only [Finset.mem_singleton] at hz
    subst z
    exact ⟨hrho, by simp⟩
  have horder := one_le_LFunction_order_of_nonprincipal_zero hrho
  have hZoneMult :
      ∀ z : ℂ,
        Zone z ≤ analyticOrderNatAt
          (DirichletCharacter.LFunction chi) z := by
    intro z
    by_cases hz : z = rho
    · subst z
      simpa [Zone] using horder
    · simp [Zone, hz]
  have hchiRaw := hselected q chi hchi rho.im sigma Zone
    hsigmaOne.le hsigmaTwo.le hZoneSupport hZoneMult
  have hZoneSum :
      Zone.sum (fun z n =>
        (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) =
          x⁻¹ := by
    calc
      _ = ((1 : ℕ) : ℝ) *
          (((((sigma : ℂ) + rho.im * I) - rho)⁻¹).re) := by
        dsimp [Zone]
        exact Finsupp.sum_single_index (a := rho) (b := 1)
          (h := fun (z : ℂ) (n : ℕ) =>
            (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re))
          (by norm_num)
      _ = x⁻¹ := by rw [Nat.cast_one, one_mul, re_inv_same_height]
  change Zone.sum (fun z n =>
      (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) -
      (16 * (A : ℝ) + 3) * L / 3 ≤
    (logDeriv (DirichletCharacter.LFunction chi)
      ((sigma : ℂ) + rho.im * I)).re at hchiRaw
  have hresidual : (16 * (A : ℝ) + 3) * L / 3 = K * L := by
    dsimp [K]
    ring
  rw [hZoneSum, hresidual] at hchiRaw
  have hchiLower :
      (m - 1) * L - K * L ≤
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
  have hsTwoSub : sTwo - 1 = (a : ℂ) + (2 * rho.im : ℝ) * I := by
    apply Complex.ext <;> simp [sTwo, sigma]
  have hpoleRe : ((sTwo - 1)⁻¹).re =
      a / (a ^ 2 + 4 * rho.im ^ 2) := by
    rw [hsTwoSub, re_inv_add_two_mul_I]
  have hdoubleLog :
      Real.log ((q : ℝ) * (|2 * rho.im| + 2)) ≤ 2 * L := by
    simpa [L, Q] using log_doubled_height_le_two_mul_log (q := q) rho.im
  have hsTwoIm : sTwo.im = 2 * rho.im := by simp [sTwo]
  have hprincipalLower :
      -a / (a ^ 2 + 4 * rho.im ^ 2) - 2 * J * L ≤
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
      -a / (a ^ 2 + 4 * rho.im ^ 2) - 2 * J * L ≤
          -a / (a ^ 2 + 4 * rho.im ^ 2) -
            J * Real.log ((q : ℝ) * (|2 * rho.im| + 2)) := by
        nlinarith only [hJlog]
      _ ≤ (logDeriv
          (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := by
        have hneg := neg_le_neg hraw
        simp only [neg_neg] at hneg
        calc
          -a / (a ^ 2 + 4 * rho.im ^ 2) -
              J * Real.log ((q : ℝ) * (|2 * rho.im| + 2)) =
              -(a / (a ^ 2 + 4 * rho.im ^ 2) +
                J * Real.log ((q : ℝ) * (|2 * rho.im| + 2))) := by ring
          _ ≤ (logDeriv
              (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := hneg
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
  by_cases hlarge : a ≤ 2 * |rho.im|
  · have hpoleHalf :
        a / (a ^ 2 + 4 * rho.im ^ 2) ≤ m * L / 2 := by
      calc
        _ ≤ 1 / (2 * a) := principal_pole_le_half_inv haPos hlarge
        _ = m * L / 2 := by
          dsimp [a]
          field_simp [hmpos.ne', hLpos.ne']
    have hlower :
        (7 * m / 2 - 4 - 4 * K - 2 * J) * L ≤
          4 * (logDeriv (DirichletCharacter.LFunction chi)
              ((sigma : ℂ) + rho.im * I)).re +
            (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := by
      have hchiFour := mul_le_mul_of_nonneg_left hchiLower (by norm_num : (0 : ℝ) ≤ 4)
      have hprincipalHalf :
          -(m * L / 2) - 2 * J * L ≤
            (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := by
        calc
          -(m * L / 2) - 2 * J * L ≤
              -(a / (a ^ 2 + 4 * rho.im ^ 2)) - 2 * J * L :=
            sub_le_sub_right (neg_le_neg hpoleHalf) _
          _ = -a / (a ^ 2 + 4 * rho.im ^ 2) - 2 * J * L := by ring
          _ ≤ (logDeriv
              (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re :=
            hprincipalLower
      calc
        _ = 4 * ((m - 1) * L - K * L) +
            (-(m * L / 2) - 2 * J * L) := by ring
        _ ≤ 4 * (logDeriv (DirichletCharacter.LFunction chi)
              ((sigma : ℂ) + rho.im * I)).re +
            (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re :=
          add_le_add hchiFour hprincipalHalf
    have : 3 * m * L + 3 * C <
        (7 * m / 2 - 4 - 4 * K - 2 * J) * L := by
      calc
        3 * m * L + 3 * C = 3 * C + 3 * m * L := by ring
        _ < (m / 2 - 4 - 4 * K - 2 * J) * L + 3 * m * L :=
          by simpa [add_comm] using
            (add_lt_add_right hmarginLog (3 * m * L))
        _ = (7 * m / 2 - 4 - 4 * K - 2 * J) * L := by ring
    exact (not_lt_of_ge hlower) (hupper.trans this)
  · have hsmall : 2 * |rho.im| < a := lt_of_not_ge hlarge
    have hdist : rho ≠ conj rho := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [conj_im] at him
      exact hgamma (by linarith only [him])
    have hrhoConj := hrho.conj_of_sq_eq_one hsquare
    have horderConj := one_le_LFunction_order_of_nonprincipal_zero hrhoConj
    let Zpair : ℂ →₀ ℕ :=
      Finsupp.single rho 1 + Finsupp.single (conj rho) 1
    have hlocalConj : |(conj rho).im - rho.im| ≤ 1 := by
      rw [conj_im]
      have : |-rho.im - rho.im| = 2 * |rho.im| := by
        rw [show -rho.im - rho.im = -(2 * rho.im) by ring,
          abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [this]
      exact (hsmall.trans haLtOne).le
    have hZpairSupport :
        ∀ z ∈ Zpair.support,
          IsNonprincipalNontrivialLFunctionZero chi z ∧
            |z.im - rho.im| ≤ 1 := by
      intro z hz
      rw [Finsupp.support_single_add_single hdist one_ne_zero one_ne_zero] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ⟨hrho, by simp⟩
      · exact ⟨hrhoConj, hlocalConj⟩
    have hZpairMult :
        ∀ z : ℂ,
          Zpair z ≤ analyticOrderNatAt
            (DirichletCharacter.LFunction chi) z := by
      intro z
      by_cases hz : z = rho
      · subst z
        simpa [Zpair, hdist, hdist.symm] using horder
      · by_cases hzc : z = conj rho
        · subst z
          simpa [Zpair, hdist, hdist.symm] using horderConj
        · simp [Zpair, hz, hzc]
    have hpairRaw := hselected q chi hchi rho.im sigma Zpair
      hsigmaOne.le hsigmaTwo.le hZpairSupport hZpairMult
    let conjugateReciprocal : ℝ :=
      x / (x ^ 2 + 4 * rho.im ^ 2)
    have hZpairSum :
        Zpair.sum (fun z n =>
          (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) =
            x⁻¹ + conjugateReciprocal := by
      dsimp [Zpair]
      rw [Finsupp.sum_single_add_single rho (conj rho) 1 1 _ hdist]
      · simp only [Nat.cast_one, one_mul]
        rw [re_inv_same_height, re_inv_conjugate_height]
      · intro z
        simp
    change Zpair.sum (fun z n =>
        (n : ℝ) * (((((sigma : ℂ) + rho.im * I) - z)⁻¹).re)) -
        (16 * (A : ℝ) + 3) * L / 3 ≤
      (logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + rho.im * I)).re at hpairRaw
    rw [hZpairSum, hresidual] at hpairRaw
    have hpoleCancel :
        a / (a ^ 2 + 4 * rho.im ^ 2) ≤
          4 * conjugateReciprocal := by
      dsimp [conjugateReciprocal]
      exact principal_pole_le_four_mul_conjugate haPos hax.le hxa
    have hlower :
        (4 * m - 4 - 4 * K - 2 * J) * L ≤
          4 * (logDeriv (DirichletCharacter.LFunction chi)
              ((sigma : ℂ) + rho.im * I)).re +
            (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := by
      have hpairSelected :
          (m - 1) * L + conjugateReciprocal - K * L ≤
            (logDeriv (DirichletCharacter.LFunction chi)
              ((sigma : ℂ) + rho.im * I)).re := by
        linarith only [hpairRaw, hreciprocal]
      have hpairFour :=
        mul_le_mul_of_nonneg_left hpairSelected (by norm_num : (0 : ℝ) ≤ 4)
      have hprincipalPair :
          -4 * conjugateReciprocal - 2 * J * L ≤
            (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re := by
        calc
          -4 * conjugateReciprocal - 2 * J * L =
              -(4 * conjugateReciprocal) - 2 * J * L := by ring
          _ ≤ -(a / (a ^ 2 + 4 * rho.im ^ 2)) - 2 * J * L :=
            sub_le_sub_right (neg_le_neg hpoleCancel) _
          _ = -a / (a ^ 2 + 4 * rho.im ^ 2) - 2 * J * L := by ring
          _ ≤ (logDeriv
              (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re :=
            hprincipalLower
      calc
        _ = 4 * ((m - 1) * L + conjugateReciprocal - K * L) +
            (-4 * conjugateReciprocal - 2 * J * L) := by ring
        _ ≤ 4 * (logDeriv (DirichletCharacter.LFunction chi)
              ((sigma : ℂ) + rho.im * I)).re +
            (logDeriv (DirichletCharacter.LFunction (chi ^ 2)) sTwo).re :=
          add_le_add hpairFour hprincipalPair
    have hmLpositive : 0 < m * L := mul_pos hmpos hLpos
    have : 3 * m * L + 3 * C <
        (4 * m - 4 - 4 * K - 2 * J) * L := by
      have hstronger :
          3 * C < (m - 4 - 4 * K - 2 * J) * L := by
        calc
          3 * C < (m / 2 - 4 - 4 * K - 2 * J) * L := hmarginLog
          _ < (m - 4 - 4 * K - 2 * J) * L := by
            nlinarith only [hmLpositive]
      calc
        3 * m * L + 3 * C = 3 * C + 3 * m * L := by ring
        _ < (m - 4 - 4 * K - 2 * J) * L + 3 * m * L :=
          by simpa [add_comm] using
            (add_lt_add_right hstronger (3 * m * L))
        _ = (4 * m - 4 - 4 * K - 2 * J) * L := by ring
    exact (not_lt_of_ge hlower) (hupper.trans this)

end BoundedGaps.Maynard
