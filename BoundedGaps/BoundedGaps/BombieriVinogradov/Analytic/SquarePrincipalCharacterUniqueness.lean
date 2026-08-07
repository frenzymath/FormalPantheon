import BoundedGaps.BombieriVinogradov.Analytic.CrossCharacterPositivity
import BoundedGaps.BombieriVinogradov.Analytic.ImprimitiveLFunctionTransport
import BoundedGaps.BombieriVinogradov.Analytic.SquarePrincipalRealSimple
import BoundedGaps.BombieriVinogradov.Analytic.ZeroFreeRegionArithmetic

/-!
# Cross-character uniqueness for square-principal near-one zeros

The exact four-factor positivity inequality combines lower bounds from one
selected zero of each input character with an empty-selection lower bound for
their product. Distinct square-principal characters have nonprincipal product,
so the resulting lower bound contradicts the coefficient-one zeta pole bound.

Source: `ElkiesM229NearlyZeroFree2018`, printed p. 4, equation (4), as an
exact replacement for the corrected cross-character step in
`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 121. Semantic review:
`SEM-488`.
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

private lemma mul_ne_one_of_sq_eq_one_of_ne
    {q : ℕ} {chi1 chi2 : DirichletCharacter ℂ q}
    (hsquare1 : chi1 ^ 2 = 1) (hne : chi1 ≠ chi2) :
    chi1 * chi2 ≠ 1 := by
  intro hproduct
  have hself : chi1⁻¹ = chi1 :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsquare1)
  have hother : chi1⁻¹ = chi2 := inv_eq_of_mul_eq_one_right hproduct
  exact hne (hself.symm.trans hother)

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

/-- Two square-principal characters with real near-one zeros are equal. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_of_sq_eq_one_of_im_eq_zero :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi1 chi2 : DirichletCharacter ℂ q) (rho1 rho2 : ℂ),
          chi1 ^ 2 = 1 →
            chi2 ^ 2 = 1 →
              IsNonprincipalNontrivialLFunctionZero chi1 rho1 →
                IsNonprincipalNontrivialLFunctionZero chi2 rho2 →
                  rho1.im = 0 →
                    rho2.im = 0 →
                      1 - 1 / ((M : ℝ) ^ 2 *
                        Real.log ((q : ℝ) * (|rho1.im| + 2))) ≤ rho1.re →
                        1 - 1 / ((M : ℝ) ^ 2 *
                          Real.log ((q : ℝ) * (|rho2.im| + 2))) ≤ rho2.re →
                          chi1 = chi2 := by
  obtain ⟨A, _, hselected⟩ :=
    exists_nat_selectedNonprincipalNontrivialZeros_sum_sub_le_re_logDeriv_LFunction
  obtain ⟨C, hC, hzeta⟩ :=
    exists_pos_neg_logDeriv_riemannZeta_re_lt_inv_sub_one_add
  let K : ℝ := (16 * (A : ℝ) + 3) / 3
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  let R : ℝ := 2 + 3 * K + C / Real.log 2
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
  have hmargin : C / Real.log 2 < m - 2 - 3 * K := by
    dsimp [R] at hmThreshold
    linarith
  refine ⟨M, hMtwo, ?_⟩
  intro q _ chi1 chi2 rho1 rho2 hsquare1 hsquare2 hrho1 hrho2
    him1 him2 hbeta1 hbeta2
  by_contra hne
  have hproduct : chi1 * chi2 ≠ 1 :=
    mul_ne_one_of_sq_eq_one_of_ne hsquare1 hne
  let L : ℝ := Real.log ((q : ℝ) * 2)
  let a : ℝ := 1 / (m * L)
  let sigma : ℝ := 1 + a
  have hscale : (2 : ℝ) ≤ (q : ℝ) * 2 := by
    simpa using two_le_level_height (q := q) 0
  have hlogLower : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log zero_lt_two hscale
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
  obtain ⟨hchi1, _, _, hrho1One⟩ :=
    (isNonprincipalNontrivialLFunctionZero_iff chi1 rho1).1 hrho1
  obtain ⟨hchi2, _, _, hrho2One⟩ :=
    (isNonprincipalNontrivialLFunctionZero_iff chi2 rho2).1 hrho2
  have hbeta1' : 1 - 1 / (m ^ 2 * L) ≤ rho1.re := by
    simpa [m, L, him1] using hbeta1
  have hbeta2' : 1 - 1 / (m ^ 2 * L) ≤ rho2.re := by
    simpa [m, L, him2] using hbeta2
  have hreciprocal1 :
      (m - 1) * L ≤ (sigma - rho1.re)⁻¹ := by
    simpa [sigma, a] using mul_sub_one_le_inv_one_add_inv_sub
      (m := m) (L := L) (beta := rho1.re) hmTwo.le hLpos
        hbeta1' hrho1One
  have hreciprocal2 :
      (m - 1) * L ≤ (sigma - rho2.re)⁻¹ := by
    simpa [sigma, a] using mul_sub_one_le_inv_one_add_inv_sub
      (m := m) (L := L) (beta := rho2.re) hmTwo.le hLpos
        hbeta2' hrho2One
  have hresidual : (16 * (A : ℝ) + 3) * L / 3 = K * L := by
    dsimp [K]
    ring
  have hcharLower (chi : DirichletCharacter ℂ q) (rho : ℂ)
      (hchi : chi ≠ 1)
      (hrho : IsNonprincipalNontrivialLFunctionZero chi rho)
      (him : rho.im = 0)
      (hreciprocal : (m - 1) * L ≤ (sigma - rho.re)⁻¹) :
      (m - 1 - K) * L ≤
        (logDeriv (DirichletCharacter.LFunction chi) (sigma : ℂ)).re := by
    let Zone : ℂ →₀ ℕ := Finsupp.single rho 1
    have hZoneSupport :
        ∀ z ∈ Zone.support,
          IsNonprincipalNontrivialLFunctionZero chi z ∧ |z.im - 0| ≤ 1 := by
      intro z hz
      rw [Finsupp.support_single rho one_ne_zero] at hz
      simp only [Finset.mem_singleton] at hz
      subst z
      exact ⟨hrho, by simp [him]⟩
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
    have hraw := hselected q chi hchi 0 sigma Zone
      hsigmaOne.le hsigmaTwo.le hZoneSupport hZoneMult
    simp only [abs_zero, zero_add] at hraw
    change Zone.sum (fun z n =>
        (n : ℝ) * (((((sigma : ℂ) + (0 : ℝ) * I - z)⁻¹).re))) -
        (16 * (A : ℝ) + 3) * L / 3 ≤
      (logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + (0 : ℝ) * I)).re at hraw
    have hZoneSum :
        Zone.sum (fun z n =>
          (n : ℝ) *
            (((((sigma : ℂ) + (0 : ℝ) * I - z)⁻¹).re))) =
            (sigma - rho.re)⁻¹ := by
      calc
        _ = ((1 : ℕ) : ℝ) *
            ((((sigma : ℂ) + (0 : ℝ) * I - rho)⁻¹).re) := by
          dsimp [Zone]
          exact Finsupp.sum_single_index (a := rho) (b := 1)
            (h := fun (z : ℂ) (n : ℕ) =>
              (n : ℝ) *
                (((((sigma : ℂ) + (0 : ℝ) * I - z)⁻¹).re)))
            (by norm_num)
        _ = (sigma - rho.re)⁻¹ := by
          rw [Nat.cast_one, one_mul]
          simpa [him] using re_inv_same_height sigma rho
    rw [hZoneSum, hresidual] at hraw
    have hraw' :
        (sigma - rho.re)⁻¹ - K * L ≤
          (logDeriv (DirichletCharacter.LFunction chi) (sigma : ℂ)).re := by
      simpa using hraw
    nlinarith only [hreciprocal, hraw']
  have hchi1Lower :=
    hcharLower chi1 rho1 hchi1 hrho1 him1 hreciprocal1
  have hchi2Lower :=
    hcharLower chi2 rho2 hchi2 hrho2 him2 hreciprocal2
  let Zempty : ℂ →₀ ℕ := 0
  have hEmptySupport :
      ∀ z ∈ Zempty.support,
        IsNonprincipalNontrivialLFunctionZero (chi1 * chi2) z ∧
          |z.im - 0| ≤ 1 := by
    intro z hz
    simp [Zempty] at hz
  have hEmptyMult :
      ∀ z : ℂ,
        Zempty z ≤ analyticOrderNatAt
          (DirichletCharacter.LFunction (chi1 * chi2)) z := by
    intro z
    simp [Zempty]
  have hproductRaw := hselected q (chi1 * chi2) hproduct 0 sigma Zempty
    hsigmaOne.le hsigmaTwo.le hEmptySupport hEmptyMult
  simp only [abs_zero, zero_add] at hproductRaw
  change Zempty.sum (fun z n =>
      (n : ℝ) *
        (((((sigma : ℂ) + (0 : ℝ) * I - z)⁻¹).re))) -
      (16 * (A : ℝ) + 3) * L / 3 ≤
    (logDeriv (DirichletCharacter.LFunction (chi1 * chi2))
      ((sigma : ℂ) + (0 : ℝ) * I)).re at hproductRaw
  have hproductLower :
      -K * L ≤
        (logDeriv (DirichletCharacter.LFunction (chi1 * chi2))
          (sigma : ℂ)).re := by
    rw [show Zempty.sum (fun z n =>
        (n : ℝ) *
          (((((sigma : ℂ) + (0 : ℝ) * I - z)⁻¹).re))) = 0 by
          simp [Zempty],
      hresidual] at hproductRaw
    simpa using hproductRaw
  have hfour := four_factor_logDeriv_le_neg_logDeriv_riemannZeta
    chi1 chi2 hsquare1 hsquare2 hsigmaOne
  have hpoleSigma : (sigma - 1)⁻¹ = m * L := by
    have heq : sigma - 1 = (m * L)⁻¹ := by
      dsimp [sigma, a]
      rw [one_div]
      ring
    rw [heq, inv_inv]
  have hzetaBound := hzeta sigma hsigmaOne hsigmaTwo
  rw [hpoleSigma] at hzetaBound
  have hzetaUpper :
      (-logDeriv riemannZeta (sigma : ℂ)).re < m * L + C :=
    hzetaBound
  have hlower :
      (2 * m - 2 - 3 * K) * L ≤
        (logDeriv (DirichletCharacter.LFunction chi1) (sigma : ℂ)).re +
          (logDeriv (DirichletCharacter.LFunction chi2) (sigma : ℂ)).re +
            (logDeriv (DirichletCharacter.LFunction (chi1 * chi2))
              (sigma : ℂ)).re := by
    nlinarith only [hchi1Lower, hchi2Lower, hproductLower]
  have hsumUpper :
      (logDeriv (DirichletCharacter.LFunction chi1) (sigma : ℂ)).re +
          (logDeriv (DirichletCharacter.LFunction chi2) (sigma : ℂ)).re +
            (logDeriv (DirichletCharacter.LFunction (chi1 * chi2))
              (sigma : ℂ)).re < m * L + C :=
    hfour.trans_lt hzetaUpper
  have hmarginPos : 0 < m - 2 - 3 * K :=
    (div_pos hC hlogTwo).trans hmargin
  have hmarginLog : C < (m - 2 - 3 * K) * L := by
    calc
      C = (C / Real.log 2) * Real.log 2 := by field_simp
      _ < (m - 2 - 3 * K) * Real.log 2 :=
        mul_lt_mul_of_pos_right hmargin hlogTwo
      _ ≤ (m - 2 - 3 * K) * L :=
        mul_le_mul_of_nonneg_left hlogLower hmarginPos.le
  have hstrict :
      m * L + C < (2 * m - 2 - 3 * K) * L := by
    nlinarith only [hmarginLog, hmpos, hLpos]
  exact (not_lt_of_ge hlower) (hsumUpper.trans hstrict)

/-- Two square-principal characters with arbitrary near-one zeros are equal. -/
theorem exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_of_sq_eq_one :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi1 chi2 : DirichletCharacter ℂ q) (rho1 rho2 : ℂ),
          chi1 ^ 2 = 1 →
            chi2 ^ 2 = 1 →
              IsNonprincipalNontrivialLFunctionZero chi1 rho1 →
                IsNonprincipalNontrivialLFunctionZero chi2 rho2 →
                  1 - 1 / ((M : ℝ) ^ 2 *
                    Real.log ((q : ℝ) * (|rho1.im| + 2))) ≤ rho1.re →
                    1 - 1 / ((M : ℝ) ^ 2 *
                      Real.log ((q : ℝ) * (|rho2.im| + 2))) ≤ rho2.re →
                      chi1 = chi2 := by
  obtain ⟨Mreal, hMreal, hreal⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_real_simple_of_sq_eq_one
  obtain ⟨Mchar, hMchar, hchar⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_of_sq_eq_one_of_im_eq_zero
  let M := max Mreal Mchar
  have hMtwo : 2 ≤ M := hMreal.trans (le_max_left _ _)
  refine ⟨M, hMtwo, ?_⟩
  intro q _ chi1 chi2 rho1 rho2 hsquare1 hsquare2 hrho1 hrho2
    hnear1 hnear2
  let L1 : ℝ := Real.log ((q : ℝ) * (|rho1.im| + 2))
  let L2 : ℝ := Real.log ((q : ℝ) * (|rho2.im| + 2))
  have hscale1 : (2 : ℝ) ≤ (q : ℝ) * (|rho1.im| + 2) :=
    two_le_level_height (q := q) rho1.im
  have hscale2 : (2 : ℝ) ≤ (q : ℝ) * (|rho2.im| + 2) :=
    two_le_level_height (q := q) rho2.im
  have hL1pos : 0 < L1 := by
    dsimp [L1]
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two hscale1)
  have hL2pos : 0 < L2 := by
    dsimp [L2]
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two hscale2)
  have hnearReal1 :
      1 - 1 / ((Mreal : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le (one_le_two.trans hMreal)
      (le_max_left _ _) hL1pos
    simpa only [M, L1] using hnear1
  have hnearReal2 :
      1 - 1 / ((Mreal : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le (one_le_two.trans hMreal)
      (le_max_left _ _) hL2pos
    simpa only [M, L2] using hnear2
  have him1 := (hreal q chi1 rho1 hsquare1 hrho1
    (by simpa only [L1] using hnearReal1)).1
  have him2 := (hreal q chi2 rho2 hsquare2 hrho2
    (by simpa only [L2] using hnearReal2)).1
  have hnearChar1 :
      1 - 1 / ((Mchar : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le (one_le_two.trans hMchar)
      (le_max_right _ _) hL1pos
    simpa only [M, L1] using hnear1
  have hnearChar2 :
      1 - 1 / ((Mchar : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le (one_le_two.trans hMchar)
      (le_max_right _ _) hL2pos
    simpa only [M, L2] using hnear2
  exact hchar q chi1 chi2 rho1 rho2 hsquare1 hsquare2 hrho1 hrho2
    him1 him2 (by simpa only [L1] using hnearChar1)
      (by simpa only [L2] using hnearChar2)

end BoundedGaps.Maynard
