import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNontrivialZeroTransport
import BoundedGaps.BombieriVinogradov.Analytic.RegularizedProductExceptionalZero
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Nonexceptional Dirichlet zero-kernel bound

For a nontrivial Dirichlet-L zero, this file bounds the removable
explicit-formula kernel by the zero-free-region decay unless that zero is the
unique real, simple, square-principal exceptional zero at its modulus.

The source estimate is `KoukoulopoulosDistributionPrimesPrelim2022`, printed
pp. 121--122, equation (12.9). The explicit constant `12` is a project-derived
majorant obtained by splitting at `Re(rho) = 1 / 3` and `|Im(rho)| = 1`.
Semantic review: `SEM-536`.
-/

namespace BoundedGaps.Maynard

open Complex Set

noncomputable section

/-- The removable kernel is bounded by its line-segment derivative majorant.
This form remains valid at `rho = 0`. -/
theorem norm_dirichletExplicitFormulaKernel_le_rpow_mul_log
    {x : ℝ} (hx : 1 ≤ x) {rho : ℂ} (hrho : 0 ≤ rho.re) :
    ‖dirichletExplicitFormulaKernel x rho‖ ≤
      x ^ rho.re * Real.log x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  by_cases hrhozero : rho = 0
  · subst rho
    simp [dirichletExplicitFormulaKernel_zero, abs_of_nonneg hlog]
  let L : ℂ := (Real.log x : ℂ)
  let f : ℂ → ℂ := fun z => NormedSpace.exp (z • L)
  let C : ℝ := x ^ rho.re * Real.log x
  have hderiv : ∀ z ∈ segment ℝ (0 : ℂ) rho,
      HasDerivWithinAt f (NormedSpace.exp (z • L) * L)
        (segment ℝ (0 : ℂ) rho) z := by
    intro z hz
    exact (hasDerivAt_exp_smul_const L z).hasDerivWithinAt
  have hbound : ∀ z ∈ segment ℝ (0 : ℂ) rho,
      ‖NormedSpace.exp (z • L) * L‖ ≤ C := by
    intro z hz
    rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
    have hbOne : b ≤ 1 := by linarith
    have hre : (a • (0 : ℂ) + b • rho).re ≤ rho.re := by
      simp only [smul_zero, zero_add, Complex.smul_re, smul_eq_mul]
      nlinarith
    have hre' : (0 + (b : ℂ) * rho).re ≤ rho.re := by
      simpa [smul_eq_mul] using hre
    have hexp :
        ‖NormedSpace.exp ((a • (0 : ℂ) + b • rho) • L)‖ ≤
          x ^ rho.re := by
      rw [← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
      rw [Real.rpow_def_of_pos hxpos]
      apply Real.exp_le_exp.mpr
      dsimp [L]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      calc
        (0 + (b : ℂ) * rho).re * Real.log x ≤
            rho.re * Real.log x :=
          mul_le_mul_of_nonneg_right hre' hlog
        _ = Real.log x * rho.re := mul_comm _ _
    rw [norm_mul]
    have hnormL : ‖L‖ = Real.log x := by
      simp [L, abs_of_nonneg hlog]
    rw [hnormL]
    exact mul_le_mul_of_nonneg_right hexp hlog
  have hmv :=
    (convex_segment (0 : ℂ) rho).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound
      (left_mem_segment ℝ (0 : ℂ) rho)
      (right_mem_segment ℝ (0 : ℂ) rho)
  have hmul := mul_dirichletExplicitFormulaKernel x rho
  have hnormrho : 0 < ‖rho‖ := norm_pos_iff.mpr hrhozero
  have hnum :
      ‖Complex.exp (rho * (Real.log x : ℂ)) - 1‖ ≤ C * ‖rho‖ := by
    simpa [f, L, C, Complex.exp_eq_exp_ℂ, smul_eq_mul] using hmv
  calc
    ‖dirichletExplicitFormulaKernel x rho‖ =
        ‖Complex.exp (rho * (Real.log x : ℂ)) - 1‖ / ‖rho‖ := by
      rw [← hmul, norm_mul, mul_div_cancel_left₀ _ hnormrho.ne']
    _ ≤ (C * ‖rho‖) / ‖rho‖ :=
      div_le_div_of_nonneg_right hnum hnormrho.le
    _ = x ^ rho.re * Real.log x := by
      rw [mul_div_cancel_right₀ C hnormrho.ne']

private theorem norm_kernel_le_far
    {M q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {x T : ℝ} {rho : ℂ}
    (hM : 2 ≤ M) (hx : 4 ≤ x) (hT : 2 ≤ T)
    (hzero : IsDirichletNontrivialLFunctionZero chi rho)
    (hfar : rho.re < 1 - 1 / ((M : ℝ) ^ 2 *
      Real.log ((q : ℝ) * (T + 2)))) :
    ‖dirichletExplicitFormulaKernel x rho‖ ≤
      12 * x ^ (1 - 1 / ((M : ℝ) ^ 2 *
        Real.log ((q : ℝ) * (T + 2)))) / (1 + |rho.im|) := by
  let L : ℝ := Real.log ((q : ℝ) * (T + 2))
  let alpha : ℝ := 1 - 1 / ((M : ℝ) ^ 2 * L)
  let g : ℝ := |rho.im|
  have hxone : (1 : ℝ) ≤ x := by linarith
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hbeta0 : 0 ≤ rho.re := hzero.2.1.le
  have hLone : (1 : ℝ) ≤ L := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hscale : (4 : ℝ) ≤ (q : ℝ) * (T + 2) := by
      nlinarith [mul_le_mul hq (show (4 : ℝ) ≤ T + 2 by linarith)
        (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ q)]
    have hlogFour : (1 : ℝ) < Real.log 4 := by
      rw [Real.log_four_eq]
      nlinarith [Real.log_two_gt_d9]
    exact hlogFour.le.trans (Real.log_le_log (by norm_num) hscale)
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMsq : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hden : (4 : ℝ) ≤ (M : ℝ) ^ 2 * L := by
    nlinarith [mul_le_mul_of_nonneg_left hLone (sq_nonneg (M : ℝ))]
  have hinv : 1 / ((M : ℝ) ^ 2 * L) ≤ (1 / 4 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have halpha : (1 / 2 : ℝ) ≤ alpha := by
    dsimp [alpha]
    linarith
  have hbetaAlpha : rho.re ≤ alpha := by
    simpa only [alpha, L] using hfar.le
  have hpow : x ^ rho.re ≤ x ^ alpha :=
    Real.rpow_le_rpow_of_exponent_le hxone hbetaAlpha
  have hpowOne : (1 : ℝ) ≤ x ^ rho.re := by
    calc
      (1 : ℝ) = x ^ (0 : ℝ) := (Real.rpow_zero x).symm
      _ ≤ x ^ rho.re := Real.rpow_le_rpow_of_exponent_le hxone hbeta0
  have halphaPow : 0 ≤ x ^ alpha := Real.rpow_nonneg hxpos.le alpha
  have hrhoNe : rho ≠ 0 := by
    intro hrho
    subst rho
    have := hzero.2.1
    norm_num at this
  have hnormrho : 0 < ‖rho‖ := norm_pos_iff.mpr hrhoNe
  have hquot :
      ‖dirichletExplicitFormulaKernel x rho‖ ≤
        (x ^ rho.re + 1) / ‖rho‖ := by
    rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hxpos hrhoNe,
      norm_div]
    apply div_le_div_of_nonneg_right _ hnormrho.le
    calc
      ‖(x : ℂ) ^ rho - 1‖ ≤ ‖(x : ℂ) ^ rho‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = x ^ rho.re + 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, norm_one]
  have hg0 : 0 ≤ g := abs_nonneg rho.im
  have hgden : 0 < 1 + g := by linarith
  apply (le_div_iff₀ hgden).2
  by_cases hbeta : rho.re ≤ 1 / 3
  · by_cases hgamma : g ≤ 1
    · have hkernel :=
        norm_dirichletExplicitFormulaKernel_le_rpow_mul_log hxone hbeta0
      have hlog6 : Real.log x ≤ 6 * x ^ (1 / 6 : ℝ) := by
        have h := Real.log_le_rpow_div hxpos.le
          (show (0 : ℝ) < 1 / 6 by norm_num)
        convert h using 1
        ring
      have hsum : rho.re + 1 / 6 ≤ alpha := by linarith
      have hpowsum : x ^ (rho.re + 1 / 6) ≤ x ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hxone hsum
      calc
        ‖dirichletExplicitFormulaKernel x rho‖ * (1 + g) ≤
            (x ^ rho.re * Real.log x) * (1 + g) :=
          mul_le_mul_of_nonneg_right hkernel (by linarith)
        _ ≤ (x ^ rho.re * (6 * x ^ (1 / 6 : ℝ))) * 2 := by
          gcongr
          linarith
        _ = 12 * x ^ (rho.re + 1 / 6) := by
          rw [show x ^ rho.re * (6 * x ^ (1 / 6 : ℝ)) * 2 =
            12 * (x ^ rho.re * x ^ (1 / 6 : ℝ)) by ring,
            ← Real.rpow_add hxpos]
        _ ≤ 12 * x ^ alpha :=
          mul_le_mul_of_nonneg_left hpowsum (by norm_num)
    · have hgOne : 1 < g := lt_of_not_ge hgamma
      have hgNorm : g ≤ ‖rho‖ := by
        simpa [g] using Complex.abs_im_le_norm rho
      have hdenLe : 1 + g ≤ 2 * ‖rho‖ := by nlinarith
      calc
        ‖dirichletExplicitFormulaKernel x rho‖ * (1 + g) ≤
            ((x ^ rho.re + 1) / ‖rho‖) * (1 + g) :=
          mul_le_mul_of_nonneg_right hquot (by linarith)
        _ ≤ ((x ^ rho.re + 1) / ‖rho‖) * (2 * ‖rho‖) := by gcongr
        _ = 2 * (x ^ rho.re + 1) := by field_simp [hnormrho.ne']
        _ ≤ 4 * x ^ rho.re := by nlinarith
        _ ≤ 12 * x ^ alpha := by nlinarith
  · have hbetaThird : 1 / 3 < rho.re := lt_of_not_ge hbeta
    have hreNorm : rho.re ≤ ‖rho‖ := by
      have hbetaPos : 0 < rho.re := by linarith
      simpa [abs_of_pos hbetaPos] using Complex.abs_re_le_norm rho
    have himNorm : g ≤ ‖rho‖ := by
      simpa [g] using Complex.abs_im_le_norm rho
    have hdenLe : 1 + g ≤ 4 * ‖rho‖ := by nlinarith
    calc
      ‖dirichletExplicitFormulaKernel x rho‖ * (1 + g) ≤
          ((x ^ rho.re + 1) / ‖rho‖) * (1 + g) :=
        mul_le_mul_of_nonneg_right hquot (by linarith)
      _ ≤ ((x ^ rho.re + 1) / ‖rho‖) * (4 * ‖rho‖) := by gcongr
      _ = 4 * (x ^ rho.re + 1) := by field_simp [hnormrho.ne']
      _ ≤ 8 * x ^ rho.re := by nlinarith
      _ ≤ 12 * x ^ alpha := by nlinarith

private lemma near_one_of_le_of_scale_le
    {m M : ℕ} {l L beta : ℝ}
    (hm : 1 ≤ m) (hmM : m ≤ M) (hl : 0 < l) (hlL : l ≤ L)
    (hnear : 1 - 1 / ((M : ℝ) ^ 2 * L) ≤ beta) :
    1 - 1 / ((m : ℝ) ^ 2 * l) ≤ beta := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hcast : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hsquare : (m : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (m : ℝ), sq_nonneg (M : ℝ)]
  have hfirst : (m : ℝ) ^ 2 * l ≤ (M : ℝ) ^ 2 * l :=
    mul_le_mul_of_nonneg_right hsquare hl.le
  have hsecond : (M : ℝ) ^ 2 * l ≤ (M : ℝ) ^ 2 * L :=
    mul_le_mul_of_nonneg_left hlL (sq_nonneg (M : ℝ))
  have hinv : 1 / ((M : ℝ) ^ 2 * L) ≤
      1 / ((m : ℝ) ^ 2 * l) :=
    one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hmpos) hl)
      (hfirst.trans hsecond)
  linarith

/-- Each nontrivial zero has the zero-free-region kernel decay, unless it is
the unique real, simple, square-principal exceptional zero at its modulus. -/
theorem
    exists_nat_norm_dirichletExplicitFormulaKernel_le_or_exceptional :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (rho : ℂ),
          IsDirichletNontrivialLFunctionZero chi rho →
            ∀ x T : ℝ, 4 ≤ x → 2 ≤ T → T ≤ x → |rho.im| ≤ T →
              ‖dirichletExplicitFormulaKernel x rho‖ ≤
                    12 * x ^ (1 - 1 / ((M : ℝ) ^ 2 *
                      Real.log ((q : ℝ) * (T + 2)))) /
                        (1 + |rho.im|) ∨
                1 - 1 / ((M : ℝ) ^ 2 *
                    Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re ∧
                  regularizedDirichletLFunctionProduct q rho = 0 ∧
                    analyticOrderNatAt
                        (regularizedDirichletLFunctionProduct q) rho = 1 ∧
                      (∀ zeta : ℂ,
                        1 - 1 / ((M : ℝ) ^ 2 *
                            Real.log ((q : ℝ) * (|zeta.im| + 2))) ≤ zeta.re →
                          regularizedDirichletLFunctionProduct q zeta = 0 →
                            zeta = rho) ∧
                        ∃ psi : DirichletCharacter ℂ q,
                          IsNonprincipalNontrivialLFunctionZero psi rho ∧
                            chi = psi ∧ psi ^ 2 = 1 ∧ rho.im = 0 ∧
                              analyticOrderNatAt
                                  (DirichletCharacter.LFunction psi) rho = 1 ∧
                                ∀ eta : DirichletCharacter ℂ q,
                                  IsDirichletNontrivialLFunctionZero eta rho →
                                    eta = psi := by
  obtain ⟨Ms, hMs, hstructure⟩ :=
    exists_nat_regularizedDirichletLFunctionProduct_zero_structure
  obtain ⟨Mp, hMp, hprincipal⟩ :=
    exists_nat_principal_LFunction_openStrip_zero_re_lt
  obtain ⟨Mu, hMu, hunique⟩ :=
    exists_nat_regularizedDirichletLFunctionProduct_zero_eq
  let M : ℕ := max Ms (max Mp Mu)
  have hM : 2 ≤ M := hMs.trans (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  intro q _ chi rho hzero x T hx hT _hTx hheight
  let Lrho : ℝ := Real.log ((q : ℝ) * (|rho.im| + 2))
  let LT : ℝ := Real.log ((q : ℝ) * (T + 2))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hheightPos : 0 < |rho.im| + 2 := by
    linarith [abs_nonneg rho.im]
  have hLrhoPos : 0 < Lrho := by
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two
        (by
          nlinarith [mul_le_mul hq
            (show (2 : ℝ) ≤ |rho.im| + 2 by
              linarith [abs_nonneg rho.im])
            (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ q)]))
  have hLrhoLT : Lrho ≤ LT := by
    dsimp [Lrho, LT]
    apply Real.log_le_log (mul_pos (by exact_mod_cast NeZero.pos q) hheightPos)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  by_cases hnear :
      1 - 1 / ((M : ℝ) ^ 2 * Lrho) ≤ rho.re
  · right
    have hrhoOne : rho ≠ 1 := by
      intro hrho
      have hre := congrArg Complex.re hrho
      norm_num at hre
      linarith [hzero.2.2]
    have hproduct : regularizedDirichletLFunctionProduct q rho = 0 :=
      (regularizedDirichletLFunctionProduct_eq_zero_iff q rho).2
        ⟨hrhoOne, chi, hzero.1⟩
    have hnearStructure :
        1 - 1 / ((Ms : ℝ) ^ 2 * Lrho) ≤ rho.re :=
      near_one_of_le_of_scale_le (one_le_two.trans hMs)
        (le_max_left _ _) hLrhoPos le_rfl hnear
    obtain ⟨hproductOrder, psi, hpsi, hpsiSq, him,
        hpsiOrder, hlabel⟩ :=
      hstructure q rho (by simpa [Lrho] using hnearStructure) hproduct
    let L0 : ℝ := Real.log (|rho.im| + 2)
    have hL0Pos : 0 < L0 := by
      exact Real.log_pos (by linarith [abs_nonneg rho.im])
    have hL0Lrho : L0 ≤ Lrho := by
      dsimp [L0, Lrho]
      exact Real.log_le_log hheightPos (by nlinarith)
    have hnearPrincipal :
        1 - 1 / ((Mp : ℝ) ^ 2 * L0) ≤ rho.re :=
      near_one_of_le_of_scale_le (one_le_two.trans hMp)
        ((le_max_left Mp Mu).trans (le_max_right Ms (max Mp Mu)))
        hL0Pos hL0Lrho hnear
    have hall : ∀ eta : DirichletCharacter ℂ q,
        IsDirichletNontrivialLFunctionZero eta rho → eta = psi := by
      intro eta heta
      by_cases hetaOne : eta = 1
      · subst eta
        have hlt := hprincipal q rho heta.2.1 heta.2.2 heta.1
        exact (not_lt_of_ge (by simpa [L0] using hnearPrincipal) hlt).elim
      · apply hlabel
        exact (isNonprincipalNontrivialLFunctionZero_iff eta rho).2
          ⟨hetaOne, heta.1, heta.2.1, heta.2.2⟩
    have hnearUniqueRho :
        1 - 1 / ((Mu : ℝ) ^ 2 * Lrho) ≤ rho.re :=
      near_one_of_le_of_scale_le (one_le_two.trans hMu)
        ((le_max_right Mp Mu).trans (le_max_right Ms (max Mp Mu)))
        hLrhoPos le_rfl hnear
    have hpoint : ∀ zeta : ℂ,
        1 - 1 / ((M : ℝ) ^ 2 *
            Real.log ((q : ℝ) * (|zeta.im| + 2))) ≤ zeta.re →
          regularizedDirichletLFunctionProduct q zeta = 0 →
            zeta = rho := by
      intro zeta hnearZeta hproductZeta
      let Lzeta : ℝ := Real.log ((q : ℝ) * (|zeta.im| + 2))
      have hLzetaPos : 0 < Lzeta := by
        exact (Real.log_pos one_lt_two).trans_le
          (Real.log_le_log zero_lt_two
            (by simpa [Lzeta] using two_le_level_height (q := q) zeta.im))
      have hnearUniqueZeta :
          1 - 1 / ((Mu : ℝ) ^ 2 * Lzeta) ≤ zeta.re :=
        near_one_of_le_of_scale_le (one_le_two.trans hMu)
          ((le_max_right Mp Mu).trans (le_max_right Ms (max Mp Mu)))
          hLzetaPos le_rfl (by simpa only [Lzeta] using hnearZeta)
      exact hunique q zeta rho
        (by simpa only [Lzeta] using hnearUniqueZeta)
        (by simpa only [Lrho] using hnearUniqueRho)
        hproductZeta hproduct
    exact ⟨by simpa only [Lrho] using hnear, hproduct, hproductOrder,
      hpoint, psi, hpsi, hall chi hzero, hpsiSq, him, hpsiOrder, hall⟩
  · left
    have hfarActual :
        rho.re < 1 - 1 / ((M : ℝ) ^ 2 * Lrho) :=
      lt_of_not_ge hnear
    have hMpos : (0 : ℝ) < M := by
      exact_mod_cast (show 0 < M by omega)
    have hdenLe : (M : ℝ) ^ 2 * Lrho ≤ (M : ℝ) ^ 2 * LT :=
      mul_le_mul_of_nonneg_left hLrhoLT (sq_nonneg (M : ℝ))
    have hinv : 1 / ((M : ℝ) ^ 2 * LT) ≤
        1 / ((M : ℝ) ^ 2 * Lrho) :=
      one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hMpos) hLrhoPos)
        hdenLe
    have hfarT :
        rho.re < 1 - 1 / ((M : ℝ) ^ 2 * LT) := by
      linarith
    simpa only [M, LT] using
      (norm_kernel_le_far (M := M) hM hx hT hzero
        (by simpa only [LT] using hfarT))

end

end BoundedGaps.Maynard
