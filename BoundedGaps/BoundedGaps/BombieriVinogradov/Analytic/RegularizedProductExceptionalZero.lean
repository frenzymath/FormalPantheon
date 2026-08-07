import BoundedGaps.BombieriVinogradov.Analytic.NonprincipalExceptionalZero
import BoundedGaps.BombieriVinogradov.Analytic.PrincipalLFunctionZeroTransport
import BoundedGaps.BombieriVinogradov.Analytic.RegularizedLFunctionProduct

/-!
# Exceptional zeros of the regularized character product

This file composes the principal zero-free region, the nonprincipal
constituent structure and uniqueness theorem, and the regularized finite
product. Every near-one product zero is carried by one unique real
square-principal nonprincipal character and has analytic order one. At a
fixed modulus, there is at most one such product-zero point.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 119--121,
Theorem 12.3 and equation (12.2). Semantic review: `SEM-494`.
-/

noncomputable section

open scoped Classical

namespace BoundedGaps.Maynard

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

private lemma re_pos_of_near_one
    {M q : ℕ} [NeZero q] {rho : ℂ} (hM : 2 ≤ M)
    (hnear : 1 - 1 / ((M : ℝ) ^ 2 *
      Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re) :
    0 < rho.re := by
  let L : ℝ := Real.log ((q : ℝ) * (|rho.im| + 2))
  have hlog : (1 / 2 : ℝ) < L := by
    have hhalf : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    exact hhalf.trans_le
      (Real.log_le_log zero_lt_two
        (by simpa [L] using two_le_level_height (q := q) rho.im))
  have hMcast : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := zero_lt_two.trans_le hMcast
  have hMsquare : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hden : (1 : ℝ) < (M : ℝ) ^ 2 * L := by
    calc
      (1 : ℝ) < 4 * (1 / 2 : ℝ) := by norm_num
      _ ≤ (M : ℝ) ^ 2 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hMsquare (by norm_num)
      _ < (M : ℝ) ^ 2 * L :=
        mul_lt_mul_of_pos_left hlog (sq_pos_of_pos hMpos)
  have hinv : 1 / ((M : ℝ) ^ 2 * L) < 1 :=
    (div_lt_one (zero_lt_one.trans hden)).2 hden
  dsimp [L] at hinv
  linarith

private lemma re_lt_one_of_constituent_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hrho : rho ≠ 1) (hzero : DirichletCharacter.LFunction chi rho = 0) :
    rho.re < 1 := by
  apply lt_of_not_ge
  intro hre
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi
    (.inr hrho) hre) hzero

/-- A near-one zero of the regularized product is carried by one unique
nonprincipal constituent and is real and simple. -/
theorem exists_nat_regularizedDirichletLFunctionProduct_zero_structure :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q] (rho : ℂ),
        1 - 1 / ((M : ℝ) ^ 2 *
          Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re →
          regularizedDirichletLFunctionProduct q rho = 0 →
            analyticOrderNatAt
                (regularizedDirichletLFunctionProduct q) rho = 1 ∧
              ∃ chi : DirichletCharacter ℂ q,
                IsNonprincipalNontrivialLFunctionZero chi rho ∧
                  chi ^ 2 = 1 ∧
                    rho.im = 0 ∧
                      analyticOrderNatAt
                          (DirichletCharacter.LFunction chi) rho = 1 ∧
                        ∀ psi : DirichletCharacter ℂ q,
                          IsNonprincipalNontrivialLFunctionZero psi rho →
                            psi = chi := by
  obtain ⟨Mprincipal, hMprincipal, hprincipal⟩ :=
    exists_nat_principal_LFunction_openStrip_zero_re_lt
  obtain ⟨Mshape, hMshape, hshape⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_sq_eq_one_real_simple
  obtain ⟨Munique, hMunique, hunique⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_and_zero_eq
  let M := max Mprincipal (max Mshape Munique)
  have hMtwo : 2 ≤ M := hMprincipal.trans (le_max_left _ _)
  refine ⟨M, hMtwo, ?_⟩
  intro q _ rho hnear hproductZero
  obtain ⟨hrhoOne, chi, hchiZero⟩ :=
    (regularizedDirichletLFunctionProduct_eq_zero_iff q rho).mp hproductZero
  have hrhoPos : 0 < rho.re := re_pos_of_near_one hMtwo hnear
  have hrhoLt : rho.re < 1 :=
    re_lt_one_of_constituent_zero chi hrhoOne hchiZero
  let Lq : ℝ := Real.log ((q : ℝ) * (|rho.im| + 2))
  let L0 : ℝ := Real.log (|rho.im| + 2)
  have hLqPos : 0 < Lq := by
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two
        (by simpa [Lq] using two_le_level_height (q := q) rho.im))
  have hL0Pos : 0 < L0 := by
    apply Real.log_pos
    linarith [abs_nonneg rho.im]
  have hL0Lq : L0 ≤ Lq := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have ht : (0 : ℝ) < |rho.im| + 2 := by
      linarith [abs_nonneg rho.im]
    apply Real.log_le_log ht
    nlinarith
  have hnearPrincipal :
      1 - 1 / ((Mprincipal : ℝ) ^ 2 * L0) ≤ rho.re := by
    apply near_one_of_le_of_scale_le (one_le_two.trans hMprincipal)
      (le_max_left _ _) hL0Pos hL0Lq
    simpa only [M, Lq] using hnear
  have hprincipalNe :
      DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) rho ≠ 0 := by
    intro hzero
    have hlt := hprincipal q rho hrhoPos hrhoLt hzero
    exact (not_lt_of_ge (by simpa only [L0] using hnearPrincipal)) hlt
  have hchiNe : chi ≠ 1 := by
    intro hchi
    subst chi
    exact hprincipalNe hchiZero
  have hchi : IsNonprincipalNontrivialLFunctionZero chi rho :=
    (isNonprincipalNontrivialLFunctionZero_iff chi rho).2
      ⟨hchiNe, hchiZero, hrhoPos, hrhoLt⟩
  have hnearShape :
      1 - 1 / ((Mshape : ℝ) ^ 2 * Lq) ≤ rho.re := by
    apply near_one_of_le_of_scale_le (one_le_two.trans hMshape)
      ((le_max_left Mshape Munique).trans (le_max_right Mprincipal _))
      hLqPos le_rfl
    simpa only [M, Lq] using hnear
  have hnearUnique :
      1 - 1 / ((Munique : ℝ) ^ 2 * Lq) ≤ rho.re := by
    apply near_one_of_le_of_scale_le (one_le_two.trans hMunique)
      ((le_max_right Mshape Munique).trans (le_max_right Mprincipal _))
      hLqPos le_rfl
    simpa only [M, Lq] using hnear
  have hshapeResult := hshape q chi rho hchi
    (by simpa only [Lq] using hnearShape)
  have hlabel : ∀ psi : DirichletCharacter ℂ q,
      IsNonprincipalNontrivialLFunctionZero psi rho → psi = chi := by
    intro psi hpsi
    exact (hunique q chi psi rho rho hchi hpsi
      (by simpa only [Lq] using hnearUnique)
      (by simpa only [Lq] using hnearUnique)).1.symm
  have hprincipalRegularizedNe :
      DirichletCharacter.LFunctionTrivChar₁ q rho ≠ 0 := by
    rw [DirichletCharacter.LFunctionTrivChar₁,
      Function.update_of_ne hrhoOne]
    exact mul_ne_zero (sub_ne_zero.mpr hrhoOne) hprincipalNe
  have hchiMem : chi ∈
      Finset.univ.erase (1 : DirichletCharacter ℂ q) :=
    Finset.mem_erase.mpr ⟨hchiNe, Finset.mem_univ chi⟩
  have hotherNe : ∀ psi ∈
      (Finset.univ.erase (1 : DirichletCharacter ℂ q)).erase chi,
        DirichletCharacter.LFunction psi rho ≠ 0 := by
    intro psi hpsi
    have hpsiNeChi := Finset.ne_of_mem_erase hpsi
    have hpsiMem := Finset.mem_of_mem_erase hpsi
    have hpsiNeOne := Finset.ne_of_mem_erase hpsiMem
    intro hpsiZero
    have hpsiPred : IsNonprincipalNontrivialLFunctionZero psi rho :=
      (isNonprincipalNontrivialLFunctionZero_iff psi rho).2
        ⟨hpsiNeOne, hpsiZero, hrhoPos, hrhoLt⟩
    exact hpsiNeChi (hlabel psi hpsiPred)
  let G : ℂ → ℂ := fun z =>
    DirichletCharacter.LFunctionTrivChar₁ q z *
      ∏ psi ∈
        (Finset.univ.erase (1 : DirichletCharacter ℂ q)).erase chi,
          DirichletCharacter.LFunction psi z
  have hGAnalytic : AnalyticAt ℂ G rho := by
    apply ((DirichletCharacter.differentiable_LFunctionTrivChar₁ q).mul ?_).analyticAt
    apply Differentiable.fun_finsetProd
    intro psi hpsi
    exact DirichletCharacter.differentiable_LFunction
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hpsi))
  have hGNe : G rho ≠ 0 := by
    apply mul_ne_zero hprincipalRegularizedNe
    rw [Finset.prod_ne_zero_iff]
    exact hotherNe
  have hfactor : regularizedDirichletLFunctionProduct q =
      DirichletCharacter.LFunction chi * G := by
    funext z
    simp only [Pi.mul_apply]
    dsimp only [G, regularizedDirichletLFunctionProduct]
    rw [← Finset.mul_prod_erase
      (Finset.univ.erase (1 : DirichletCharacter ℂ q))
      (fun psi : DirichletCharacter ℂ q =>
        DirichletCharacter.LFunction psi z) hchiMem]
    ring
  have hchiAnalytic : AnalyticAt ℂ
      (DirichletCharacter.LFunction chi) rho :=
    (DirichletCharacter.differentiable_LFunction hchiNe).analyticAt rho
  have hchiFinite :
      analyticOrderAt (DirichletCharacter.LFunction chi) rho ≠ ⊤ := by
    intro htop
    have horder := hshapeResult.2.2
    simp [analyticOrderNatAt, htop] at horder
  have hGOrderZero : analyticOrderAt G rho = 0 :=
    hGAnalytic.analyticOrderAt_eq_zero.mpr hGNe
  have hGFinite : analyticOrderAt G rho ≠ ⊤ := by
    rw [hGOrderZero]
    simp
  have hGNatOrderZero : analyticOrderNatAt G rho = 0 := by
    simp [analyticOrderNatAt, hGOrderZero]
  have hproductOrder : analyticOrderNatAt
      (regularizedDirichletLFunctionProduct q) rho = 1 := by
    rw [hfactor, analyticOrderNatAt_mul hchiAnalytic hGAnalytic
      hchiFinite hGFinite, hshapeResult.2.2, hGNatOrderZero, add_zero]
  exact ⟨hproductOrder, chi, hchi, hshapeResult.1,
    hshapeResult.2.1, hshapeResult.2.2, hlabel⟩

/-- A fixed modulus has at most one regularized-product zero in the near-one
region. -/
theorem exists_nat_regularizedDirichletLFunctionProduct_zero_eq :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (q : ℕ) [NeZero q] (rho1 rho2 : ℂ),
        1 - 1 / ((M : ℝ) ^ 2 *
          Real.log ((q : ℝ) * (|rho1.im| + 2))) ≤ rho1.re →
          1 - 1 / ((M : ℝ) ^ 2 *
            Real.log ((q : ℝ) * (|rho2.im| + 2))) ≤ rho2.re →
            regularizedDirichletLFunctionProduct q rho1 = 0 →
              regularizedDirichletLFunctionProduct q rho2 = 0 →
                rho1 = rho2 := by
  obtain ⟨Mstructure, hMstructure, hstructure⟩ :=
    exists_nat_regularizedDirichletLFunctionProduct_zero_structure
  obtain ⟨Mpair, hMpair, hpair⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_and_zero_eq
  let M := max Mstructure Mpair
  have hMtwo : 2 ≤ M := hMstructure.trans (le_max_left _ _)
  refine ⟨M, hMtwo, ?_⟩
  intro q _ rho1 rho2 hnear1 hnear2 hzero1 hzero2
  let L1 : ℝ := Real.log ((q : ℝ) * (|rho1.im| + 2))
  let L2 : ℝ := Real.log ((q : ℝ) * (|rho2.im| + 2))
  have hL1Pos : 0 < L1 := by
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two
        (by simpa [L1] using two_le_level_height (q := q) rho1.im))
  have hL2Pos : 0 < L2 := by
    exact (Real.log_pos one_lt_two).trans_le
      (Real.log_le_log zero_lt_two
        (by simpa [L2] using two_le_level_height (q := q) rho2.im))
  have hnearStructure1 :
      1 - 1 / ((Mstructure : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le_of_scale_le (one_le_two.trans hMstructure)
      (le_max_left _ _) hL1Pos le_rfl
    simpa only [M, L1] using hnear1
  have hnearStructure2 :
      1 - 1 / ((Mstructure : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le_of_scale_le (one_le_two.trans hMstructure)
      (le_max_left _ _) hL2Pos le_rfl
    simpa only [M, L2] using hnear2
  obtain ⟨_, chi1, hchi1, _⟩ := hstructure q rho1
    (by simpa only [L1] using hnearStructure1) hzero1
  obtain ⟨_, chi2, hchi2, _⟩ := hstructure q rho2
    (by simpa only [L2] using hnearStructure2) hzero2
  have hnearPair1 :
      1 - 1 / ((Mpair : ℝ) ^ 2 * L1) ≤ rho1.re := by
    apply near_one_of_le_of_scale_le (one_le_two.trans hMpair)
      (le_max_right _ _) hL1Pos le_rfl
    simpa only [M, L1] using hnear1
  have hnearPair2 :
      1 - 1 / ((Mpair : ℝ) ^ 2 * L2) ≤ rho2.re := by
    apply near_one_of_le_of_scale_le (one_le_two.trans hMpair)
      (le_max_right _ _) hL2Pos le_rfl
    simpa only [M, L2] using hnear2
  exact (hpair q chi1 chi2 rho1 rho2 hchi1 hchi2
    (by simpa only [L1] using hnearPair1)
    (by simpa only [L2] using hnearPair2)).2

end BoundedGaps.Maynard
