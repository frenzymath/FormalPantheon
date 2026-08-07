import BoundedGaps.BombieriVinogradov.Analytic.DirichletGoodHeightSelector
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveFunctionalEquation
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionNontrivialSelection
import BoundedGaps.BombieriVinogradov.Analytic.PrincipalLFunctionZeroTransport

/-!
# Ordinary-zero coverage for a quantitative good height

This file proves that the two midpoint windows counted in SEM-511 cover every
guarded ordinary L-function zero capable of approaching either horizontal
edge. It then combines that classification with SEM-512's selector to obtain
clearance from both signed zero ordinates.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84--86 and
110--115. The arbitrary-character product split and two-sign correction are
project-derived. Semantic review: `SEM-513`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

private theorem gammaFactor_ne_zero_of_im_ne_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (him : rho.im ≠ 0) :
    DirichletCharacter.gammaFactor chi rho ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def, ne_eq, Gammaℝ_eq_zero_iff, not_exists]
    intro n hn
    have himEq := congrArg Complex.im hn
    norm_num at himEq
    exact him himEq
  · rw [hodd.gammaFactor_def, ne_eq, Gammaℝ_eq_zero_iff, not_exists]
    intro n hn
    have himEq := congrArg Complex.im hn
    norm_num at himEq
    exact him himEq

/-- A nonreal ordinary zero of a primitive L-function lies to the right of the
imaginary axis, including the conductor-one zeta case. -/
private theorem primitive_LFunction_zero_re_pos_of_im_ne_zero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {rho : ℂ} (him : rho.im ≠ 0)
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    0 < rho.re := by
  by_contra hre
  have hre0 : rho.re ≤ 0 := le_of_not_gt hre
  have hrho0 : rho ≠ 0 := by
    intro hrho
    apply him
    rw [hrho]
    rfl
  have hrho1 : rho ≠ 1 := by
    intro hrho
    apply him
    rw [hrho]
    rfl
  have hgamma : DirichletCharacter.gammaFactor chi rho ≠ 0 :=
    gammaFactor_ne_zero_of_im_ne_zero chi him
  have hcompleted :
      DirichletCharacter.completedLFunction chi rho = 0 := by
    have hquot := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
      chi rho (.inl hrho0)
    rw [hzero] at hquot
    exact (div_eq_zero_iff.mp hquot.symm).resolve_right hgamma
  have hfun := hchi.completedLFunction_one_sub (1 - rho)
  have hbase : (q : ℂ) ^ ((1 - rho) - 1 / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have hroot : DirichletCharacter.rootNumber chi ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_rootNumber_of_isPrimitive chi hchi]
    exact one_ne_zero
  have hreflectedCompleted :
      DirichletCharacter.completedLFunction chi⁻¹ (1 - rho) = 0 := by
    rw [show 1 - (1 - rho) = rho by ring, hcompleted] at hfun
    exact (mul_eq_zero.mp hfun.symm).resolve_left (mul_ne_zero hbase hroot)
  have hreflectedL :
      DirichletCharacter.LFunction chi⁻¹ (1 - rho) = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹
      (1 - rho) (.inl (sub_ne_zero.mpr (Ne.symm hrho1))),
      hreflectedCompleted, zero_div]
  have hreflectedGuard : chi⁻¹ ≠ 1 ∨ (1 - rho) ≠ 1 := by
    refine .inr ?_
    intro h
    apply hrho0
    linear_combination -h
  exact (chi⁻¹).LFunction_ne_zero_of_one_le_re hreflectedGuard
    (by simp; linarith) hreflectedL

private theorem LFunction_zero_re_lt_one_of_im_ne_zero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (him : rho.im ≠ 0)
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    rho.re < 1 := by
  by_contra hre
  have hguard : chi ≠ 1 ∨ rho ≠ 1 := by
    refine .inr ?_
    intro hrho
    apply him
    rw [hrho]
    rfl
  exact chi.LFunction_ne_zero_of_one_le_re hguard (le_of_not_gt hre) hzero

private theorem isPrimitiveNontrivialLFunctionZero_of_nonreal_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {rho : ℂ} (him : rho.im ≠ 0)
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    IsPrimitiveNontrivialLFunctionZero chi rho := by
  refine ⟨hq, hchi, ?_⟩
  have hgamma : DirichletCharacter.gammaFactor chi rho ≠ 0 :=
    gammaFactor_ne_zero_of_im_ne_zero chi him
  have hquot := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    chi rho (.inr (Nat.ne_of_gt hq))
  rw [hzero] at hquot
  exact (div_eq_zero_iff.mp hquot.symm).resolve_right hgamma

private theorem mem_support_divisor_riemannZetaOne_of_zero
    {U : Set ℂ} {rho : ℂ} (hrhoU : rho ∈ U)
    (hzero : riemannZeta₁ rho = 0) :
    rho ∈ (MeromorphicOn.divisor riemannZeta₁ U).support := by
  have hA : AnalyticOnNhd ℂ riemannZeta₁ U :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have htop : analyticOrderAt riemannZeta₁ rho ≠ ⊤ := by
    rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho
      (fun z => differentiable_riemannZeta₁.analyticAt z)]
    intro hzeroFunction
    have hone := congrFun hzeroFunction 1
    rw [riemannZeta₁_one] at hone
    exact one_ne_zero hone
  rw [Function.mem_support,
    MeromorphicOn.AnalyticOnNhd.divisor_apply hA hrhoU]
  lift analyticOrderAt riemannZeta₁ rho to ℕ using htop with n hn
  simp only [ENat.map_coe, WithTop.untop₀_coe]
  have horder : analyticOrderAt riemannZeta₁ rho ≠ 0 :=
    (differentiable_riemannZeta₁.analyticAt rho
      |>.analyticOrderAt_ne_zero).mpr hzero
  rw [← hn] at horder
  exact_mod_cast horder

private theorem riemannZetaOne_eq_zero_of_riemannZeta_eq_zero
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

private theorem mem_closedBall_three_of_openStrip_of_localHeight
    {rho : ℂ} {t : ℝ}
    (hre0 : 0 < rho.re) (hre1 : rho.re < 1)
    (hheight : |rho.im - t| ≤ 1) :
    rho ∈ closedBall ((2 : ℂ) + t * I) 3 := by
  have hx : (rho.re - 2) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    nlinarith
  have hy : (rho.im - t) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hheight)
  rw [mem_closedBall, Complex.dist_eq, Complex.norm_def, Real.sqrt_le_iff]
  constructor
  · norm_num
  · rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, sub_zero, Complex.sub_im, Complex.add_im]
    norm_num
    nlinarith

private theorem im_mem_dirichletLocalBadOrdinates_of_LFunction_eq_zero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ} (t : ℝ)
    (hguard : rho ≠ 1 ∨ chi ≠ 1)
    (hzero : DirichletCharacter.LFunction chi rho = 0)
    (him : rho.im ≠ 0) (hheight : |rho.im - t| ≤ 1) :
    rho.im ∈ dirichletLocalBadOrdinates chi t := by
  have hzeroOriginal := hzero
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
    hguard.symm] at hzero
  rcases mul_eq_zero.mp hzero with hbase | hproduct
  · apply Set.mem_union_left
    rw [characterBaseDivisorOrdinatesInLocalDisk]
    split_ifs with hchi
    · subst chi
      refine ⟨rho, ?_, rfl⟩
      have hre0 := primitive_LFunction_zero_re_pos_of_im_ne_zero
        (1 : DirichletCharacter ℂ q).primitiveCharacter
          (1 : DirichletCharacter ℂ q).primitiveCharacter_isPrimitive him hbase
      have hre1 := LFunction_zero_re_lt_one_of_im_ne_zero
        (1 : DirichletCharacter ℂ q).primitiveCharacter him hbase
      apply mem_support_divisor_riemannZetaOne_of_zero
        (mem_closedBall_three_of_openStrip_of_localHeight hre0 hre1 hheight)
      apply riemannZetaOne_eq_zero_of_riemannZeta_eq_zero
      exact (principal_LFunction_eq_zero_iff_riemannZeta_eq_zero_of_re_pos_of_ne_one
        hre0 (by
          intro hrho
          apply him
          rw [hrho]
          rfl)).mp hzeroOriginal
    · refine ⟨rho, ?_, rfl⟩
      have hprimitiveNe : chi.primitiveCharacter ≠ 1 := by
        intro hp
        apply hchi
        rw [← chi.changeLevel_primitiveCharacter, hp]
        exact DirichletCharacter.changeLevel_one chi.conductor_dvd_level
      have hd : 1 < chi.conductor := by
        have hd0 := chi.conductor_ne_zero
        have hd1 : chi.conductor ≠ 1 := by
          intro hd
          exact hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
        omega
      have hnontrivial :=
        isPrimitiveNontrivialLFunctionZero_of_nonreal_zero
          hd chi.primitiveCharacter chi.primitiveCharacter_isPrimitive him hbase
      apply (mem_support_divisor_LFunction_iff hprimitiveNe ?_).2 hbase
      exact mem_closedBall.mpr
        (hnontrivial.dist_two_add_mul_I_le_six hheight)
  · apply Set.mem_union_right
    refine ⟨?_, hheight⟩
    have hre := re_eq_zero_of_inducingEulerProduct_eq_zero chi hproduct
    have hrho : rho = (rho.im : ℂ) * I := by
      apply Complex.ext
      · simp [hre]
      · simp
    rw [hrho] at hproduct
    exact hproduct

/-- Every guarded ordinary zero in either signed midpoint window contributes
the corresponding positive forbidden height. -/
theorem guardedLFunctionZero_twoSidedBadHeights_coverage
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 2 ≤ T) {rho : ℂ}
    (hguard : rho ≠ 1 ∨ chi ≠ 1)
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    (|rho.im - (T + 1 / 2)| ≤ 1 →
      rho.im ∈ dirichletTwoSidedBadHeights chi T) ∧
    (|rho.im + (T + 1 / 2)| ≤ 1 →
      -rho.im ∈ dirichletTwoSidedBadHeights chi T) := by
  constructor
  · intro hheight
    have him : rho.im ≠ 0 := by
      intro him
      rw [him, zero_sub, abs_neg,
        abs_of_nonneg (by linarith [hT])] at hheight
      linarith [hT]
    rw [dirichletTwoSidedBadHeights]
    apply Set.mem_union_left
    exact im_mem_dirichletLocalBadOrdinates_of_LFunction_eq_zero
      chi (T + 1 / 2) hguard hzero him hheight
  · intro hheight
    have him : rho.im ≠ 0 := by
      intro him
      rw [him, zero_add, abs_of_nonneg (by linarith [hT])] at hheight
      linarith [hT]
    rw [dirichletTwoSidedBadHeights]
    apply Set.mem_union_right
    refine ⟨rho.im, ?_, rfl⟩
    apply im_mem_dirichletLocalBadOrdinates_of_LFunction_eq_zero
      chi (-(T + 1 / 2)) hguard hzero him
    simpa only [sub_neg_eq_add] using hheight

/-- One absolute constant selects a height separated from both horizontal
ordinates of every guarded ordinary L-function zero. -/
theorem exists_nat_guardedLFunctionZero_twoSided_clearance :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (T : ℝ),
          2 ≤ T →
            ∃ T' : ℝ, T' ∈ Icc T (T + 1) ∧
              ∀ rho : ℂ,
                (rho ≠ 1 ∨ chi ≠ 1) →
                  DirichletCharacter.LFunction chi rho = 0 →
                    (1 / ((C : ℝ) *
                        Real.log ((q : ℝ) * (T + 2))) ≤
                      |T' - rho.im|) ∧
                    (1 / ((C : ℝ) *
                        Real.log ((q : ℝ) * (T + 2))) ≤
                      |T' + rho.im|) := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_nat_dirichletTwoSidedBadHeights_clearance
  refine ⟨C, hC, ?_⟩
  intro q _ chi T hT
  obtain ⟨T', hT', hclear⟩ := hselect q chi T hT
  refine ⟨T', hT', ?_⟩
  let L := Real.log ((q : ℝ) * (T + 2))
  let delta := 1 / ((C : ℝ) * L)
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hscale : (4 : ℝ) ≤ (q : ℝ) * (T + 2) := by
    nlinarith [mul_le_mul hq (show (4 : ℝ) ≤ T + 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ q)]
  have hlogFour : (1 : ℝ) < Real.log 4 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_gt_d9]
  have hLone : (1 : ℝ) ≤ L := by
    have hlogScale : Real.log 4 ≤ L := by
      dsimp [L]
      exact Real.log_le_log (by norm_num) hscale
    exact hlogFour.le.trans hlogScale
  have hCreal : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hden : (2 : ℝ) ≤ (C : ℝ) * L := by
    nlinarith [mul_le_mul hCreal hLone (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ C)]
  have hdeltaHalf : delta ≤ 1 / 2 := by
    dsimp [delta]
    exact one_div_le_one_div_of_le (by norm_num) hden
  intro rho hguard hzero
  constructor
  · by_contra hdistance
    have hlt : |T' - rho.im| < delta := lt_of_not_ge hdistance
    have hmid : |T' - (T + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hT'.1, hT'.2]
    have hheight : |rho.im - (T + 1 / 2)| ≤ 1 := by
      have htri : |rho.im - (T + 1 / 2)| ≤
          |rho.im - T'| + |T' - (T + 1 / 2)| := by
        calc
          |rho.im - (T + 1 / 2)| =
              |(rho.im - T') + (T' - (T + 1 / 2))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have hlt' : |rho.im - T'| < 1 / 2 := by
        have := hlt.trans_le hdeltaHalf
        simpa only [abs_sub_comm] using this
      linarith
    have hbad : rho.im ∈ dirichletTwoSidedBadHeights chi T :=
      (guardedLFunctionZero_twoSidedBadHeights_coverage
        chi T hT hguard hzero).1 hheight
    exact (not_lt_of_ge (by simpa [delta, L] using hclear rho.im hbad)) hlt
  · by_contra hdistance
    have hlt : |T' + rho.im| < delta := lt_of_not_ge hdistance
    have hmid : |(T + 1 / 2) - T'| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hT'.1, hT'.2]
    have hheight : |rho.im + (T + 1 / 2)| ≤ 1 := by
      have htri : |rho.im + (T + 1 / 2)| ≤
          |rho.im + T'| + |(T + 1 / 2) - T'| := by
        calc
          |rho.im + (T + 1 / 2)| =
              |(rho.im + T') + ((T + 1 / 2) - T')| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have hlt' : |rho.im + T'| < 1 / 2 := by
        have := hlt.trans_le hdeltaHalf
        simpa only [add_comm] using this
      linarith
    have hbad : -rho.im ∈ dirichletTwoSidedBadHeights chi T :=
      (guardedLFunctionZero_twoSidedBadHeights_coverage
        chi T hT hguard hzero).2 hheight
    exact (not_lt_of_ge (by
      simpa only [sub_neg_eq_add, delta, L] using hclear (-rho.im) hbad)) hlt

end

end BoundedGaps.Maynard
