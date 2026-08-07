import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveFunctionalEquation
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionCentralStrip
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Primitive Dirichlet zeros in the shallow left strip

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 112--113,
classifies the parity-dependent trivial zeros of primitive Dirichlet
L-functions. On `-1/2 < Re(s) <= 0`, the only possible ordinary zero is the
origin for an even nonprincipal character, and that zero is simple.

The source's cited Theorem 12.8 covers only real characters. The simplicity
proof here instead uses Mathlib's all-complex-character nonvanishing theorem
at one. Semantic reviews: `SEM-525` and `SEM-530`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Filter Set
open scoped Topology

private theorem primitive_LFunction_zero_forces_gammaFactor_zero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {rho : ℂ} (hright : rho.re ≤ 0)
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    DirichletCharacter.gammaFactor chi rho = 0 := by
  by_contra hgamma
  have hrelationGuard : rho ≠ 0 ∨ q ≠ 1 := by
    by_cases hrho : rho = 0
    · right
      intro hq
      subst q
      rw [hrho, DirichletCharacter.LFunction_modOne_eq,
        riemannZeta_zero] at hzero
      norm_num at hzero
    · exact .inl hrho
  have hcompleted :
      DirichletCharacter.completedLFunction chi rho = 0 := by
    have hquot := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
      chi rho hrelationGuard
    rw [hzero] at hquot
    exact (div_eq_zero_iff.mp hquot.symm).resolve_right hgamma
  have hqzero : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hbase : (q : ℂ) ^ ((1 - rho) - 1 / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl hqzero)
  have hroot : DirichletCharacter.rootNumber chi ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_rootNumber_of_isPrimitive chi hchi]
    exact one_ne_zero
  have hfun := hchi.completedLFunction_one_sub (1 - rho)
  have hreflectedCompleted :
      DirichletCharacter.completedLFunction chi⁻¹ (1 - rho) = 0 := by
    rw [show 1 - (1 - rho) = rho by ring, hcompleted] at hfun
    exact (mul_eq_zero.mp hfun.symm).resolve_left (mul_ne_zero hbase hroot)
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    norm_num at hre
    linarith
  have hreflectedL :
      DirichletCharacter.LFunction chi⁻¹ (1 - rho) = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹
      (1 - rho) (.inl (sub_ne_zero.mpr (Ne.symm hrhoOne))),
      hreflectedCompleted, zero_div]
  have hreflectedGuard : chi⁻¹ ≠ 1 ∨ (1 - rho) ≠ 1 := by
    by_cases hrho : rho = 0
    · left
      apply inv_ne_one.mpr
      have hq : 1 < q := by
        have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
        have hqne : q ≠ 1 := hrelationGuard.resolve_left (not_ne_iff.mpr hrho)
        omega
      exact character_ne_one_of_isPrimitive hq chi hchi
    · right
      intro h
      apply hrho
      linear_combination -h
  exact (chi⁻¹).LFunction_ne_zero_of_one_le_re hreflectedGuard
    (by simp; linarith) hreflectedL

/-- Every primitive ordinary zero stays at least one half from the fixed
negative-half vertical line. -/
theorem
    one_half_le_norm_neg_half_add_mul_I_sub_of_LFunction_eq_zero_of_isPrimitive
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) {rho : ℂ}
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    (1 / 2 : ℝ) ≤
      ‖(((-1 / 2 : ℝ) : ℂ) + t * Complex.I) - rho‖ := by
  by_contra hsep
  rw [not_le] at hsep
  let s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I
  have hreNorm : |(-1 / 2 : ℝ) - rho.re| ≤ ‖s - rho‖ := by
    have h := Complex.abs_re_le_norm (s - rho)
    simpa [s] using h
  have hreAbs : |(-1 / 2 : ℝ) - rho.re| < 1 / 2 :=
    hreNorm.trans_lt (by simpa [s] using hsep)
  rw [abs_lt] at hreAbs
  have hrhoLower : (-1 : ℝ) < rho.re := by linarith [hreAbs.1]
  have hrhoUpper : rho.re < 0 := by linarith [hreAbs.2]
  have hgamma := primitive_LFunction_zero_forces_gammaFactor_zero
    chi hchi hrhoUpper.le hzero
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def, Gammaℝ_eq_zero_iff] at hgamma
    obtain ⟨n, hn⟩ := hgamma
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    by_cases hnzero : n = 0
    · subst n
      norm_num at hre
      linarith
    · have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnzero
      linarith
  · rw [hodd.gammaFactor_def, Gammaℝ_eq_zero_iff] at hgamma
    obtain ⟨n, hn⟩ := hgamma
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- A primitive ordinary Dirichlet L-function has no shallow left-strip zero
except the origin of an even nonprincipal character. -/
theorem
    primitive_LFunction_eq_zero_iff_origin_of_neg_half_lt_re_of_re_nonpos
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {rho : ℂ} (hleft : -(1 / 2 : ℝ) < rho.re)
    (hright : rho.re ≤ 0) :
    DirichletCharacter.LFunction chi rho = 0 ↔
      rho = 0 ∧ chi ≠ 1 ∧ chi.Even := by
  constructor
  · intro hzero
    have hgamma := primitive_LFunction_zero_forces_gammaFactor_zero
      chi hchi hright hzero
    rcases chi.even_or_odd with heven | hodd
    · have hrho : rho = 0 := by
        rw [heven.gammaFactor_def, Gammaℝ_eq_zero_iff] at hgamma
        obtain ⟨n, hn⟩ := hgamma
        by_cases hnzero : n = 0
        · subst n
          simpa using hn
        · have hnOne : (1 : ℝ) ≤ n := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnzero)
          have hre := congrArg Complex.re hn
          norm_num at hre
          have hrhoLe : rho.re ≤ -2 := by
            rw [hre]
            linarith [hnOne]
          linarith
      refine ⟨hrho, ?_, heven⟩
      intro hchiOne
      have hconductorOne : chi.conductor = 1 :=
        DirichletCharacter.eq_one_iff_conductor_eq_one.mp hchiOne
      have hconductorLevel : chi.conductor = q := hchi
      have hq : q = 1 := hconductorLevel.symm.trans hconductorOne
      subst q
      rw [hrho, DirichletCharacter.LFunction_modOne_eq,
        riemannZeta_zero] at hzero
      norm_num at hzero
    · rw [hodd.gammaFactor_def, Gammaℝ_eq_zero_iff] at hgamma
      obtain ⟨n, hn⟩ := hgamma
      have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hre := congrArg Complex.re hn
      norm_num at hre
      linarith
  · rintro ⟨rfl, hchi, heven⟩
    have hq : q ≠ 1 := fun hq => hchi (chi.level_one' hq)
    change ZMod.LFunction chi 0 = 0
    rw [ZMod.LFunction_apply_zero_of_even heven.to_fun, chi.map_zero' hq,
      neg_zero, zero_div]

/-- The origin zero of a primitive even nonprincipal character is simple. -/
theorem analyticOrderNatAt_LFunction_zero_eq_one_of_isPrimitive_even
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (heven : chi.Even) :
    analyticOrderNatAt (DirichletCharacter.LFunction chi) 0 = 1 := by
  let L : ℂ → ℂ := DirichletCharacter.LFunction chi
  let A : ℂ → ℂ := fun s =>
    (q : ℂ) ^ ((1 - s) - 1 / 2) *
      DirichletCharacter.rootNumber chi *
        DirichletCharacter.completedLFunction chi⁻¹ (1 - s)
  have hqne : q ≠ 1 := Nat.ne_of_gt hq
  have hchiNe : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hinvNe : chi⁻¹ ≠ 1 := inv_ne_one.mpr hchiNe
  have hqzero : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hroot : DirichletCharacter.rootNumber chi ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_rootNumber_of_isPrimitive chi hchi]
    exact one_ne_zero
  have hcompletedOne :
      DirichletCharacter.completedLFunction chi⁻¹ 1 ≠ 0 := by
    intro hzero
    have hrelation :=
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor
        chi⁻¹ 1 (.inr hqne)
    rw [hzero, zero_div] at hrelation
    exact (DirichletCharacter.LFunction_apply_one_ne_zero hinvNe) hrelation
  have hAZero : A 0 ≠ 0 := by
    dsimp only [A]
    simpa using
      (mul_ne_zero
        (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl hqzero)) hroot)
        hcompletedOne)
  have hAContinuous : ContinuousAt A 0 := by
    have hpow : ContinuousAt
        (fun s : ℂ => (q : ℂ) ^ ((1 - s) - 1 / 2)) 0 :=
      (by
        change ContinuousAt
          ((fun z : ℂ => (q : ℂ) ^ z) ∘
            (fun s : ℂ => (1 - s) - 1 / 2)) 0
        exact (continuousAt_const_cpow hqzero).comp (by fun_prop))
    have hcompleted : ContinuousAt
        (fun s : ℂ =>
          DirichletCharacter.completedLFunction chi⁻¹ (1 - s)) 0 :=
      (by
        change ContinuousAt
          (DirichletCharacter.completedLFunction chi⁻¹ ∘
            (fun s : ℂ => 1 - s)) 0
        exact
          ((DirichletCharacter.differentiable_completedLFunction hinvNe).continuous
            |>.continuousAt).comp (by fun_prop))
    exact (hpow.mul continuousAt_const).mul hcompleted
  have hLZero : L 0 = 0 := by
    change ZMod.LFunction chi 0 = 0
    rw [ZMod.LFunction_apply_zero_of_even heven.to_fun, chi.map_zero' hqne,
      neg_zero, zero_div]
  have hratio : Tendsto (fun s => A s / (s * Gammaℝ s))
      (nhdsWithin 0 {0}ᶜ) (nhds (A 0 / 2)) :=
    (hAContinuous.tendsto.mono_left nhdsWithin_le_nhds).div
      Gammaℝ_residue_zero two_ne_zero
  have hslope : Tendsto
      (fun t : ℂ => t⁻¹ • (L (0 + t) - L 0))
      (nhdsWithin 0 {0}ᶜ) (nhds (A 0 / 2)) := by
    apply hratio.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htZero : t ≠ 0 := by simpa using ht
    have hcompleted :
        DirichletCharacter.completedLFunction chi t = A t := by
      have hfun := hchi.completedLFunction_one_sub (1 - t)
      rw [show 1 - (1 - t) = t by ring] at hfun
      simpa only [A] using hfun
    rw [zero_add, hLZero, sub_zero, smul_eq_mul]
    change A t / (t * Gammaℝ t) = t⁻¹ * L t
    rw [show L t = DirichletCharacter.LFunction chi t by rfl,
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor
        chi t (.inr hqne), heven.gammaFactor_def, hcompleted]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hderiv : HasDerivAt L (A 0 / 2) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr hslope
  have hLAnalytic : AnalyticAt ℂ L 0 :=
    (DirichletCharacter.differentiable_LFunction hchiNe).analyticAt 0
  have horder : analyticOrderAt L 0 = 1 :=
    hLAnalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hLZero (by
      rw [hderiv.deriv]
      exact div_ne_zero hAZero two_ne_zero)
  change (analyticOrderAt L 0).toNat = 1
  rw [horder]
  rfl

end BoundedGaps.Maynard
