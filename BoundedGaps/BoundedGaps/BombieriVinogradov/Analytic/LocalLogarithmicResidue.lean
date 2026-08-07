import BoundedGaps.BombieriVinogradov.Analytic.DirichletLZeroDivisor
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Local logarithmic residues

A finite-order analytic germ factors as `(z - rho) ^ m * g z`, where `g` is
analytic and nonzero at `rho`. On a deleted neighborhood this gives the exact
logarithmic-derivative term `m / (z - rho)`, and its logarithmic residue is
`m`. The final declarations specialize these facts to Mathlib's ordinary
continued Dirichlet L-function.

This is a qualitative local result. It neither constructs a zero sum nor
proves a conductor/height-uniform remainder.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 114,
Lemma 11.4(b), for the positive zero-term sign and multiplicity convention;
`ElkiesM229PNTAP2018`, p. 1, equations (2)--(3), and
`ElkiesM229NearlyZeroFree2018`, p. 2. Semantic review: `SEM-471`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped Topology

private theorem logDeriv_sub_pow_mul
    {rho z : ℂ} {g : ℂ -> ℂ} (m : ℕ)
    (hz : z ≠ rho) (hg0 : g z ≠ 0) (hg : DifferentiableAt ℂ g z) :
    logDeriv (fun w : ℂ => (w - rho) ^ m * g w) z =
      (m : ℂ) / (z - rho) + logDeriv g z := by
  rw [logDeriv_mul (f := fun w : ℂ => (w - rho) ^ m) (g := g) z
    (pow_ne_zero m (sub_ne_zero.mpr hz)) hg0 (by fun_prop) hg]
  rw [show (fun w : ℂ => (w - rho) ^ m) =
    Function.comp (fun w => w ^ m) (fun w => w - rho) by rfl]
  rw [logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
  simp only [deriv_sub_const, deriv_id'', mul_one]

/-- The local logarithmic derivative of a finite-order analytic germ is its
order term plus a regular logarithmic derivative. -/
theorem AnalyticAt.exists_eventually_logDeriv_eq_order_div_add
    {f : ℂ -> ℂ} {rho : ℂ} (hf : AnalyticAt ℂ f rho)
    (hfinite : analyticOrderAt f rho ≠ ⊤) :
    ∃ g : ℂ -> ℂ,
      AnalyticAt ℂ g rho ∧ g rho ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] rho,
        logDeriv f z =
          (analyticOrderNatAt f rho : ℂ) / (z - rho) + logDeriv g z := by
  obtain ⟨g, hg, hg0, hfactor⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  have hfactor' :
      f =ᶠ[𝓝 rho] fun z =>
        (z - rho) ^ analyticOrderNatAt f rho * g z := by
    simpa [smul_eq_mul] using hfactor
  have hderiv := hfactor'.deriv
  have hg_ne : ∀ᶠ z in 𝓝 rho, g z ≠ 0 :=
    hg.continuousAt.eventually_ne hg0
  have hg_diff : ∀ᶠ z in 𝓝 rho, DifferentiableAt ℂ g z :=
    hg.eventually_analyticAt.mono fun _ h => h.differentiableAt
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [hfactor'.filter_mono nhdsWithin_le_nhds,
    hderiv.filter_mono nhdsWithin_le_nhds,
    hg_ne.filter_mono nhdsWithin_le_nhds,
    hg_diff.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z hvalue hderiv hgne hgdiff hz
  rw [logDeriv_apply, hderiv, hvalue, ← logDeriv_apply]
  exact logDeriv_sub_pow_mul _ (by simpa using hz) hgne hgdiff

/-- The logarithmic residue of a finite-order analytic germ is its natural
analytic order. -/
theorem AnalyticAt.tendsto_sub_mul_logDeriv
    {f : ℂ -> ℂ} {rho : ℂ} (hf : AnalyticAt ℂ f rho)
    (hfinite : analyticOrderAt f rho ≠ ⊤) :
    Tendsto (fun z => (z - rho) * logDeriv f z) (𝓝[≠] rho)
      (𝓝 (analyticOrderNatAt f rho : ℂ)) := by
  obtain ⟨g, hg, hg0, hexpansion⟩ :=
    BoundedGaps.Maynard.AnalyticAt.exists_eventually_logDeriv_eq_order_div_add
      hf hfinite
  have hlog : ContinuousAt (logDeriv g) rho :=
    hg.deriv.continuousAt.div hg.continuousAt hg0
  have hsub : Tendsto (fun z : ℂ => z - rho) (𝓝[≠] rho) (𝓝 0) := by
    have h :=
      (show ContinuousAt (fun z : ℂ => z - rho) rho by fun_prop).tendsto
        |>.mono_left (show 𝓝[≠] rho ≤ 𝓝 rho from nhdsWithin_le_nhds)
    simpa using h
  have hrem :
      Tendsto (fun z => (z - rho) * logDeriv g z) (𝓝[≠] rho) (𝓝 0) := by
    simpa using hsub.mul (hlog.tendsto.mono_left nhdsWithin_le_nhds)
  apply Tendsto.congr'
    (hexpansion.and self_mem_nhdsWithin |>.mono fun z hz => by
      have hne : z - rho ≠ 0 := sub_ne_zero.mpr (by simpa using hz.2)
      rw [hz.1, mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ hne])
  simpa using tendsto_const_nhds.add hrem

private theorem analyticOnNhd_LFunction_of_nontrivial
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N} (hchi : chi ≠ 1) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi) Set.univ :=
  fun z _ => (DirichletCharacter.differentiable_LFunction hchi).analyticAt z

private theorem analyticOrderAt_LFunction_ne_top
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ≠ 1) (rho : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction chi) rho ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho
    (fun z => analyticOnNhd_LFunction_of_nontrivial hchi z (Set.mem_univ z))]
  intro hzero
  have htwo : DirichletCharacter.LFunction chi (2 : ℂ) = 0 := by
    rw [hzero]
    rfl
  have htwo_ne : DirichletCharacter.LFunction chi (2 : ℂ) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi (by norm_num)]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi (by norm_num)
  exact htwo_ne htwo

private theorem analyticOrderNatAt_LFunction_pos_of_zero
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ≠ 1) {rho : ℂ}
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    0 < analyticOrderNatAt (DirichletCharacter.LFunction chi) rho := by
  have hdiv := one_le_divisor_LFunction_of_zero
    (U := Set.univ) (s := rho) hchi (Set.mem_univ rho) hzero
  rw [divisor_LFunction_apply_eq_analyticOrderNatAt
    hchi (Set.mem_univ rho)] at hdiv
  exact_mod_cast hdiv

/-- At an ordinary zero of a nontrivial Dirichlet L-function, the local order
is positive and is the coefficient of its logarithmic-derivative pole. -/
theorem LFunction_zero_local_logDeriv_expansion
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ≠ 1) {rho : ℂ}
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    0 < analyticOrderNatAt (DirichletCharacter.LFunction chi) rho ∧
      ∃ g : ℂ -> ℂ,
        AnalyticAt ℂ g rho ∧ g rho ≠ 0 ∧
        ∀ᶠ z in 𝓝[≠] rho,
          logDeriv (DirichletCharacter.LFunction chi) z =
            (analyticOrderNatAt
              (DirichletCharacter.LFunction chi) rho : ℂ) / (z - rho) +
              logDeriv g z := by
  refine ⟨analyticOrderNatAt_LFunction_pos_of_zero hchi hzero, ?_⟩
  exact
    BoundedGaps.Maynard.AnalyticAt.exists_eventually_logDeriv_eq_order_div_add
      ((DirichletCharacter.differentiable_LFunction hchi).analyticAt rho)
      (analyticOrderAt_LFunction_ne_top hchi rho)

/-- The logarithmic residue of a nontrivial ordinary Dirichlet L-function at
any point is its natural analytic order there. -/
theorem tendsto_sub_mul_logDeriv_LFunction
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ≠ 1) (rho : ℂ) :
    Tendsto
      (fun z => (z - rho) *
        logDeriv (DirichletCharacter.LFunction chi) z)
      (𝓝[≠] rho)
      (𝓝 (analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho : ℂ)) :=
  BoundedGaps.Maynard.AnalyticAt.tendsto_sub_mul_logDeriv
    ((DirichletCharacter.differentiable_LFunction hchi).analyticAt rho)
    (analyticOrderAt_LFunction_ne_top hchi rho)

end BoundedGaps.Maynard
