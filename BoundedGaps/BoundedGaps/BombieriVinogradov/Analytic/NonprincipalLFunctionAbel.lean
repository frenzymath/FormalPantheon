import BoundedGaps.BombieriVinogradov.Analytic.CharacterPartialSummation
import BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionAbelContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Abel continuation and the ordered value at one

This file specializes the bounded-prefix Abel continuation to every
nonprincipal character and identifies the natural reciprocal prefixes with
the analytic value `L(1, chi)`. The series is conditionally convergent, so the
statement deliberately uses finite prefixes and `Tendsto`, not an
unconditional infinite-sum interface. Semantic review: `SEM-544`.
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

/-- The Abel integral for every nonprincipal character on the positive
half-plane, using the all-nonprincipal Polya--Vinogradov prefix bound. -/
theorem LFunction_eq_abelIntegral_of_ne_one
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)) := by
  simpa [dirichletCharacterIntervalSum] using
    LFunction_eq_abelIntegral_of_prefixBound chi hchi
      (2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
      (fun n ↦ by
        simpa [dirichletCharacterIntervalSum] using
          norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
            hq chi hchi n)
      s hs

private theorem tendsto_reciprocalPrefix_of_abelIntegral
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤ C)
    (habel : DirichletCharacter.LFunction chi (1 : ℂ) =
      (1 : ℂ) * ∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-((1 : ℂ) + 1))) :
    Tendsto (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
      chi (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let c : ℕ → ℂ := fun n ↦ chi (n : ZMod q)
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(1 : ℂ))
  have hc0 : c 0 = 0 := by
    simpa [c] using chi.map_zero' (Nat.ne_of_gt hq)
  have hCumulative (n : ℕ) :
      ∑ k ∈ Finset.Icc 0 n, c k =
        dirichletCharacterIntervalSum 1 n q chi := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [c, dirichletCharacterIntervalSum]
  have hfDiff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      (zero_lt_one.trans_le ht).ne' (by norm_num)
  have hfInt : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by norm_num))).locallyIntegrableOn
  have hEndpoint : Tendsto
      (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun n : ℕ ↦ C / (n : ℝ))
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      rw [hCumulative, norm_mul]
      have hfn : ‖f n‖ = (n : ℝ)⁻¹ := by
        change ‖(n : ℂ) ^ (-(1 : ℂ))‖ = (n : ℝ)⁻¹
        rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      rw [hfn]
      calc
        (n : ℝ)⁻¹ *
            ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤
            (n : ℝ)⁻¹ * C :=
          mul_le_mul_of_nonneg_left (hprefix n)
            (inv_nonneg.mpr (by positivity))
        _ = C / (n : ℝ) := by ring
    · simpa [div_eq_mul_inv] using
        ((tendsto_const_nhds (x := C)).mul
          (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hDom :
      (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        (fun t : ℝ ↦ t ^ (-2 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [norm_mul, hCumulative]
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hderiv : ‖deriv f t‖ = t ^ (-2 : ℝ) := by
      rw [show deriv f t =
          deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
        deriv_ofReal_cpow_const ht0.ne' (by norm_num), norm_mul,
        norm_neg, norm_one, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      norm_num
    rw [hderiv]
    have hgNonneg : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    calc
      t ^ (-2 : ℝ) *
          ‖dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi‖ ≤
          t ^ (-2 : ℝ) * C :=
        mul_le_mul_of_nonneg_left (hprefix _) hgNonneg
      _ = C * ‖t ^ (-2 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hgNonneg]
        ring
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (f := f) (l := 0) c hc0 hfDiff hfInt hEndpoint hDom
      (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))
  have hleft (n : ℕ) :
      (∑ k ∈ Finset.Icc 0 n, f k * c k) =
        ∑ k ∈ Finset.Icc 1 n,
          chi (k : ZMod q) / (k : ℂ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      mul_zero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [f, c, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]
  have hright :
      0 - ∫ t in Ioi (1 : ℝ),
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
        DirichletCharacter.LFunction chi (1 : ℂ) := by
    rw [habel, one_mul, zero_sub, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -(deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = _
    rw [show deriv f t =
        deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
      deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (by norm_num),
      hCumulative]
    ring_nf
  rw [← hright]
  exact hconv.congr' (Eventually.of_forall hleft)

/-- The natural reciprocal prefixes of a nonprincipal character converge to
the analytic value `L(1, chi)`. This is conditional, ordered convergence. -/
theorem tendsto_dirichletCharacterReciprocalPrefix_atTop
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    Tendsto
      (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  apply tendsto_reciprocalPrefix_of_abelIntegral hq chi C
  · intro n
    simpa [C] using
      norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
        hq chi hchi n
  · exact LFunction_eq_abelIntegral_of_ne_one
      hq chi hchi (1 : ℂ) (by norm_num)

/-- The factor-four quantitative remainder for the naturally ordered value
`L(1, chi)`. -/
theorem norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x : ℕ) (hx : 0 < x) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 x,
          chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  let P : ℕ → ℂ := fun y ↦ ∑ n ∈ Finset.Icc 1 y,
    chi (n : ZMod q) / (n : ℂ)
  have htail {y : ℕ} (hxy : x ≤ y) :
      P y - P x = ∑ n ∈ Finset.Ioc x y,
        chi (n : ZMod q) / (n : ℂ) := by
    have hunion : Finset.Icc 1 x ∪ Finset.Ioc x y =
        Finset.Icc 1 y := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro (hn | hn) <;> omega
      · intro hn
        by_cases hnx : n ≤ x
        · exact Or.inl ⟨hn.1, hnx⟩
        · exact Or.inr ⟨lt_of_not_ge hnx, hn.2⟩
    have hdis : Disjoint (Finset.Icc 1 x) (Finset.Ioc x y) := by
      rw [Finset.disjoint_left]
      intro n hncc hnoc
      simp only [Finset.mem_Icc] at hncc
      simp only [Finset.mem_Ioc] at hnoc
      omega
    change (∑ n ∈ Finset.Icc 1 y,
        chi (n : ZMod q) / (n : ℂ)) -
      (∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ)) = _
    rw [← hunion, Finset.sum_union hdis]
    ring
  have hconv :=
    tendsto_dirichletCharacterReciprocalPrefix_atTop hq chi hchi
  have hlim : Tendsto (fun y ↦ ‖P y - P x‖) atTop
      (𝓝 ‖DirichletCharacter.LFunction chi (1 : ℂ) - P x‖) := by
    exact (hconv.sub_const (P x)).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hxy
  rw [htail hxy]
  exact norm_dirichletCharacterReciprocalIntervalSum_le
    hq chi hchi x y hx

end BoundedGaps.Maynard
