import BoundedGaps.BombieriVinogradov.Analytic.DirichletLZeroDivisor
import BoundedGaps.BombieriVinogradov.Analytic.FixedDiskLogDerivative
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionCentralStrip
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionRadiusTwelve

/-!
# Primitive Dirichlet L-functions on a fixed disk

This file specializes the fixed-disk logarithmic-derivative theorem to the
center `2+it` and radii `3`, `6`, and `12`. The selected radius-six divisor is
the ordinary L-function divisor, so it includes trivial zeros when they lie in
the disk.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 90--92,
Lemma 8.6(a) and the proof of Lemma 8.2(b), and printed pp. 112--114,
Lemma 11.4 and its zero conventions. Semantic review: `SEM-479`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

/-- The radius-six ordinary divisor coefficient is the analytic multiplicity
inside the closed disk and zero outside it. -/
theorem divisor_LFunction_radiusSix_apply
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (rho : ℂ) :
    MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
        (closedBall ((2 : ℂ) + t * I) 6) rho =
      ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
          analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
        else 0 : ℕ) : ℤ) := by
  have hchi_ne := character_ne_one_of_isPrimitive hq chi hchi
  by_cases hrho : dist rho ((2 : ℂ) + t * I) ≤ 6
  · rw [if_pos hrho,
      divisor_LFunction_apply_eq_analyticOrderNatAt hchi_ne
        (mem_closedBall.mpr hrho)]
  · rw [if_neg hrho,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _
        (by simpa [mem_closedBall] using hrho)]
    norm_cast

/-- Reindex the radius-six ordinary divisor sum by conditional analytic
multiplicity. -/
theorem finsum_divisor_LFunction_radiusSix_eq
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (s : ℂ) :
    (∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6)) rho : ℂ) / (s - rho)) =
      ∑ᶠ rho : ℂ,
        ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
            analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
          else 0 : ℕ) : ℂ) / (s - rho) := by
  apply finsum_congr
  intro rho
  rw [divisor_LFunction_radiusSix_apply hq chi hchi t rho]
  norm_cast

/-- The primitive Dirichlet specialization of the fixed-disk theorem,
retaining the exact ordinary divisor of the closed radius-six disk. -/
theorem exists_nat_norm_logDeriv_LFunction_sub_radiusSix_divisor_finsum_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t : ℝ) (s : ℂ),
            s ∈ closedBall ((2 : ℂ) + t * I) 3 →
              DirichletCharacter.LFunction chi s ≠ 0 →
                ‖logDeriv (DirichletCharacter.LFunction chi) s -
                    ∑ᶠ rho : ℂ,
                      ((MeromorphicOn.divisor
                        (DirichletCharacter.LFunction chi)
                        (closedBall ((2 : ℂ) + t * I) 6)) rho : ℂ) /
                          (s - rho)‖ ≤
                  16 * ((A : ℝ) *
                    Real.log ((q : ℝ) * (|t| + 2))) / 3 := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_LFunction_radiusTwelveSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t s hs hLs
  let c : ℂ := (2 : ℂ) + t * I
  let B : ℝ := (q : ℝ) * (|t| + 2)
  let M : ℝ := (A : ℝ) * Real.log B
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hT2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hM : 0 ≤ M := by
    exact mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg (by linarith))
  have hchi_ne : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi)
      (closedBall c (4 * (3 : ℝ))) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hchi_ne).analyticAt z
  have hc : DirichletCharacter.LFunction chi c ≠ 0 := by
    have hc_re : 1 < c.re := by simp [c]
    rw [DirichletCharacter.LFunction_eq_LSeries chi hc_re]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hc_re
  have hbound : ∀ z ∈ sphere c (4 * (3 : ℝ)),
      ‖DirichletCharacter.LFunction chi z‖ ≤
        Real.exp M * ‖DirichletCharacter.LFunction chi c‖ := by
    intro z hz
    norm_num at hz
    simpa [c, M, B] using
      hgrowth q hq chi hchi t z (by simpa [c] using hz)
  have hfixed := norm_logDeriv_sub_divisor_finsum_le
    (f := DirichletCharacter.LFunction chi) (c := c) (s := s)
    (R := (3 : ℝ)) (M := M) (by norm_num) hM hf hc hbound
    (by simpa [c] using hs) hLs
  rw [show (2 : ℝ) * 3 = 6 by norm_num] at hfixed
  simpa [c, M, B] using hfixed

/-- The same fixed-disk estimate with each ordinary zero represented by its
conditional analytic multiplicity. -/
theorem exists_nat_norm_logDeriv_LFunction_sub_radiusSix_analyticOrder_finsum_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t : ℝ) (s : ℂ),
            s ∈ closedBall ((2 : ℂ) + t * I) 3 →
              DirichletCharacter.LFunction chi s ≠ 0 →
                ‖logDeriv (DirichletCharacter.LFunction chi) s -
                    ∑ᶠ rho : ℂ,
                      ((if dist rho ((2 : ℂ) + t * I) ≤ 6 then
                          analyticOrderNatAt
                            (DirichletCharacter.LFunction chi) rho
                        else 0 : ℕ) : ℂ) / (s - rho)‖ ≤
                  16 * ((A : ℝ) *
                    Real.log ((q : ℝ) * (|t| + 2))) / 3 := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_nat_norm_logDeriv_LFunction_sub_radiusSix_divisor_finsum_le
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t s hs hLs
  rw [← finsum_divisor_LFunction_radiusSix_eq hq chi hchi t s]
  exact hbound q hq chi hchi t s hs hLs

end

end BoundedGaps.Maynard
