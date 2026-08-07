import BoundedGaps.BombieriVinogradov.Analytic.FarRightLFunctionCenter
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionCentralStrip
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionFixedStrip

/-!
# Primitive Dirichlet L-functions on radius-twelve spheres

This file turns fixed-strip polynomial growth into the relative boundary
growth used by the fixed-disk logarithmic-derivative argument. The center is
`2+it`, the inner radius is `3`, and the growth sphere has radius `12`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 89--91,
Lemmas 8.5--8.6, and printed p. 114, Lemma 11.4. The natural exponents are
conservative project consequences, not source-printed constants. Semantic
review: `SEM-478`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

private lemma radiusTwelveSphere_geometry
    (t : ℝ) (z : ℂ)
    (hz : z ∈ sphere ((2 : ℂ) + t * I) 12) :
    -(10 : ℝ) ≤ z.re ∧ z.re ≤ 14 ∧
      |z.im| + 2 ≤ 7 * (|t| + 2) := by
  have hdist : ‖z - ((2 : ℂ) + t * I)‖ = 12 := by
    simpa [mem_sphere, Complex.dist_eq] using hz
  have hre : |z.re - 2| ≤ 12 := by
    calc
      |z.re - 2| = |(z - ((2 : ℂ) + t * I)).re| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_re_le_norm _
      _ = 12 := hdist
  have him : |z.im - t| ≤ 12 := by
    calc
      |z.im - t| = |(z - ((2 : ℂ) + t * I)).im| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_im_le_norm _
      _ = 12 := hdist
  have hz_im : |z.im| ≤ |t| + 12 := by
    have hadd := abs_add_le (z.im - t) t
    rw [sub_add_cancel] at hadd
    linarith
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · rw [abs_le] at hre
    linarith
  · linarith [abs_nonneg t]

/-- Primitive Dirichlet L-functions have one absolute polynomial bound on
the radius-twelve spheres used by the fixed-disk argument. -/
theorem exists_nat_norm_LFunction_radiusTwelveSphere_le :
    ∃ E : ℕ, 36 ≤ E ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t : ℝ) (z : ℂ),
            z ∈ sphere ((2 : ℂ) + t * I) 12 →
              ‖DirichletCharacter.LFunction chi z‖ ≤
                ((q : ℝ) * (|t| + 2)) ^ E := by
  obtain ⟨A, hA, hstrip⟩ := exists_norm_LFunction_fixedStrip_le_pow
  refine ⟨3 * A, by omega, ?_⟩
  intro q _ hq chi hchi t z hz
  obtain ⟨hzlo, _hzhi, hzheight⟩ := radiusTwelveSphere_geometry t z hz
  let B : ℝ := (q : ℝ) * (|t| + 2)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hT2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ |t| + 2 := one_le_two.trans hT2
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB0 : (0 : ℝ) ≤ B := zero_le_one.trans hB1
  have hqB : (q : ℝ) ≤ B := by
    calc
      (q : ℝ) = (q : ℝ) * 1 := by ring
      _ ≤ (q : ℝ) * (|t| + 2) :=
        mul_le_mul_of_nonneg_left hT1 hq0
      _ = B := rfl
  by_cases hleft : z.re ≤ (1 / 2 : ℝ)
  · have hzT0 : (0 : ℝ) ≤ |z.im| + 2 := by positivity
    have hlocal : (q : ℝ) * (|z.im| + 2) ≤ B ^ 3 := by
      calc
        (q : ℝ) * (|z.im| + 2) ≤
            (q : ℝ) * (7 * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left hzheight hq0
        _ = 7 * B := by simp [B]; ring
        _ ≤ B ^ 2 * B := by
          apply mul_le_mul_of_nonneg_right _ hB0
          nlinarith [sq_nonneg B]
        _ = B ^ 3 := by ring
    calc
      ‖DirichletCharacter.LFunction chi z‖ ≤
          ((q : ℝ) * (|z.im| + 2)) ^ A :=
        hstrip q hq chi hchi z hzlo hleft
      _ ≤ (B ^ 3) ^ A :=
        pow_le_pow_left₀ (mul_nonneg hq0 hzT0) hlocal A
      _ = B ^ (3 * A) := by rw [pow_mul]
  · have hhalf : (1 / 2 : ℝ) ≤ z.re := le_of_not_ge hleft
    by_cases hcentral : z.re ≤ 2
    · have hcentralBound := norm_LFunction_centralStrip_le hq chi hchi
          (sigma := z.re) (t := z.im) hhalf hcentral
      have hzarg : (((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rw [hzarg] at hcentralBound
      have hsqrt : Real.sqrt (q : ℝ) ≤ q :=
        Real.sqrt_le_self_iff.mpr (Or.inr hq1)
      have hlog : Real.log (q : ℝ) ≤ q :=
        (Real.log_le_sub_one_of_pos hqpos).trans
          (sub_le_self _ zero_le_one)
      have h14 : (14 : ℝ) ≤ B ^ 2 := by
        nlinarith [sq_nonneg B]
      have hcentralPower :
          2 * (|z.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
            B ^ 4 := by
        calc
          2 * (|z.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
              2 * (7 * (|t| + 2)) * (q : ℝ) * (q : ℝ) := by
            gcongr
          _ = 14 * (q : ℝ) * B := by simp [B]; ring
          _ ≤ 14 * B * B := by gcongr
          _ = 14 * B ^ 2 := by ring
          _ ≤ B ^ 2 * B ^ 2 :=
            mul_le_mul_of_nonneg_right h14 (sq_nonneg B)
          _ = B ^ 4 := by ring
      calc
        ‖DirichletCharacter.LFunction chi z‖ ≤
            2 * (|z.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
          hcentralBound
        _ ≤ B ^ 4 := hcentralPower
        _ ≤ B ^ (3 * A) :=
          pow_le_pow_right₀ hB1 (by omega)
    · have hfar : (2 : ℝ) ≤ z.re := le_of_not_ge hcentral
      have hfarBound := norm_LFunction_farRight_le_three chi z hfar
      have hBpow : B ≤ B ^ (3 * A) := by
        calc
          B = B ^ 1 := by simp
          _ ≤ B ^ (3 * A) := pow_le_pow_right₀ hB1 (by omega)
      exact hfarBound.trans (le_trans (by linarith) hBpow)

/-- The radius-twelve absolute bound can be made relative to the nonzero
far-right center with one additional conductor-height power. -/
theorem exists_nat_norm_LFunction_radiusTwelveSphere_le_exp_mul_center :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t : ℝ) (z : ℂ),
            z ∈ sphere ((2 : ℂ) + t * I) 12 →
              ‖DirichletCharacter.LFunction chi z‖ ≤
                Real.exp
                    ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) *
                  ‖DirichletCharacter.LFunction chi ((2 : ℂ) + t * I)‖ := by
  obtain ⟨E, hE, habsolute⟩ :=
    exists_nat_norm_LFunction_radiusTwelveSphere_le
  refine ⟨E + 1, by omega, ?_⟩
  intro q _ hq chi hchi t z hz
  let c : ℂ := (2 : ℂ) + t * I
  let B : ℝ := (q : ℝ) * (|t| + 2)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hT2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hBpos : (0 : ℝ) < B := zero_lt_four.trans_le hB4
  have hc : DirichletCharacter.LFunction chi c ≠ 0 := by
    have hc_re : 1 < c.re := by simp [c]
    rw [DirichletCharacter.LFunction_eq_LSeries chi hc_re]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hc_re
  have hinv : ‖(DirichletCharacter.LFunction chi c)⁻¹‖ ≤ 3 := by
    simpa [c] using norm_inv_LFunction_two_add_mul_I_le_three chi t
  have hone_center :
      (1 : ℝ) ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ := by
    calc
      (1 : ℝ) = ‖(DirichletCharacter.LFunction chi c)⁻¹ *
          DirichletCharacter.LFunction chi c‖ := by
        rw [inv_mul_cancel₀ hc, norm_one]
      _ = ‖(DirichletCharacter.LFunction chi c)⁻¹‖ *
          ‖DirichletCharacter.LFunction chi c‖ := norm_mul _ _
      _ ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ :=
        mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hone_base_center :
      (1 : ℝ) ≤ B * ‖DirichletCharacter.LFunction chi c‖ := by
    exact hone_center.trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have habs : ‖DirichletCharacter.LFunction chi z‖ ≤ B ^ E := by
    simpa [B, c] using habsolute q hq chi hchi t z hz
  have hexp :
      Real.exp (((E + 1 : ℕ) : ℝ) * Real.log B) = B ^ (E + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hBpos]
  calc
    ‖DirichletCharacter.LFunction chi z‖ ≤ B ^ E := habs
    _ = B ^ E * 1 := by ring
    _ ≤ B ^ E * (B * ‖DirichletCharacter.LFunction chi c‖) :=
      mul_le_mul_of_nonneg_left hone_base_center (pow_nonneg hBpos.le E)
    _ = B ^ (E + 1) * ‖DirichletCharacter.LFunction chi c‖ := by
      rw [pow_succ]
      ring
    _ = Real.exp (((E + 1 : ℕ) : ℝ) * Real.log B) *
        ‖DirichletCharacter.LFunction chi c‖ := by rw [hexp]
    _ = Real.exp
          (((E + 1 : ℕ) : ℝ) *
            Real.log ((q : ℝ) * (|t| + 2))) *
        ‖DirichletCharacter.LFunction chi ((2 : ℂ) + t * I)‖ := by
      rfl

end BoundedGaps.Maynard
