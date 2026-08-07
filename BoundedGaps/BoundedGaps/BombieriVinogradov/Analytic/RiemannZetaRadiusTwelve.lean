import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusFour

/-!
# Regularized zeta on radius-twelve spheres

This file supplies the boundary growth needed to apply the fixed-disk
logarithmic-derivative theorem with radii `3`, `6`, and `12`. The right half-
plane uses the Abel representation of `riemannZeta₁`; the left half-plane uses
its reflection identity after a separate compact neighborhood of zero.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 55,
equation (5.7), printed p. 62, equations (6.1)--(6.2), printed pp. 66--67,
and printed pp. 89--92, Lemmas 8.5--8.6. Semantic review: `SEM-529`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

private lemma radiusTwelveRiemannZetaSphere_geometry
    (t : ℝ) (z : ℂ)
    (hz : z ∈ sphere ((2 : ℂ) + t * I) 12) :
    -(10 : ℝ) ≤ z.re ∧ z.re ≤ 14 ∧
      |z.im| + 2 ≤ 7 * (|t| + 2) ∧
        ‖z‖ ≤ 7 * (|t| + 2) := by
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
  have hzIm : |z.im| ≤ |t| + 12 := by
    calc
      |z.im| = |(z.im - t) + t| := by rw [sub_add_cancel]
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ 12 + |t| := by linarith
      _ = |t| + 12 := by ring
  have hcenter : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
    calc
      ‖(2 : ℂ) + t * I‖ ≤ ‖(2 : ℂ)‖ + ‖t * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp [Real.norm_eq_abs]
  have hnorm : ‖z‖ ≤ |t| + 14 := by
    calc
      ‖z‖ = ‖(z - ((2 : ℂ) + t * I)) + ((2 : ℂ) + t * I)‖ := by ring_nf
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ + ‖(2 : ℂ) + t * I‖ :=
        norm_add_le _ _
      _ ≤ 12 + (2 + |t|) := add_le_add (le_of_eq hdist) hcenter
      _ = |t| + 14 := by ring
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · linarith [abs_nonneg t]
  · linarith [abs_nonneg t]

private lemma exists_pos_norm_riemannZeta₁_closedBall_one_le_radiusTwelve :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖riemannZeta₁ z‖ ≤ C := by
  have hball : IsCompact (closedBall (0 : ℂ) 1) :=
    isCompact_closedBall (0 : ℂ) 1
  obtain ⟨C, hC⟩ := hball.exists_bound_of_continuousOn
    differentiable_riemannZeta₁.continuous.continuousOn
  refine ⟨max C 0 + 1, by linarith [le_max_right C 0], ?_⟩
  intro z hz
  exact (hC z hz).trans (by linarith [le_max_left C 0])

private lemma natCast_le_two_pow_radiusTwelve (n : ℕ) :
    (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith

/-- Regularized zeta has an absolute polynomial bound on every radius-twelve
sphere centered at `2 + t * I`. -/
theorem exists_nat_norm_riemannZeta₁_radiusTwelveSphere_le :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ (t : ℝ) (z : ℂ),
        z ∈ sphere ((2 : ℂ) + t * I) 12 →
          ‖riemannZeta₁ z‖ ≤ (|t| + 2) ^ E := by
  obtain ⟨Ccompact, _hCcompact, hcompact⟩ :=
    exists_pos_norm_riemannZeta₁_closedBall_one_le_radiusTwelve
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_gammaFactor_ratio_fixedStrip_le
  let K : ℝ := max Ccompact (8 * Cgamma * 7 ^ 11)
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge K
  refine ⟨n + 21, by omega, ?_⟩
  intro t z hz
  obtain ⟨hzlo, _hzhi, hzheight, hznorm⟩ :=
    radiusTwelveRiemannZetaSphere_geometry t z hz
  let T : ℝ := |t| + 2
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ T := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hzsub : ‖z - 1‖ ≤ 8 * T := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 7 * T + 1 := add_le_add (by simpa [T] using hznorm) (by norm_num)
      _ ≤ 8 * T := by linarith
  have hKpow : K ≤ T ^ n := by
    calc
      K ≤ (n : ℝ) := hn
      _ ≤ 2 ^ n := natCast_le_two_pow_radiusTwelve n
      _ ≤ T ^ n := pow_le_pow_left₀ (by norm_num) hT2 n
  have h120 : (120 : ℝ) ≤ T ^ 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 7
    norm_num at h ⊢
    linarith
  by_cases hright : (1 / 2 : ℝ) ≤ z.re
  · have habel := norm_riemannZeta₁_le_abel z (by linarith)
    have hrightBound : ‖riemannZeta₁ z‖ ≤ T ^ 9 := by
      calc
        ‖riemannZeta₁ z‖ ≤ ‖z‖ + ‖z‖ * ‖z - 1‖ / z.re := habel
        _ ≤ 7 * T + (7 * T) * (8 * T) / (1 / 2 : ℝ) := by gcongr
        _ = 7 * T + 112 * T ^ 2 := by ring
        _ ≤ 120 * T ^ 2 := by nlinarith [sq_nonneg T]
        _ ≤ T ^ 7 * T ^ 2 :=
          mul_le_mul_of_nonneg_right h120 (sq_nonneg T)
        _ = T ^ 9 := by ring
    exact hrightBound.trans (pow_le_pow_right₀ hT1 (by omega))
  · have hzleft : z.re ≤ (1 / 2 : ℝ) := le_of_not_ge hright
    by_cases hzsmall : ‖z‖ ≤ 1
    · have hzball : z ∈ closedBall (0 : ℂ) 1 := by
        simpa [mem_closedBall, dist_zero_right] using hzsmall
      calc
        ‖riemannZeta₁ z‖ ≤ Ccompact := hcompact z hzball
        _ ≤ K := le_max_left _ _
        _ ≤ T ^ n := hKpow
        _ ≤ T ^ (n + 21) := pow_le_pow_right₀ hT1 (by omega)
    · have hz0 : z ≠ 0 := by
        intro h
        subst z
        simp at hzsmall
      have hreflect := riemannZeta₁_eq_reflection_of_re_le z hz0 hzleft
      have hreflectNorm : ‖1 - z‖ ≤ 8 * T := by
        rw [show 1 - z = -(z - 1) by ring, norm_neg]
        exact hzsub
      have hreflectSub : ‖(1 - z) - 1‖ ≤ 7 * T := by
        simpa only [sub_sub_cancel_left, norm_neg] using
          (show ‖z‖ ≤ 7 * T by simpa [T] using hznorm)
      have hreflectAbel :=
        norm_riemannZeta₁_le_abel (1 - z) (by simp; linarith)
      have hreflectBound : ‖riemannZeta₁ (1 - z)‖ ≤ T ^ 9 := by
        calc
          ‖riemannZeta₁ (1 - z)‖ ≤
              ‖1 - z‖ + ‖1 - z‖ * ‖(1 - z) - 1‖ / (1 - z).re :=
            hreflectAbel
          _ ≤ 8 * T + (8 * T) * (7 * T) / (1 / 2 : ℝ) := by
            gcongr
            · simp
              linarith
          _ = 8 * T + 112 * T ^ 2 := by ring
          _ ≤ 120 * T ^ 2 := by nlinarith [sq_nonneg T]
          _ ≤ T ^ 7 * T ^ 2 :=
            mul_le_mul_of_nonneg_right h120 (sq_nonneg T)
          _ = T ^ 9 := by ring
      have hratio : ‖(1 - z) / z‖ ≤ 8 * T := by
        rw [norm_div]
        have hzOne : (1 : ℝ) ≤ ‖z‖ := le_of_not_ge hzsmall
        exact (div_le_iff₀ (norm_pos_iff.mpr hz0)).2 (by
          calc
            ‖1 - z‖ ≤ 8 * T := hreflectNorm
            _ ≤ 8 * T * ‖z‖ :=
              le_mul_of_one_le_right (by positivity) hzOne)
      have hgamma' := hgamma 1 (1 : DirichletCharacter ℂ 1) z hzlo hzleft
      have hgammaBound :
          ‖DirichletCharacter.gammaFactor
                (1 : DirichletCharacter ℂ 1)⁻¹ (1 - z) /
              DirichletCharacter.gammaFactor
                (1 : DirichletCharacter ℂ 1) z‖ ≤
            Cgamma * (7 * T) ^ 11 := by
        exact hgamma'.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity)
            (by simpa [T] using hzheight) 11) hCgamma.le)
      have hinvOne : (1 : DirichletCharacter ℂ 1)⁻¹ = 1 := inv_one
      rw [hinvOne] at hgammaBound
      rw [hreflect, norm_mul, norm_mul]
      calc
        ‖(1 - z) / z‖ * ‖riemannZeta₁ (1 - z)‖ *
              ‖DirichletCharacter.gammaFactor
                    (1 : DirichletCharacter ℂ 1) (1 - z) /
                DirichletCharacter.gammaFactor
                    (1 : DirichletCharacter ℂ 1) z‖ ≤
            (8 * T) * T ^ 9 * (Cgamma * (7 * T) ^ 11) := by gcongr
        _ = (8 * Cgamma * 7 ^ 11) * T ^ 21 := by ring
        _ ≤ K * T ^ 21 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hT0 21)
        _ ≤ T ^ n * T ^ 21 :=
          mul_le_mul_of_nonneg_right hKpow (pow_nonneg hT0 21)
        _ = T ^ (n + 21) := by rw [pow_add]

/-- The radius-twelve absolute bound made relative to the nonzero far-right
center. -/
theorem exists_nat_norm_riemannZeta₁_radiusTwelveSphere_le_exp_mul_center :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (t : ℝ) (z : ℂ),
        z ∈ sphere ((2 : ℂ) + t * I) 12 →
          ‖riemannZeta₁ z‖ ≤
            Real.exp ((A : ℝ) * Real.log (|t| + 2)) *
              ‖riemannZeta₁ ((2 : ℂ) + t * I)‖ := by
  obtain ⟨E, _hE, habsolute⟩ :=
    exists_nat_norm_riemannZeta₁_radiusTwelveSphere_le
  let A := max 37 (E + 2)
  refine ⟨A, Nat.le_max_left 37 (E + 2), ?_⟩
  intro t z hz
  let c : ℂ := (2 : ℂ) + t * I
  let T : ℝ := |t| + 2
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hTpos : 0 < T := zero_lt_two.trans_le hT2
  have hc1 : c ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [c] at this
  have hzeta : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [c])
  have hcenter : riemannZeta₁ c = (c - 1) * riemannZeta c := by
    rw [riemannZeta_eq_inv_sub_mul hc1]
    field_simp
  have hcsubNorm : (1 : ℝ) ≤ ‖c - 1‖ := by
    rw [show c - 1 = (1 : ℂ) + t * I by dsimp [c]; ring]
    simpa using Complex.abs_re_le_norm ((1 : ℂ) + t * I)
  have hcsubInv : ‖(c - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hc1)) |>.2 hcsubNorm
  have hzetaInv : ‖(riemannZeta c)⁻¹‖ ≤ 3 := by
    have h := norm_inv_LFunction_two_add_mul_I_le_three
      (1 : DirichletCharacter ℂ 1) t
    simpa [DirichletCharacter.LFunction_modOne_eq, c] using h
  have hcenterInv : ‖(riemannZeta₁ c)⁻¹‖ ≤ 3 := by
    rw [hcenter, mul_inv_rev, norm_mul]
    nlinarith [mul_le_mul hcsubInv hzetaInv (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)]
  have hcenterNe : riemannZeta₁ c ≠ 0 := by
    rw [hcenter]
    exact mul_ne_zero (sub_ne_zero.mpr hc1) hzeta
  have honeCenter : (1 : ℝ) ≤ 3 * ‖riemannZeta₁ c‖ := by
    calc
      (1 : ℝ) = ‖(riemannZeta₁ c)⁻¹ * riemannZeta₁ c‖ := by
        rw [inv_mul_cancel₀ hcenterNe, norm_one]
      _ = ‖(riemannZeta₁ c)⁻¹‖ * ‖riemannZeta₁ c‖ := norm_mul _ _
      _ ≤ 3 * ‖riemannZeta₁ c‖ :=
        mul_le_mul_of_nonneg_right hcenterInv (norm_nonneg _)
  have hTcenter : (1 : ℝ) ≤ T ^ 2 * ‖riemannZeta₁ c‖ := by
    exact honeCenter.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [sq_nonneg T]) (norm_nonneg _))
  have habs : ‖riemannZeta₁ z‖ ≤ T ^ E := by
    simpa [T, c] using habsolute t z (by simpa [c] using hz)
  have hEA : E + 2 ≤ A := Nat.le_max_right 37 (E + 2)
  have hpowEA : T ^ (E + 2) ≤ T ^ A :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ T) hEA
  have hexp : Real.exp ((A : ℝ) * Real.log T) = T ^ A := by
    rw [Real.exp_nat_mul, Real.exp_log hTpos]
  calc
    ‖riemannZeta₁ z‖ ≤ T ^ E := habs
    _ = T ^ E * 1 := by ring
    _ ≤ T ^ E * (T ^ 2 * ‖riemannZeta₁ c‖) :=
      mul_le_mul_of_nonneg_left hTcenter (pow_nonneg hTpos.le E)
    _ = T ^ (E + 2) * ‖riemannZeta₁ c‖ := by rw [pow_add]; ring
    _ ≤ T ^ A * ‖riemannZeta₁ c‖ :=
      mul_le_mul_of_nonneg_right hpowEA (norm_nonneg _)
    _ = Real.exp ((A : ℝ) * Real.log T) * ‖riemannZeta₁ c‖ := by rw [hexp]
    _ = Real.exp ((A : ℝ) * Real.log (|t| + 2)) *
        ‖riemannZeta₁ ((2 : ℂ) + t * I)‖ := rfl

end

end BoundedGaps.Maynard
