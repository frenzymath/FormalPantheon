import BoundedGaps.BombieriVinogradov.Analytic.FarRightLFunctionCenter
import BoundedGaps.BombieriVinogradov.Analytic.FixedStripGammaRatio
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaAbel
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Regularized zeta growth on radius-four spheres

The fixed-disk argument for the principal pole needs only the strip
`1 <= re(s) <= 2`. We therefore use inner radius one, selected radius two,
and outer radius four around `2+it`. The right half-plane is controlled by
the Abel representation, while the left half-plane uses the completed-zeta
functional equation and the audited Gamma-factor quotient.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 55,
equation (5.7), printed p. 61, equations (6.1)--(6.2), and printed
pp. 89--91, Lemmas 8.5--8.6. Semantic review: `SEM-482`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Metric Set

private lemma even_one_mod_one :
    (1 : DirichletCharacter ℂ 1).Even := by
  rw [DirichletCharacter.Even]
  exact map_one _

/-- The exact regularized-zeta reflection identity on the left half-plane
away from zero. -/
theorem riemannZeta₁_eq_reflection_of_re_le
    (s : ℂ) (hs0 : s ≠ 0) (hs : s.re ≤ (1 / 2 : ℝ)) :
    riemannZeta₁ s =
      (1 - s) / s * riemannZeta₁ (1 - s) *
        (DirichletCharacter.gammaFactor
            (1 : DirichletCharacter ℂ 1) (1 - s) /
          DirichletCharacter.gammaFactor
            (1 : DirichletCharacter ℂ 1) s) := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hreflect0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hGammaReflect : Gammaℝ (1 - s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hGammaR :
      riemannZeta₁ s =
        (1 - s) / s * riemannZeta₁ (1 - s) *
          (Gammaℝ (1 - s) / Gammaℝ s) := by
    by_cases hGamma : Gammaℝ s = 0
    · obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hGamma
      have hn0 : n ≠ 0 := by
        intro hn0
        subst n
        simp at hn
        exact hs0 hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hzeta : riemannZeta (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using
          riemannZeta_neg_two_mul_nat_add_one k
      have harg1 : -(2 * ((k + 1 : ℕ) : ℂ)) ≠ 1 := by
        intro h
        have hreal := congrArg Complex.re h
        norm_num at hreal
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hsub : -(2 * ((k + 1 : ℕ) : ℂ)) - 1 ≠ 0 :=
        sub_ne_zero.mpr harg1
      have hfactor := riemannZeta_eq_inv_sub_mul harg1
      rw [hzeta] at hfactor
      have hinv : (-(2 * ((k + 1 : ℕ) : ℂ)) - 1)⁻¹ ≠ 0 :=
        inv_ne_zero hsub
      have hzeta1 : riemannZeta₁ (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 :=
        (mul_eq_zero.mp hfactor.symm).resolve_left hinv
      have hden : Gammaℝ (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 := by
        simpa [hn] using hGamma
      rw [hn, hzeta1, hden]
      simp
    · have hreflected :
          completedRiemannZeta (1 - s) =
            riemannZeta (1 - s) * Gammaℝ (1 - s) := by
        symm
        exact (eq_div_iff hGammaReflect).mp
          (riemannZeta_def_of_ne_zero hreflect0)
      have hzeta :
          riemannZeta s =
            riemannZeta (1 - s) * Gammaℝ (1 - s) / Gammaℝ s := by
        rw [riemannZeta_def_of_ne_zero hs0,
          ← completedRiemannZeta_one_sub s, hreflected]
      have hreg : riemannZeta₁ s = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul hs1]
        field_simp
      have hreflect1 : 1 - s ≠ 1 := by
        intro h
        apply hs0
        linear_combination -h
      have hregReflect :
          riemannZeta₁ (1 - s) =
            ((1 - s) - 1) * riemannZeta (1 - s) := by
        rw [riemannZeta_eq_inv_sub_mul hreflect1]
        field_simp
      rw [hreg, hzeta, hregReflect]
      field_simp [hs0, hGamma]
      ring
  rw [even_one_mod_one.gammaFactor_def, even_one_mod_one.gammaFactor_def]
  exact hGammaR

private lemma radiusFourSphere_geometry
    (t : ℝ) (z : ℂ)
    (hz : z ∈ sphere ((2 : ℂ) + t * I) 4) :
    -(2 : ℝ) ≤ z.re ∧ z.re ≤ 6 ∧
      |z.im| + 2 ≤ 3 * (|t| + 2) ∧
        ‖z‖ ≤ 3 * (|t| + 2) := by
  have hdist : ‖z - ((2 : ℂ) + t * I)‖ = 4 := by
    simpa [mem_sphere, Complex.dist_eq] using hz
  have hre : |z.re - 2| ≤ 4 := by
    calc
      |z.re - 2| = |(z - ((2 : ℂ) + t * I)).re| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_re_le_norm _
      _ = 4 := hdist
  have him : |z.im - t| ≤ 4 := by
    calc
      |z.im - t| = |(z - ((2 : ℂ) + t * I)).im| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_im_le_norm _
      _ = 4 := hdist
  have hzIm : |z.im| ≤ |t| + 4 := by
    calc
      |z.im| = |(z.im - t) + t| := by rw [sub_add_cancel]
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ 4 + |t| := by linarith
      _ = |t| + 4 := by ring
  have hcenter : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
    calc
      ‖(2 : ℂ) + t * I‖ ≤ ‖(2 : ℂ)‖ + ‖t * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp [Real.norm_eq_abs]
  have hnorm : ‖z‖ ≤ |t| + 6 := by
    calc
      ‖z‖ = ‖(z - ((2 : ℂ) + t * I)) + ((2 : ℂ) + t * I)‖ := by ring_nf
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ + ‖(2 : ℂ) + t * I‖ :=
        norm_add_le _ _
      _ ≤ 4 + (2 + |t|) := add_le_add (le_of_eq hdist) hcenter
      _ = |t| + 6 := by ring
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · linarith [abs_nonneg t]
  · linarith [abs_nonneg t]

private lemma exists_pos_norm_riemannZeta₁_closedBall_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖riemannZeta₁ z‖ ≤ C := by
  have hball : IsCompact (closedBall (0 : ℂ) 1) :=
    isCompact_closedBall (0 : ℂ) 1
  obtain ⟨C, hC⟩ := hball.exists_bound_of_continuousOn
    differentiable_riemannZeta₁.continuous.continuousOn
  refine ⟨max C 0 + 1, by linarith [le_max_right C 0], ?_⟩
  intro z hz
  exact (hC z hz).trans (by linarith [le_max_left C 0])

private lemma natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith

/-- Regularized zeta has one absolute polynomial bound on the radius-four
spheres used by the principal fixed-disk argument. -/
theorem exists_nat_norm_riemannZeta₁_radiusFourSphere_le :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ (t : ℝ) (z : ℂ),
        z ∈ sphere ((2 : ℂ) + t * I) 4 →
          ‖riemannZeta₁ z‖ ≤ (|t| + 2) ^ E := by
  obtain ⟨Ccompact, hCcompact, hcompact⟩ :=
    exists_pos_norm_riemannZeta₁_closedBall_one_le
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_gammaFactor_ratio_fixedStrip_le
  let K : ℝ := max Ccompact (4 * Cgamma * 3 ^ 11)
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge K
  refine ⟨n + 19, by omega, ?_⟩
  intro t z hz
  obtain ⟨hzlo, hzhi, hzheight, hznorm⟩ :=
    radiusFourSphere_geometry t z hz
  let T : ℝ := |t| + 2
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ T := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hzsub : ‖z - 1‖ ≤ 4 * T := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * T + 1 := add_le_add (by simpa [T] using hznorm) (by norm_num)
      _ ≤ 4 * T := by linarith
  have hKpow : K ≤ T ^ n := by
    calc
      K ≤ (n : ℝ) := hn
      _ ≤ 2 ^ n := natCast_le_two_pow n
      _ ≤ T ^ n := pow_le_pow_left₀ (by norm_num) hT2 n
  by_cases hright : (1 / 2 : ℝ) ≤ z.re
  · have habel := norm_riemannZeta₁_le_abel z (by linarith)
    have hrightBound : ‖riemannZeta₁ z‖ ≤ T ^ 7 := by
      calc
        ‖riemannZeta₁ z‖ ≤ ‖z‖ + ‖z‖ * ‖z - 1‖ / z.re := habel
        _ ≤ 3 * T + (3 * T) * (4 * T) / (1 / 2 : ℝ) := by
          gcongr
        _ = 3 * T + 24 * T ^ 2 := by ring
        _ ≤ T ^ 7 := by
          have hT5 : (32 : ℝ) ≤ T ^ 5 := by
            have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 5
            norm_num at h
            exact h
          have hT7 : 32 * T ^ 2 ≤ T ^ 7 := by
            calc
              32 * T ^ 2 ≤ T ^ 5 * T ^ 2 :=
                mul_le_mul_of_nonneg_right hT5 (sq_nonneg T)
              _ = T ^ 7 := by ring
          nlinarith [sq_nonneg T]
    exact hrightBound.trans (pow_le_pow_right₀ hT1 (by omega))
  · have hzleft : z.re ≤ (1 / 2 : ℝ) := le_of_not_ge hright
    by_cases hzsmall : ‖z‖ ≤ 1
    · have hzball : z ∈ closedBall (0 : ℂ) 1 := by
        simpa [mem_closedBall, dist_zero_right] using hzsmall
      have hC : Ccompact ≤ K := le_max_left _ _
      calc
        ‖riemannZeta₁ z‖ ≤ Ccompact := hcompact z hzball
        _ ≤ K := hC
        _ ≤ T ^ n := hKpow
        _ ≤ T ^ (n + 19) := pow_le_pow_right₀ hT1 (by omega)
    · have hz0 : z ≠ 0 := by
        intro h
        subst z
        simp at hzsmall
      have hreflect := riemannZeta₁_eq_reflection_of_re_le z hz0 hzleft
      have hreflectRe : (1 / 2 : ℝ) ≤ (1 - z).re := by simp; linarith
      have hreflectNorm : ‖1 - z‖ ≤ 4 * T := by
        calc
          ‖1 - z‖ = ‖z - 1‖ := by
            rw [show 1 - z = -(z - 1) by ring, norm_neg]
          _ ≤ 4 * T := hzsub
      have hreflectSub : ‖(1 - z) - 1‖ ≤ 3 * T := by
        simpa only [sub_sub_cancel_left, norm_neg] using
          (show ‖z‖ ≤ 3 * T by simpa [T] using hznorm)
      have hreflectAbel := norm_riemannZeta₁_le_abel (1 - z) (by linarith)
      have hreflectBound : ‖riemannZeta₁ (1 - z)‖ ≤ T ^ 7 := by
        calc
          ‖riemannZeta₁ (1 - z)‖ ≤
              ‖1 - z‖ + ‖1 - z‖ * ‖(1 - z) - 1‖ / (1 - z).re :=
            hreflectAbel
          _ ≤ 4 * T + (4 * T) * (3 * T) / (1 / 2 : ℝ) := by
            gcongr
          _ = 4 * T + 24 * T ^ 2 := by ring
          _ ≤ T ^ 7 := by
            have hT5 : (32 : ℝ) ≤ T ^ 5 := by
              have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 5
              norm_num at h
              exact h
            have hT7 : 32 * T ^ 2 ≤ T ^ 7 := by
              calc
                32 * T ^ 2 ≤ T ^ 5 * T ^ 2 :=
                  mul_le_mul_of_nonneg_right hT5 (sq_nonneg T)
                _ = T ^ 7 := by ring
            nlinarith [sq_nonneg T]
      have hratio : ‖(1 - z) / z‖ ≤ 4 * T := by
        rw [norm_div]
        have hzOne : (1 : ℝ) ≤ ‖z‖ := le_of_not_ge hzsmall
        exact (div_le_iff₀ (norm_pos_iff.mpr hz0)).2 (by
          calc
            ‖1 - z‖ ≤ 4 * T := hreflectNorm
            _ ≤ 4 * T * ‖z‖ := by
              exact le_mul_of_one_le_right (by positivity) hzOne)
      have hgamma' := hgamma 1 (1 : DirichletCharacter ℂ 1) z
        (by linarith) hzleft
      have hgammaBound :
          ‖DirichletCharacter.gammaFactor
                (1 : DirichletCharacter ℂ 1)⁻¹ (1 - z) /
              DirichletCharacter.gammaFactor
                (1 : DirichletCharacter ℂ 1) z‖ ≤
            Cgamma * (3 * T) ^ 11 := by
        exact hgamma'.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by simpa [T] using hzheight) 11)
          hCgamma.le)
      have hinvOne : (1 : DirichletCharacter ℂ 1)⁻¹ = 1 := inv_one
      rw [hinvOne] at hgammaBound
      rw [hreflect, norm_mul, norm_mul]
      calc
        ‖(1 - z) / z‖ * ‖riemannZeta₁ (1 - z)‖ *
              ‖DirichletCharacter.gammaFactor
                  (1 : DirichletCharacter ℂ 1) (1 - z) /
                DirichletCharacter.gammaFactor
                  (1 : DirichletCharacter ℂ 1) z‖ ≤
            (4 * T) * T ^ 7 * (Cgamma * (3 * T) ^ 11) := by
          gcongr
        _ = (4 * Cgamma * 3 ^ 11) * T ^ 19 := by ring
        _ ≤ K * T ^ 19 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hT0 19)
        _ ≤ T ^ n * T ^ 19 :=
          mul_le_mul_of_nonneg_right hKpow (pow_nonneg hT0 19)
        _ = T ^ (n + 19) := by rw [pow_add]

/-- The radius-four absolute bound made relative to the nonzero far-right
center. -/
theorem exists_nat_norm_riemannZeta₁_radiusFourSphere_le_exp_mul_center :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ (t : ℝ) (z : ℂ),
        z ∈ sphere ((2 : ℂ) + t * I) 4 →
          ‖riemannZeta₁ z‖ ≤
            Real.exp ((A : ℝ) * Real.log (|t| + 2)) *
              ‖riemannZeta₁ ((2 : ℂ) + t * I)‖ := by
  obtain ⟨E, hE, habsolute⟩ :=
    exists_nat_norm_riemannZeta₁_radiusFourSphere_le
  refine ⟨E + 2, by omega, ?_⟩
  intro t z hz
  let c : ℂ := (2 : ℂ) + t * I
  let T : ℝ := |t| + 2
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hTpos : 0 < T := zero_lt_two.trans_le hT2
  have hc1 : c ≠ 1 := by intro h; have := congrArg Complex.re h; simp [c] at this
  have hzeta : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [c])
  have hcenter : riemannZeta₁ c = (c - 1) * riemannZeta c := by
    rw [riemannZeta_eq_inv_sub_mul hc1]
    field_simp
  have hcsubNorm : (1 : ℝ) ≤ ‖c - 1‖ := by
    rw [show c - 1 = (1 : ℂ) + t * I by dsimp [c]; ring]
    have hre := Complex.abs_re_le_norm ((1 : ℂ) + t * I)
    simpa using hre
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
  have hexp : Real.exp (((E + 2 : ℕ) : ℝ) * Real.log T) = T ^ (E + 2) := by
    rw [Real.exp_nat_mul, Real.exp_log hTpos]
  calc
    ‖riemannZeta₁ z‖ ≤ T ^ E := habs
    _ = T ^ E * 1 := by ring
    _ ≤ T ^ E * (T ^ 2 * ‖riemannZeta₁ c‖) :=
      mul_le_mul_of_nonneg_left hTcenter (pow_nonneg hTpos.le E)
    _ = T ^ (E + 2) * ‖riemannZeta₁ c‖ := by rw [pow_add]; ring
    _ = Real.exp (((E + 2 : ℕ) : ℝ) * Real.log T) *
        ‖riemannZeta₁ c‖ := by rw [hexp]
    _ = Real.exp (((E + 2 : ℕ) : ℝ) * Real.log (|t| + 2)) *
        ‖riemannZeta₁ ((2 : ℂ) + t * I)‖ := rfl

end BoundedGaps.Maynard
