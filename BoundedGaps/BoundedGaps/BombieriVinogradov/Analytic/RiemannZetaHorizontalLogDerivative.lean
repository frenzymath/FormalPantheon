import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusSixDivisorMass
import BoundedGaps.BombieriVinogradov.Analytic.FiniteDivisorReciprocalBound

/-!
# Principal modulus-one horizontal logarithmic derivatives

This file combines the radius-six regularized-zeta divisor mass, the
radius-three fixed-disk residual, two-sided selected-height clearance, and the
exact zeta pole term. The result controls both shallow horizontal lines for
the unique Dirichlet character modulo one.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84--86,
89--92, and 114--115, especially Lemmas 8.2 and 8.6 and Theorem 11.3.
Semantic review: `SEM-529`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

/-- The modulus-one selected-height scale has logarithm at least one. -/
theorem one_le_riemannZetaHorizontalLogScale
    {T : ℝ} (hT : 2 ≤ T) :
    (1 : ℝ) ≤ Real.log (T + 2) := by
  have hscale : (4 : ℝ) ≤ T + 2 := by linarith
  have hlogFour : (1 : ℝ) < Real.log 4 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_gt_d9]
  exact hlogFour.le.trans (Real.log_le_log (by norm_num) hscale)

private theorem log_riemannZetaSelectedHeightScale_le_two_mul
    {T U : ℝ} (hT : 2 ≤ T) (hU : U ∈ Icc T (T + 1)) :
    Real.log (|U| + 2) ≤ 2 * Real.log (T + 2) := by
  have hU0 : 0 ≤ U := by linarith [hT, hU.1]
  have hheight : U + 2 ≤ (T + 2) ^ 2 := by
    nlinarith [hU.2, sq_nonneg T]
  calc
    Real.log (|U| + 2) ≤ Real.log ((T + 2) ^ 2) := by
      rw [abs_of_nonneg hU0]
      exact Real.log_le_log (by linarith) hheight
    _ = 2 * Real.log (T + 2) := by
      rw [Real.log_pow]
      norm_num

/-- At one selected good height, the modulus-one logarithmic derivative is
uniformly bounded on both shallow horizontal lines. -/
theorem exists_nat_norm_logDeriv_LFunction_modOne_horizontal_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ C : ℕ, 2 ≤ C →
        ∀ (T U sigma : ℝ), 2 ≤ T →
          U ∈ Icc T (T + 1) →
            -1 ≤ sigma → sigma ≤ 3 →
              (∀ rho : ℂ,
                (rho ≠ 1 ∨ (1 : DirichletCharacter ℂ 1) ≠ 1) →
                  DirichletCharacter.LFunction
                      (1 : DirichletCharacter ℂ 1) rho = 0 →
                    (1 / ((C : ℝ) * Real.log (T + 2)) ≤
                      |U - rho.im|) ∧
                    (1 / ((C : ℝ) * Real.log (T + 2)) ≤
                      |U + rho.im|)) →
                ‖logDeriv (DirichletCharacter.LFunction
                    (1 : DirichletCharacter ℂ 1))
                    ((sigma : ℂ) + U * I)‖ ≤
                  10 * (A : ℝ) * C * Real.log (T + 2) ^ 2 ∧
                ‖logDeriv (DirichletCharacter.LFunction
                    (1 : DirichletCharacter ℂ 1))
                    ((sigma : ℂ) - U * I)‖ ≤
                  10 * (A : ℝ) * C * Real.log (T + 2) ^ 2 := by
  obtain ⟨Af, hAf, hfixed⟩ :=
    exists_nat_norm_logDeriv_riemannZeta₁_sub_radiusSix_divisor_finsum_le
  obtain ⟨Ad, _hAd, hmass⟩ :=
    exists_nat_finsum_divisor_riemannZeta₁_radiusSix_le
  let A := max Af Ad
  refine ⟨A, hAf.trans (Nat.le_max_left Af Ad), ?_⟩
  intro C hC T U sigma hT hU hsigmaLower hsigmaUpper hclear
  let L : ℝ := Real.log (T + 2)
  let delta : ℝ := 1 / ((C : ℝ) * L)
  have hLone : (1 : ℝ) ≤ L := by
    simpa [L] using one_le_riemannZetaHorizontalLogScale hT
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hCreal : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hdelta : 0 < delta :=
    one_div_pos.mpr (mul_pos (by linarith) (by linarith))
  have hU0 : 0 ≤ U := by linarith [hT, hU.1]
  have hheightLog : Real.log (|U| + 2) ≤ 2 * L := by
    simpa [L] using log_riemannZetaSelectedHeightScale_le_two_mul hT hU
  have hAfA : Af ≤ A := Nat.le_max_left Af Ad
  have hAdA : Ad ≤ A := Nat.le_max_right Af Ad
  have hAfAReal : (Af : ℝ) ≤ A := by exact_mod_cast hAfA
  have hAdAReal : (Ad : ℝ) ≤ A := by exact_mod_cast hAdA
  have hA37 : 37 ≤ A := hAf.trans hAfA
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hbound : ∀ (t : ℝ), |t| = U →
      (∀ rho : ℂ, riemannZeta rho = 0 → rho ≠ 1 →
        delta ≤ |t - rho.im|) →
      ∀ (r : ℝ), -1 ≤ r → r ≤ 3 →
        ‖logDeriv riemannZeta ((r : ℂ) + t * I)‖ ≤
          10 * (A : ℝ) * C * L ^ 2 := by
    intro t htAbs hclearSigned r hrLower hrUpper
    let s : ℂ := (r : ℂ) + t * I
    let D : ℂ → ℤ := MeromorphicOn.divisor riemannZeta₁
      (closedBall ((2 : ℂ) + t * I) 6)
    have hlogt : Real.log (|t| + 2) ≤ 2 * L := by
      simpa [htAbs, abs_of_nonneg hU0] using hheightLog
    have hlogt0 : 0 ≤ Real.log (|t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    have hsDisk : s ∈ closedBall ((2 : ℂ) + t * I) 3 := by
      rw [mem_closedBall, Complex.dist_eq]
      have hsSub : s - ((2 : ℂ) + t * I) = ((r - 2 : ℝ) : ℂ) := by
        dsimp [s]
        push_cast
        ring
      rw [hsSub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor
      · linarith
      · linarith
    have hsOne : s ≠ 1 := by
      intro hsEq
      have him := congrArg Complex.im hsEq
      simp [s] at him
      have ht0 : 0 < |t| := by
        rw [htAbs]
        linarith [hT, hU.1]
      exact (abs_pos.mp ht0) him
    have hsZeta : riemannZeta s ≠ 0 := by
      intro hsZero
      have hsep := hclearSigned s hsZero hsOne
      have hsim : s.im = t := by simp [s]
      rw [hsim, sub_self, abs_zero] at hsep
      linarith
    have hsZetaOne : riemannZeta₁ s ≠ 0 := by
      intro hsZero
      have hfactor := riemannZeta_eq_inv_sub_mul hsOne
      rw [hsZero, mul_zero] at hfactor
      exact hsZeta hfactor
    have hresidual0 := hfixed t s hsDisk hsZetaOne
    have hprodResidual :
        (Af : ℝ) * Real.log (|t| + 2) ≤ (A : ℝ) * (2 * L) :=
      mul_le_mul hAfAReal hlogt hlogt0 hA0
    have hresidual :
        ‖logDeriv riemannZeta₁ s -
            ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
          32 * (A : ℝ) * L / 3 := by
      calc
        _ ≤ 16 * ((Af : ℝ) * Real.log (|t| + 2)) / 3 := by
          simpa [D] using hresidual0
        _ ≤ 16 * ((A : ℝ) * (2 * L)) / 3 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprodResidual (by norm_num))
            (by norm_num)
        _ = 32 * (A : ℝ) * L / 3 := by ring
    have hDfinite : D.support.Finite := by
      simpa [D] using divisor_riemannZeta₁_closedBall_support_finite
        ((2 : ℂ) + t * I) 6
    have hDnonneg : 0 ≤ D := by
      intro rho
      exact (divisor_riemannZeta₁_nonneg
        (closedBall ((2 : ℂ) + t * I) 6)) rho
    have hDsep : ∀ rho ∈ D.support, delta ≤ ‖s - rho‖ := by
      intro rho hrho
      have hrhoDisk : rho ∈ closedBall ((2 : ℂ) + t * I) 6 :=
        (MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 6)).supportWithinDomain
            (by simpa [D] using hrho)
      have hrhoReg : riemannZeta₁ rho = 0 :=
        (mem_support_divisor_riemannZeta₁_iff hrhoDisk).1
          (by simpa [D] using hrho)
      have hrhoOne : rho ≠ 1 := by
        intro h
        subst rho
        rw [riemannZeta₁_one] at hrhoReg
        exact one_ne_zero hrhoReg
      have hrhoZero : riemannZeta rho = 0 := by
        have hfactor := riemannZeta_eq_inv_sub_mul hrhoOne
        rw [hrhoReg, mul_zero] at hfactor
        exact hfactor
      calc
        delta ≤ |t - rho.im| := hclearSigned rho hrhoZero hrhoOne
        _ = |(s - rho).im| := by simp [s]
        _ ≤ ‖s - rho‖ := Complex.abs_im_le_norm _
    have hsum0 := norm_finsum_intCast_div_sub_le
      D hDfinite hDnonneg hdelta hDsep
    have hmass0 := hmass t
    have hprodMass :
        (Ad : ℝ) * Real.log (|t| + 2) ≤ (A : ℝ) * (2 * L) :=
      mul_le_mul hAdAReal hlogt hlogt0 hA0
    have hmassBound : ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) ≤
        4 * (A : ℝ) * L := by
      calc
        _ ≤ 2 * (Ad : ℝ) * Real.log (|t| + 2) := by
          simpa [D] using hmass0
        _ ≤ 2 * ((A : ℝ) * (2 * L)) := by nlinarith
        _ = 4 * (A : ℝ) * L := by ring
    have hsum : ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
        4 * (A : ℝ) * C * L ^ 2 := by
      calc
        _ ≤ ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) / delta := hsum0
        _ ≤ (4 * (A : ℝ) * L) / delta :=
          div_le_div_of_nonneg_right hmassBound hdelta.le
        _ = 4 * (A : ℝ) * C * L ^ 2 := by
          dsimp [delta]
          field_simp
    have hTnorm : 2 ≤ ‖s - 1‖ := by
      calc
        2 ≤ |t| := by simpa [htAbs] using hT.trans hU.1
        _ = |(s - 1).im| := by simp [s]
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have hpole : ‖(s - 1)⁻¹‖ ≤ 1 / 2 := by
      rw [norm_inv]
      simpa [one_div] using
        one_div_le_one_div_of_le (by norm_num) hTnorm
    have hrelation :=
      neg_logDeriv_riemannZeta_eq_pole_sub_regularized_of_ne_zero
        s hsOne hsZeta
    have hCLtwo : (2 : ℝ) ≤ (C : ℝ) * L := by
      nlinarith [mul_le_mul hCreal hLone
        (by norm_num : (0 : ℝ) ≤ 1) hC0]
    have hAL0 : 0 ≤ (A : ℝ) * L := mul_nonneg hA0 hL0
    have hscaleProduct : 2 * ((A : ℝ) * L) ≤
        ((C : ℝ) * L) * ((A : ℝ) * L) :=
      mul_le_mul_of_nonneg_right hCLtwo hAL0
    have hhalf : (1 / 2 : ℝ) ≤
        (2 / 3) * (A : ℝ) * C * L ^ 2 := by
      have hAreal : (37 : ℝ) ≤ A := by exact_mod_cast hA37
      nlinarith [mul_le_mul hCreal hLone
        (by norm_num : (0 : ℝ) ≤ 1) hC0]
    have hregularTotal : ‖logDeriv riemannZeta₁ s‖ ≤
        ‖logDeriv riemannZeta₁ s -
          ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ +
        ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ := by
      calc
        ‖logDeriv riemannZeta₁ s‖ =
            ‖(logDeriv riemannZeta₁ s -
                ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)) +
              ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    calc
      ‖logDeriv riemannZeta s‖ =
          ‖logDeriv riemannZeta₁ s - (s - 1)⁻¹‖ := by
        have heq : logDeriv riemannZeta s =
            logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
          linear_combination -hrelation
        rw [heq]
      _ ≤ ‖logDeriv riemannZeta₁ s‖ + ‖(s - 1)⁻¹‖ := norm_sub_le _ _
      _ ≤ (‖logDeriv riemannZeta₁ s -
            ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ +
          ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖) +
            ‖(s - 1)⁻¹‖ := add_le_add hregularTotal le_rfl
      _ ≤ 32 * (A : ℝ) * L / 3 +
          4 * (A : ℝ) * C * L ^ 2 + 1 / 2 :=
        add_le_add (add_le_add hresidual hsum) hpole
      _ ≤ 10 * (A : ℝ) * C * L ^ 2 := by
        nlinarith [hscaleProduct, hhalf]
  constructor
  · have hu := hbound U (abs_of_nonneg hU0)
        (fun rho hrho hrhoOne =>
          (hclear rho (Or.inl hrhoOne) (by simpa using hrho)).1)
        sigma hsigmaLower hsigmaUpper
    simpa [L, DirichletCharacter.LFunction_modOne_eq] using hu
  · have hl := hbound (-U) (by rw [abs_neg, abs_of_nonneg hU0])
        (fun rho hrho hrhoOne => by
          have hc :=
            (hclear rho (Or.inl hrhoOne) (by simpa using hrho)).2
          convert hc using 1
          rw [show -U - rho.im = -(U + rho.im) by ring, abs_neg])
        sigma hsigmaLower hsigmaUpper
    simpa [L, sub_eq_add_neg, DirichletCharacter.LFunction_modOne_eq]
      using hl

end

end BoundedGaps.Maynard
