import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaLeftKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaPrincipalCircleIntegral
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPrimitiveShallowZeros
import BoundedGaps.BombieriVinogradov.Analytic.FiniteDivisorReciprocalBound
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusSixDivisorMass

/-!
# Principal modulus-one fixed-left-edge estimates

The entire regularization `riemannZeta₁` supplies a complete radius-six
divisor and fixed-disk residual on `Re(s) = -1/2`. This file restores the zeta
pole explicitly and derives the modulus-one left-edge integral bound.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84--86 and
114--115, especially Lemma 8.2 and the proof of Theorem 11.3. The source
leaves this edge estimate as an exercise. Semantic review: `SEM-530`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Metric Set
open scoped Interval

noncomputable section

/-- One absolute constant bounds the modulus-one logarithmic derivative on
the fixed negative-half line. -/
theorem exists_nat_norm_logDeriv_LFunction_modOne_leftEdge_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ t : ℝ,
        ‖logDeriv (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1))
            (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
          10 * (A : ℝ) * Real.log (|t| + 2) := by
  obtain ⟨Af, hAf, hfixed⟩ :=
    exists_nat_norm_logDeriv_riemannZeta₁_sub_radiusSix_divisor_finsum_le
  obtain ⟨Ad, _hAd, hmass⟩ :=
    exists_nat_finsum_divisor_riemannZeta₁_radiusSix_le
  let A := max Af Ad
  refine ⟨A, hAf.trans (Nat.le_max_left Af Ad), ?_⟩
  intro t
  let s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I
  let D : ℂ → ℤ := MeromorphicOn.divisor riemannZeta₁
    (closedBall ((2 : ℂ) + t * I) 6)
  let L : ℝ := Real.log (|t| + 2)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  have hsDisk : s ∈ closedBall ((2 : ℂ) + t * I) 3 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hsSub : s - ((2 : ℂ) + t * I) = ((-5 / 2 : ℝ) : ℂ) := by
      dsimp [s]
      push_cast
      ring
    rw [hsSub, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hsOne : s ≠ 1 := by
    intro hsEq
    have hre := congrArg Complex.re hsEq
    norm_num [s] at hre
  have hsZeta : riemannZeta s ≠ 0 := by
    intro hsZero
    have hsep :=
      one_half_le_norm_neg_half_add_mul_I_sub_of_LFunction_eq_zero_of_isPrimitive
        (1 : DirichletCharacter ℂ 1)
        DirichletCharacter.isPrimitive_one_level_one t (by
          simpa [DirichletCharacter.LFunction_modOne_eq] using hsZero)
    rw [show (((-1 / 2 : ℝ) : ℂ) + t * I) = s by rfl,
      sub_self, norm_zero] at hsep
    norm_num at hsep
  have hsZetaOne : riemannZeta₁ s ≠ 0 := by
    intro hsZero
    have hfactor := riemannZeta_eq_inv_sub_mul hsOne
    rw [hsZero, mul_zero] at hfactor
    exact hsZeta hfactor
  have hAfAReal : (Af : ℝ) ≤ A := by
    exact_mod_cast Nat.le_max_left Af Ad
  have hAdAReal : (Ad : ℝ) ≤ A := by
    exact_mod_cast Nat.le_max_right Af Ad
  have hA37 : 37 ≤ A := hAf.trans (Nat.le_max_left Af Ad)
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hresidual0 := hfixed t s hsDisk hsZetaOne
  have hresidual :
      ‖logDeriv riemannZeta₁ s -
          ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
        16 * ((A : ℝ) * L) / 3 := by
    calc
      _ ≤ 16 * ((Af : ℝ) * L) / 3 := by
        simpa [D, L] using hresidual0
      _ ≤ 16 * ((A : ℝ) * L) / 3 := by gcongr
  have hDfinite : D.support.Finite := by
    simpa [D] using divisor_riemannZeta₁_closedBall_support_finite
      ((2 : ℂ) + t * I) 6
  have hDnonneg : 0 ≤ D := by
    intro rho
    exact (divisor_riemannZeta₁_nonneg
      (closedBall ((2 : ℂ) + t * I) 6)) rho
  have hDsep : ∀ rho ∈ D.support, (1 / 2 : ℝ) ≤ ‖s - rho‖ := by
    intro rho hrho
    have hrhoDisk : rho ∈ closedBall ((2 : ℂ) + t * I) 6 :=
      (MeromorphicOn.divisor riemannZeta₁
        (closedBall ((2 : ℂ) + t * I) 6)).supportWithinDomain
          (by simpa [D] using hrho)
    have hrhoReg : riemannZeta₁ rho = 0 :=
      (mem_support_divisor_riemannZeta₁_iff hrhoDisk).1
        (by simpa [D] using hrho)
    have hrhoOne : rho ≠ 1 := by
      intro hrhoEq
      subst rho
      rw [riemannZeta₁_one] at hrhoReg
      exact one_ne_zero hrhoReg
    have hrhoZeta : riemannZeta rho = 0 := by
      have hfactor := riemannZeta_eq_inv_sub_mul hrhoOne
      rw [hrhoReg, mul_zero] at hfactor
      exact hfactor
    simpa [s, DirichletCharacter.LFunction_modOne_eq] using
      one_half_le_norm_neg_half_add_mul_I_sub_of_LFunction_eq_zero_of_isPrimitive
        (1 : DirichletCharacter ℂ 1)
        DirichletCharacter.isPrimitive_one_level_one t (by
          simpa [DirichletCharacter.LFunction_modOne_eq] using hrhoZeta)
  have hsum0 := norm_finsum_intCast_div_sub_le D hDfinite hDnonneg
    (show (0 : ℝ) < 1 / 2 by norm_num) hDsep
  have hmass0 := hmass t
  have hmassA : ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) ≤
      2 * (A : ℝ) * L := by
    calc
      _ ≤ 2 * (Ad : ℝ) * L := by simpa [D, L] using hmass0
      _ ≤ 2 * (A : ℝ) * L := by gcongr
  have hsum : ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
      4 * (A : ℝ) * L := by
    calc
      _ ≤ ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) / (1 / 2) := hsum0
      _ ≤ (2 * (A : ℝ) * L) / (1 / 2) := by gcongr
      _ = 4 * (A : ℝ) * L := by ring
  have hregular : ‖logDeriv riemannZeta₁ s‖ ≤
      16 * ((A : ℝ) * L) / 3 + 4 * (A : ℝ) * L := by
    calc
      ‖logDeriv riemannZeta₁ s‖ =
          ‖(logDeriv riemannZeta₁ s -
              ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)) +
            ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ := by ring_nf
      _ ≤ ‖logDeriv riemannZeta₁ s -
              ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ +
            ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hresidual hsum
  have hsPoleNorm : (3 / 2 : ℝ) ≤ ‖s - 1‖ := by
    calc
      (3 / 2 : ℝ) = |(s - 1).re| := by norm_num [s]
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have hpole : ‖(s - 1)⁻¹‖ ≤ 2 / 3 := by
    rw [norm_inv]
    calc
      ‖s - 1‖⁻¹ ≤ (3 / 2 : ℝ)⁻¹ :=
        by simpa [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 2)
            hsPoleNorm
      _ = 2 / 3 := by norm_num
  have hrelation :=
    neg_logDeriv_riemannZeta_eq_pole_sub_regularized_of_ne_zero
      s hsOne hsZeta
  have hlogTwo : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hLhalf : (1 / 2 : ℝ) ≤ L := by
    nlinarith [Real.log_two_gt_d9]
  have hAreal : (37 : ℝ) ≤ A := by exact_mod_cast hA37
  have hALone : (1 : ℝ) ≤ (A : ℝ) * L := by nlinarith
  have hzetaBound : ‖logDeriv riemannZeta s‖ ≤
      10 * (A : ℝ) * L := by
    have heq : logDeriv riemannZeta s =
        logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
      linear_combination -hrelation
    rw [heq]
    calc
      ‖logDeriv riemannZeta₁ s - (s - 1)⁻¹‖ ≤
          ‖logDeriv riemannZeta₁ s‖ + ‖(s - 1)⁻¹‖ := norm_sub_le _ _
      _ ≤ (16 * ((A : ℝ) * L) / 3 + 4 * (A : ℝ) * L) +
          2 / 3 := add_le_add hregular hpole
      _ ≤ 10 * (A : ℝ) * L := by nlinarith
  simpa [s, L, DirichletCharacter.LFunction_modOne_eq] using hzetaBound

/-- The modulus-one modified integrand is integrable on every finite segment
of the fixed negative-half line. -/
theorem intervalIntegrable_dirichletExplicitFormulaIntegrand_modOne_leftEdge
    (x U : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ 1) x
          (((-1 / 2 : ℝ) : ℂ) + t * Complex.I))
      MeasureTheory.volume (-U) U := by
  have hone : ∀ t : ℝ, (((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := by
    intro t ht
    have hre := congrArg Complex.re ht
    norm_num at hre
  have hnonzero : ∀ t : ℝ,
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
        (((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t htZero
    have hsep :=
      one_half_le_norm_neg_half_add_mul_I_sub_of_LFunction_eq_zero_of_isPrimitive
        (1 : DirichletCharacter ℂ 1)
        DirichletCharacter.isPrimitive_one_level_one t htZero
    rw [sub_self, norm_zero] at hsep
    norm_num at hsep
  have hpath : Continuous (fun t : ℝ => ((-1 / 2 : ℝ) : ℂ) + t * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcontinuous : Continuous (fun t : ℝ =>
      dirichletExplicitFormulaIntegrand (1 : DirichletCharacter ℂ 1) x
        (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hdiff :=
      differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
        x (hone t) (hnonzero t)
    have hcomp := hdiff.continuousAt.comp
      (f := fun r : ℝ => ((-1 / 2 : ℝ) : ℂ) + r * I)
      hpath.continuousAt
    change ContinuousAt
      (dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ 1) x ∘
          fun r : ℝ => ((-1 / 2 : ℝ) : ℂ) + r * I) t
    exact hcomp
  exact hcontinuous.intervalIntegrable _ _

/-- The modulus-one fixed left edge has the explicit-formula source-scale
bound. -/
theorem
    exists_nat_norm_intervalIntegral_dirichletExplicitFormulaIntegrand_modOne_leftEdge_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (x T U : ℝ), 2 ≤ T → T ≤ x →
        U ∈ Set.Icc T (T + 1) →
          ‖∫ t in -U..U,
              dirichletExplicitFormulaIntegrand
                (1 : DirichletCharacter ℂ 1) x
                  (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
            720 * (A : ℝ) * x * Real.log x ^ 2 / T := by
  obtain ⟨A, hA, hpointwise⟩ :=
    exists_nat_norm_logDeriv_LFunction_modOne_leftEdge_le
  refine ⟨A, hA, ?_⟩
  intro x T U hT hTx hU
  let L : ℝ := Real.log (U + 2)
  let R : ℝ := Real.log (U + 1)
  let Q : ℝ := Real.log x
  let K : ℝ := 10 * (A : ℝ) * L
  have hx : 2 ≤ x := hT.trans hTx
  have hU0 : 0 ≤ U := by linarith [hT, hU.1]
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact Real.log_nonneg (by linarith)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hintegrable :=
    intervalIntegrable_dirichletExplicitFormulaIntegrand_modOne_leftEdge x U
  have hlogBound : ∀ t ∈ Icc (-U) U,
      ‖logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1))
          (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K := by
    intro t ht
    have htAbs : |t| ≤ U := abs_le.mpr ht
    have hlog : Real.log (|t| + 2) ≤ L := by
      dsimp [L]
      exact Real.log_le_log (by positivity) (by linarith)
    have hp := hpointwise t
    calc
      _ ≤ 10 * (A : ℝ) * Real.log (|t| + 2) := hp
      _ ≤ 10 * (A : ℝ) * L := by gcongr
      _ = K := rfl
  have hraw :=
    norm_intervalIntegral_dirichletExplicitFormulaIntegrand_leftEdge_le
      (1 : DirichletCharacter ℂ 1) hx hU0 hK0 hintegrable hlogBound
  have hxpos : 0 < x := by linarith
  have hxPlusThree : x + 3 ≤ x ^ 3 := by
    have hxSq : (3 : ℝ) ≤ x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx)
        (show (0 : ℝ) ≤ x + 2 by linarith)]
    have hmul : 0 ≤ x * (x ^ 2 - 3) :=
      mul_nonneg hxpos.le (sub_nonneg.mpr hxSq)
    nlinarith
  have hxPlusTwo : x + 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx)
      (show (0 : ℝ) ≤ x + 1 by linarith)]
  have hUxOne : U ≤ x + 1 := by
    calc
      U ≤ T + 1 := hU.2
      _ ≤ x + 1 := by linarith
  have hleftArg : U + 2 ≤ x ^ 3 :=
    (by linarith : U + 2 ≤ x + 3).trans hxPlusThree
  have hrightArg : U + 1 ≤ x ^ 2 :=
    (by linarith : U + 1 ≤ x + 2).trans hxPlusTwo
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact Real.log_nonneg (by linarith)
  have hLQ : L ≤ 3 * Q := by
    calc
      L = Real.log (U + 2) := rfl
      _ ≤ Real.log (x ^ 3) := Real.log_le_log (by linarith) hleftArg
      _ = 3 * Q := by rw [Real.log_pow]; simp [Q]
  have hRQ : R ≤ 2 * Q := by
    calc
      R = Real.log (U + 1) := rfl
      _ ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hrightArg
      _ = 2 * Q := by rw [Real.log_pow]; simp [Q]
  have hLR : L * R ≤ 6 * Q ^ 2 := by
    calc
      L * R ≤ (3 * Q) * (2 * Q) :=
        mul_le_mul hLQ hRQ hR0 (by positivity)
      _ = 6 * Q ^ 2 := by ring
  have hsource :
      ‖∫ t in -U..U,
          dirichletExplicitFormulaIntegrand
            (1 : DirichletCharacter ℂ 1) x
              (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        720 * (A : ℝ) * Q ^ 2 := by
    calc
      _ ≤ 12 * K * R := by simpa [R] using hraw
      _ = (120 * (A : ℝ)) * (L * R) := by simp [K]; ring
      _ ≤ (120 * (A : ℝ)) * (6 * Q ^ 2) :=
        mul_le_mul_of_nonneg_left hLR (by positivity)
      _ = 720 * (A : ℝ) * Q ^ 2 := by ring
  have hTpos : 0 < T := by linarith
  have hratio : (1 : ℝ) ≤ x / T :=
    (le_div_iff₀ hTpos).2 (by simpa using hTx)
  calc
    _ ≤ 720 * (A : ℝ) * Q ^ 2 := hsource
    _ ≤ (720 * (A : ℝ) * Q ^ 2) * (x / T) :=
      le_mul_of_one_le_right (by positivity) hratio
    _ = 720 * (A : ℝ) * x * Real.log x ^ 2 / T := by simp [Q]; ring

end

end BoundedGaps.Maynard
