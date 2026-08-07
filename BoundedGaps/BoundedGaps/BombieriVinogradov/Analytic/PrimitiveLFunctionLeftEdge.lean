import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaLeftKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletLocalDivisorMass
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPrimitiveShallowZeros
import BoundedGaps.BombieriVinogradov.Analytic.FiniteDivisorReciprocalBound
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionFixedDisk

/-!
# Primitive nonprincipal fixed-left-edge estimates

The complete radius-six divisor and its fixed-disk residual control `L'/L` on
the project-fixed line `Re(s) = -1/2`. Half-unit separation from every
primitive ordinary zero removes any dependence on the selected horizontal
clearance.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 112--115,
especially Lemma 11.4 and the proof of Theorem 11.3. The source leaves this
edge estimate as an exercise. Semantic review: `SEM-530`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Metric Set
open scoped Interval

noncomputable section

/-- One absolute constant bounds the primitive nonprincipal logarithmic
derivative on the fixed negative-half line. -/
theorem exists_nat_norm_logDeriv_LFunction_primitive_leftEdge_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ t : ℝ,
            ‖logDeriv (DirichletCharacter.LFunction chi)
              (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
              10 * (A : ℝ) *
                Real.log ((q : ℝ) * (|t| + 2)) := by
  obtain ⟨Af, hAf, hfixed⟩ :=
    exists_nat_norm_logDeriv_LFunction_sub_radiusSix_divisor_finsum_le
  obtain ⟨Ad, _hAd, hmass⟩ :=
    exists_nat_finsum_divisor_LFunction_radiusSix_le
  let A := max Af Ad
  refine ⟨A, hAf.trans (Nat.le_max_left Af Ad), ?_⟩
  intro q _ hq chi hchi t
  let s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I
  let D : ℂ → ℤ :=
    MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
      (closedBall ((2 : ℂ) + t * I) 6)
  let L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hscaleFour : (4 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
    nlinarith [mul_le_mul hqTwo
      (show (2 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
      (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ q)]
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith)
  have hsDisk : s ∈ closedBall ((2 : ℂ) + t * I) 3 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hsSub : s - ((2 : ℂ) + t * I) = ((-5 / 2 : ℝ) : ℂ) := by
      dsimp [s]
      push_cast
      ring
    rw [hsSub, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hsNonzero : DirichletCharacter.LFunction chi s ≠ 0 := by
    intro hsZero
    have hsep :=
      one_half_le_norm_neg_half_add_mul_I_sub_of_LFunction_eq_zero_of_isPrimitive
        chi hchi t hsZero
    rw [show (((-1 / 2 : ℝ) : ℂ) + t * I) = s by rfl,
      sub_self, norm_zero] at hsep
    norm_num at hsep
  have hAfAReal : (Af : ℝ) ≤ A := by
    exact_mod_cast Nat.le_max_left Af Ad
  have hAdAReal : (Ad : ℝ) ≤ A := by
    exact_mod_cast Nat.le_max_right Af Ad
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hresidual0 := hfixed q hq chi hchi t s hsDisk hsNonzero
  have hresidual :
      ‖logDeriv (DirichletCharacter.LFunction chi) s -
          ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
        16 * ((A : ℝ) * L) / 3 := by
    calc
      _ ≤ 16 * ((Af : ℝ) * L) / 3 := by
        simpa [D, L] using hresidual0
      _ ≤ 16 * ((A : ℝ) * L) / 3 := by
        gcongr
  have hchiNe : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hDfinite : D.support.Finite := by
    simpa [D] using divisor_LFunction_closedBall_support_finite hchiNe
      ((2 : ℂ) + t * I) 6
  have hDnonneg : 0 ≤ D := by
    intro rho
    exact (divisor_LFunction_nonneg hchiNe
      (closedBall ((2 : ℂ) + t * I) 6)) rho
  have hDsep : ∀ rho ∈ D.support, (1 / 2 : ℝ) ≤ ‖s - rho‖ := by
    intro rho hrho
    have hrhoDisk : rho ∈ closedBall ((2 : ℂ) + t * I) 6 :=
      (MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
        (closedBall ((2 : ℂ) + t * I) 6)).supportWithinDomain
          (by simpa [D] using hrho)
    have hrhoZero : DirichletCharacter.LFunction chi rho = 0 :=
      (mem_support_divisor_LFunction_iff hchiNe hrhoDisk).1
        (by simpa [D] using hrho)
    simpa [s] using
      one_half_le_norm_neg_half_add_mul_I_sub_of_LFunction_eq_zero_of_isPrimitive
        chi hchi t hrhoZero
  have hsum0 := norm_finsum_intCast_div_sub_le D hDfinite hDnonneg
    (show (0 : ℝ) < 1 / 2 by norm_num) hDsep
  have hmass0 := hmass q hq chi hchi t
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
  calc
    ‖logDeriv (DirichletCharacter.LFunction chi) s‖ =
        ‖(logDeriv (DirichletCharacter.LFunction chi) s -
            ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)) +
          ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ := by ring_nf
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction chi) s -
            ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ +
          ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ := norm_add_le _ _
    _ ≤ 16 * ((A : ℝ) * L) / 3 + 4 * (A : ℝ) * L :=
      add_le_add hresidual hsum
    _ ≤ 10 * (A : ℝ) * L := by
      nlinarith [mul_nonneg hA0 hL0]
    _ = 10 * (A : ℝ) *
        Real.log ((q : ℝ) * (|t| + 2)) := rfl

/-- The primitive nonprincipal modified integrand is integrable on every
finite segment of the fixed negative-half line. -/
theorem intervalIntegrable_dirichletExplicitFormulaIntegrand_primitive_leftEdge
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (x U : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => dirichletExplicitFormulaIntegrand chi x
        (((-1 / 2 : ℝ) : ℂ) + t * Complex.I))
      MeasureTheory.volume (-U) U := by
  have hchiNe : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hnonzero : ∀ t : ℝ, DirichletCharacter.LFunction chi
      (((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t htZero
    have hsep :=
      one_half_le_norm_neg_half_add_mul_I_sub_of_LFunction_eq_zero_of_isPrimitive
        chi hchi t htZero
    rw [sub_self, norm_zero] at hsep
    norm_num at hsep
  have hpath : Continuous (fun t : ℝ => ((-1 / 2 : ℝ) : ℂ) + t * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcontinuous : Continuous (fun t : ℝ =>
      dirichletExplicitFormulaIntegrand chi x
        (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hdiff := differentiableAt_dirichletExplicitFormulaIntegrand_of_ne_zero
      hchiNe x (hnonzero t)
    have hcomp := hdiff.continuousAt.comp
      (f := fun r : ℝ => ((-1 / 2 : ℝ) : ℂ) + r * I)
      hpath.continuousAt
    change ContinuousAt
      (dirichletExplicitFormulaIntegrand chi x ∘
        fun r : ℝ => ((-1 / 2 : ℝ) : ℂ) + r * I) t
    exact hcomp
  exact hcontinuous.intervalIntegrable _ _

/-- The primitive nonprincipal fixed left edge has the explicit-formula
source-scale bound. -/
theorem
    exists_nat_norm_intervalIntegral_dirichletExplicitFormulaIntegrand_primitive_leftEdge_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (x T U : ℝ), 2 ≤ T → T ≤ x →
            U ∈ Set.Icc T (T + 1) →
              ‖∫ t in -U..U,
                  dirichletExplicitFormulaIntegrand chi x
                    (((-1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
                720 * (A : ℝ) * x *
                  Real.log ((q : ℝ) * x) ^ 2 / T := by
  obtain ⟨A, hA, hpointwise⟩ :=
    exists_nat_norm_logDeriv_LFunction_primitive_leftEdge_le
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi x T U hT hTx hU
  let L : ℝ := Real.log ((q : ℝ) * (U + 2))
  let R : ℝ := Real.log (U + 1)
  let Q : ℝ := Real.log ((q : ℝ) * x)
  let K : ℝ := 10 * (A : ℝ) * L
  have hx : 2 ≤ x := hT.trans hTx
  have hU0 : 0 ≤ U := by linarith [hT, hU.1]
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hqOne
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hL0 : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    nlinarith [mul_le_mul hqOne
      (show (1 : ℝ) ≤ U + 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) hq0]
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact Real.log_nonneg (by linarith)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hintegrable :=
    intervalIntegrable_dirichletExplicitFormulaIntegrand_primitive_leftEdge
      hq chi hchi x U
  have hlogBound : ∀ t ∈ Icc (-U) U,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K := by
    intro t ht
    have htAbs : |t| ≤ U := abs_le.mpr ht
    have hargPos : 0 < (q : ℝ) * (|t| + 2) := by positivity
    have harg : (q : ℝ) * (|t| + 2) ≤ (q : ℝ) * (U + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0
    have hlog : Real.log ((q : ℝ) * (|t| + 2)) ≤ L := by
      dsimp [L]
      exact Real.log_le_log hargPos harg
    have hp := hpointwise q hq chi hchi t
    calc
      _ ≤ 10 * (A : ℝ) * Real.log ((q : ℝ) * (|t| + 2)) := hp
      _ ≤ 10 * (A : ℝ) * L := by gcongr
      _ = K := rfl
  have hraw :=
    norm_intervalIntegral_dirichletExplicitFormulaIntegrand_leftEdge_le
      chi hx hU0 hK0 hintegrable hlogBound
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
  have hqSq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hqOne)]
  have hqCubeStep : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
    have hmul : 0 ≤ (q : ℝ) ^ 2 * ((q : ℝ) - 1) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hqOne)
    nlinarith
  have hqCube : (q : ℝ) ≤ (q : ℝ) ^ 3 := hqSq.trans hqCubeStep
  have hUxOne : U ≤ x + 1 := by
    calc
      U ≤ T + 1 := hU.2
      _ ≤ x + 1 := by linarith
  have hleftArg : (q : ℝ) * (U + 2) ≤
      ((q : ℝ) * x) ^ 3 := by
    calc
      (q : ℝ) * (U + 2) ≤ (q : ℝ) * (x + 3) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hq0
      _ ≤ (q : ℝ) * x ^ 3 :=
        mul_le_mul_of_nonneg_left hxPlusThree hq0
      _ ≤ (q : ℝ) ^ 3 * x ^ 3 :=
        mul_le_mul_of_nonneg_right hqCube (by positivity)
      _ = ((q : ℝ) * x) ^ 3 := by ring
  have hrightArg : U + 1 ≤ ((q : ℝ) * x) ^ 2 := by
    have hxqx : x ≤ (q : ℝ) * x := by
      calc
        x = 1 * x := by ring
        _ ≤ (q : ℝ) * x := mul_le_mul_of_nonneg_right hqOne hxpos.le
    calc
      U + 1 ≤ x + 2 := by linarith
      _ ≤ x ^ 2 := hxPlusTwo
      _ ≤ ((q : ℝ) * x) ^ 2 := pow_le_pow_left₀ hxpos.le hxqx 2
  have hqxFour : (4 : ℝ) ≤ (q : ℝ) * x := by
    nlinarith [mul_le_mul hqTwo hx (by norm_num : (0 : ℝ) ≤ 2) hq0]
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact Real.log_nonneg (by linarith)
  have hLQ : L ≤ 3 * Q := by
    calc
      L = Real.log ((q : ℝ) * (U + 2)) := rfl
      _ ≤ Real.log (((q : ℝ) * x) ^ 3) :=
        Real.log_le_log (by positivity) hleftArg
      _ = 3 * Q := by rw [Real.log_pow]; simp [Q]
  have hRQ : R ≤ 2 * Q := by
    calc
      R = Real.log (U + 1) := rfl
      _ ≤ Real.log (((q : ℝ) * x) ^ 2) :=
        Real.log_le_log (by linarith) hrightArg
      _ = 2 * Q := by rw [Real.log_pow]; simp [Q]
  have hLR : L * R ≤ 6 * Q ^ 2 := by
    calc
      L * R ≤ (3 * Q) * (2 * Q) :=
        mul_le_mul hLQ hRQ hR0 (by positivity)
      _ = 6 * Q ^ 2 := by ring
  have hsource :
      ‖∫ t in -U..U, dirichletExplicitFormulaIntegrand chi x
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
    _ = 720 * (A : ℝ) * x *
        Real.log ((q : ℝ) * x) ^ 2 / T := by simp [Q]; ring

end

end BoundedGaps.Maynard
