import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaHorizontalKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaPrincipalCircleIntegral
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaHorizontalLogDerivative

/-!
# Principal modulus-one horizontal edge integrals

Two-sided selected-height clearance makes the modulus-one principal modified
explicit-formula integrand continuous on both shallow horizontal lines. The
pointwise logarithmic-derivative theorem and modified Perron kernel estimate
then give the source-scale bound for both edges.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84--86 and
114--115, especially Lemma 8.2 and Theorem 11.3. Semantic review: `SEM-529`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

/-- Two-sided zero clearance makes both modulus-one shallow horizontal
integrands genuinely interval-integrable. -/
theorem intervalIntegrable_dirichletExplicitFormulaIntegrand_modOne_horizontal
    {C : ℕ} (hC : 2 ≤ C) {T U : ℝ} (hT : 2 ≤ T)
    (hU : U ∈ Icc T (T + 1))
    (hclear : ∀ rho : ℂ,
      (rho ≠ 1 ∨ (1 : DirichletCharacter ℂ 1) ≠ 1) →
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) rho = 0 →
          (1 / ((C : ℝ) * Real.log (T + 2)) ≤ |U - rho.im|) ∧
          (1 / ((C : ℝ) * Real.log (T + 2)) ≤ |U + rho.im|))
    {x : ℝ} (_hx : 2 ≤ x) :
    IntervalIntegrable
        (fun sigma : ℝ => dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ 1) x ((sigma : ℂ) + U * I))
        volume (-1 / 2) (1 + 1 / Real.log x) ∧
      IntervalIntegrable
        (fun sigma : ℝ => dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ 1) x ((sigma : ℂ) - U * I))
        volume (-1 / 2) (1 + 1 / Real.log x) := by
  let L : ℝ := Real.log (T + 2)
  let delta : ℝ := 1 / ((C : ℝ) * L)
  have hLone : (1 : ℝ) ≤ L := by
    simpa [L] using one_le_riemannZetaHorizontalLogScale hT
  have hCreal : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hdelta : 0 < delta :=
    one_div_pos.mpr (mul_pos (by linarith) (by linarith))
  have hUpos : 0 < U := by linarith [hT, hU.1]
  have hupperOne : ∀ sigma : ℝ, ((sigma : ℂ) + U * I) ≠ 1 := by
    intro sigma hs
    have him := congrArg Complex.im hs
    simp at him
    linarith
  have hlowerOne : ∀ sigma : ℝ, ((sigma : ℂ) - U * I) ≠ 1 := by
    intro sigma hs
    have him := congrArg Complex.im hs
    simp at him
    linarith
  have hupperNonzero : ∀ sigma : ℝ,
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
        ((sigma : ℂ) + U * I) ≠ 0 := by
    intro sigma hsZero
    have hc := (hclear ((sigma : ℂ) + U * I)
      (Or.inl (hupperOne sigma)) hsZero).1
    have hfalse : delta ≤ 0 := by simpa [delta, L] using hc
    linarith
  have hlowerNonzero : ∀ sigma : ℝ,
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
        ((sigma : ℂ) - U * I) ≠ 0 := by
    intro sigma hsZero
    have hc := (hclear ((sigma : ℂ) - U * I)
      (Or.inl (hlowerOne sigma)) hsZero).2
    have hfalse : delta ≤ 0 := by simpa [delta, L] using hc
    linarith
  have hupperPath : Continuous (fun sigma : ℝ => (sigma : ℂ) + U * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hlowerPath : Continuous (fun sigma : ℝ => (sigma : ℂ) - U * I) :=
    Complex.continuous_ofReal.sub continuous_const
  have hupperContinuous : Continuous (fun sigma : ℝ =>
      dirichletExplicitFormulaIntegrand (1 : DirichletCharacter ℂ 1) x
        ((sigma : ℂ) + U * I)) := by
    rw [continuous_iff_continuousAt]
    intro sigma
    have hdiff :=
      differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
        x (hupperOne sigma) (hupperNonzero sigma)
    have hcomp := hdiff.continuousAt.comp
      (f := fun r : ℝ => (r : ℂ) + U * I) hupperPath.continuousAt
    change ContinuousAt
      (dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ 1) x ∘
          fun r : ℝ => (r : ℂ) + U * I) sigma
    exact hcomp
  have hlowerContinuous : Continuous (fun sigma : ℝ =>
      dirichletExplicitFormulaIntegrand (1 : DirichletCharacter ℂ 1) x
        ((sigma : ℂ) - U * I)) := by
    rw [continuous_iff_continuousAt]
    intro sigma
    have hdiff :=
      differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
        x (hlowerOne sigma) (hlowerNonzero sigma)
    have hcomp := hdiff.continuousAt.comp
      (f := fun r : ℝ => (r : ℂ) - U * I) hlowerPath.continuousAt
    change ContinuousAt
      (dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ 1) x ∘
          fun r : ℝ => (r : ℂ) - U * I) sigma
    exact hcomp
  exact ⟨hupperContinuous.intervalIntegrable _ _,
    hlowerContinuous.intervalIntegrable _ _⟩

/-- Each modulus-one principal shallow horizontal edge has the source-scale
modified explicit-formula bound. -/
theorem
    exists_nat_norm_intervalIntegral_dirichletExplicitFormulaIntegrand_modOne_horizontal_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ C : ℕ, 2 ≤ C →
        ∀ (x T U : ℝ), 2 ≤ T → T ≤ x →
          U ∈ Icc T (T + 1) →
            (∀ rho : ℂ,
              (rho ≠ 1 ∨ (1 : DirichletCharacter ℂ 1) ≠ 1) →
                DirichletCharacter.LFunction
                    (1 : DirichletCharacter ℂ 1) rho = 0 →
                  (1 / ((C : ℝ) * Real.log (T + 2)) ≤
                    |U - rho.im|) ∧
                  (1 / ((C : ℝ) * Real.log (T + 2)) ≤
                    |U + rho.im|)) →
              ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
                  dirichletExplicitFormulaIntegrand
                    (1 : DirichletCharacter ℂ 1) x
                    ((sigma : ℂ) + U * I)‖ ≤
                640 * (A : ℝ) * C * x * Real.log x ^ 2 / T ∧
              ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
                  dirichletExplicitFormulaIntegrand
                    (1 : DirichletCharacter ℂ 1) x
                    ((sigma : ℂ) - U * I)‖ ≤
                640 * (A : ℝ) * C * x * Real.log x ^ 2 / T := by
  obtain ⟨A, hA, hpointwise⟩ :=
    exists_nat_norm_logDeriv_LFunction_modOne_horizontal_le
  refine ⟨A, hA, ?_⟩
  intro C hC x T U hT hTx hU hclear
  let a : ℝ := -1 / 2
  let b : ℝ := 1 + 1 / Real.log x
  let L : ℝ := Real.log (T + 2)
  let Q : ℝ := Real.log x
  let K : ℝ := 10 * (A : ℝ) * C * L ^ 2
  have hx : 2 ≤ x := hT.trans hTx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [one_div_pos.mpr hlogx]
  have hlogHalf : (1 / 2 : ℝ) < Real.log x := by
    have hlogTwo : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx
    nlinarith [Real.log_two_gt_d9]
  have hinvLog : 1 / Real.log x ≤ 2 := by
    apply (div_le_iff₀ hlogx).2
    nlinarith
  have hbThree : b ≤ 3 := by dsimp [b]; linarith
  have hlength : b - a ≤ 4 := by dsimp [a]; linarith
  have hTpos : 0 < T := by linarith
  have hU0 : 0 ≤ U := by linarith [hT, hU.1]
  have htUpper : T ≤ |U| := by
    simpa [abs_of_nonneg hU0] using hU.1
  have htLower : T ≤ |-U| := by simpa [abs_neg] using htUpper
  have hLone : (1 : ℝ) ≤ L := by
    simpa [L] using one_le_riemannZetaHorizontalLogScale hT
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hintegrable :=
    intervalIntegrable_dirichletExplicitFormulaIntegrand_modOne_horizontal
      hC hT hU hclear hx
  have hupperLog : ∀ r ∈ Icc a b,
      ‖logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1)) ((r : ℂ) + U * I)‖ ≤ K := by
    intro r hr
    have hp := hpointwise C hC T U r hT hU
      (by dsimp [a] at hr; linarith [hr.1])
      (hr.2.trans hbThree) hclear
    simpa [K, L] using hp.1
  have hlowerLog : ∀ r ∈ Icc a b,
      ‖logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1))
          ((r : ℂ) + ((-U : ℝ) : ℂ) * I)‖ ≤ K := by
    intro r hr
    have hp := hpointwise C hC T U r hT hU
      (by dsimp [a] at hr; linarith [hr.1])
      (hr.2.trans hbThree) hclear
    simpa [K, L, sub_eq_add_neg] using hp.2
  have hlowerIntegrable : IntervalIntegrable
      (fun r : ℝ => dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ 1) x
          ((r : ℂ) + ((-U : ℝ) : ℂ) * I)) volume a b := by
    simpa [a, b, sub_eq_add_neg] using hintegrable.2
  have hupperRaw :=
    norm_intervalIntegral_dirichletExplicitFormulaIntegrand_horizontal_le
      (1 : DirichletCharacter ℂ 1)
      (x := x) (a := a) (b := b) (t := U) (T := T) (K := K)
      hx hab (by simp [b]) hTpos htUpper hK0
      (by simpa [a, b] using hintegrable.1) hupperLog
  have hlowerRaw :=
    norm_intervalIntegral_dirichletExplicitFormulaIntegrand_horizontal_le
      (1 : DirichletCharacter ℂ 1)
      (x := x) (a := a) (b := b) (t := -U) (T := T) (K := K)
      hx hab (by simp [b]) hTpos htLower hK0 hlowerIntegrable hlowerLog
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hargPos : 0 < T + 2 := by linarith
  have harg : T + 2 ≤ x ^ 2 := by
    have hxpoly : x + 2 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx)
        (by linarith : 0 ≤ x + 1)]
    nlinarith
  have hLQ : L ≤ 2 * Q := by
    calc
      L = Real.log (T + 2) := rfl
      _ ≤ Real.log (x ^ 2) := Real.log_le_log hargPos harg
      _ = 2 * Q := by rw [Real.log_pow]; simp [Q]
  have hLsq : L ^ 2 ≤ 4 * Q ^ 2 := by
    calc
      L ^ 2 ≤ (2 * Q) ^ 2 := pow_le_pow_left₀ hL0 hLQ 2
      _ = 4 * Q ^ 2 := by ring
  have hselectedUpper :
      ‖∫ r in a..b, dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ 1) x ((r : ℂ) + U * I)‖ ≤
        160 * (A : ℝ) * C * x * L ^ 2 / T := by
    calc
      _ ≤ (4 * K * x / T) * (b - a) := hupperRaw
      _ ≤ (4 * K * x / T) * 4 :=
        mul_le_mul_of_nonneg_left hlength (by positivity)
      _ = 160 * (A : ℝ) * C * x * L ^ 2 / T := by
        simp [K]
        ring
  have hselectedLower :
      ‖∫ r in a..b, dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ 1) x
            ((r : ℂ) + ((-U : ℝ) : ℂ) * I)‖ ≤
        160 * (A : ℝ) * C * x * L ^ 2 / T := by
    calc
      _ ≤ (4 * K * x / T) * (b - a) := hlowerRaw
      _ ≤ (4 * K * x / T) * 4 :=
        mul_le_mul_of_nonneg_left hlength (by positivity)
      _ = 160 * (A : ℝ) * C * x * L ^ 2 / T := by
        simp [K]
        ring
  have hcoefficient : 0 ≤ 160 * (A : ℝ) * C * x := by positivity
  have hsourceNumerator :
      160 * (A : ℝ) * C * x * L ^ 2 ≤
        640 * (A : ℝ) * C * x * Q ^ 2 := by
    calc
      _ ≤ (160 * (A : ℝ) * C * x) * (4 * Q ^ 2) :=
        mul_le_mul_of_nonneg_left hLsq hcoefficient
      _ = 640 * (A : ℝ) * C * x * Q ^ 2 := by ring
  constructor
  · have hfinal := hselectedUpper.trans
      (div_le_div_of_nonneg_right hsourceNumerator hTpos.le)
    simpa [a, b, L, Q] using hfinal
  · have hfinal := hselectedLower.trans
      (div_le_div_of_nonneg_right hsourceNumerator hTpos.le)
    simpa [a, b, L, Q, sub_eq_add_neg] using hfinal

end

end BoundedGaps.Maynard
