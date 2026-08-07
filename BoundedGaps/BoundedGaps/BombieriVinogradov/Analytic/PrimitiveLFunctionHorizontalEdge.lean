import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaHorizontalKernel
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionHorizontalLogDerivative

/-!
# Primitive nonprincipal horizontal edge integrals

Two-sided selected-height clearance makes the primitive nonprincipal modified
explicit-formula integrand continuous on both shallow horizontal lines. The
pointwise logarithmic-derivative theorem and modified-Perron kernel estimate
then give the source-scale bound for each edge.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 84--86 and
114--115, especially Lemmas 8.2 and 11.4 and Theorem 11.3. Semantic review:
`SEM-528`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

/-- Two-sided zero clearance makes both shallow horizontal integrands
genuinely interval-integrable. -/
theorem
    intervalIntegrable_dirichletExplicitFormulaIntegrand_primitive_horizontal
    {C q : ℕ} [NeZero q] (hC : 2 ≤ C) (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {T U : ℝ} (hT : 2 ≤ T) (_hU : U ∈ Icc T (T + 1))
    (hclear : ∀ rho : ℂ,
      (rho ≠ 1 ∨ chi ≠ 1) →
        DirichletCharacter.LFunction chi rho = 0 →
          (1 / ((C : ℝ) * Real.log ((q : ℝ) * (T + 2))) ≤
            |U - rho.im|) ∧
          (1 / ((C : ℝ) * Real.log ((q : ℝ) * (T + 2))) ≤
            |U + rho.im|))
    {x : ℝ} (_hx : 2 ≤ x) :
    IntervalIntegrable
        (fun sigma : ℝ =>
          dirichletExplicitFormulaIntegrand chi x
            ((sigma : ℂ) + U * I))
        volume (-1 / 2) (1 + 1 / Real.log x) ∧
      IntervalIntegrable
        (fun sigma : ℝ =>
          dirichletExplicitFormulaIntegrand chi x
            ((sigma : ℂ) - U * I))
        volume (-1 / 2) (1 + 1 / Real.log x) := by
  let L : ℝ := Real.log ((q : ℝ) * (T + 2))
  let delta : ℝ := 1 / ((C : ℝ) * L)
  have hLone : (1 : ℝ) ≤ L := by
    simpa [L] using one_le_dirichletHorizontalLogScale (q := q) hT
  have hCreal : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hdelta : 0 < delta := by
    exact one_div_pos.mpr (mul_pos (by linarith) (by linarith))
  have hchiNe : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hupperNonzero : ∀ sigma : ℝ,
      DirichletCharacter.LFunction chi ((sigma : ℂ) + U * I) ≠ 0 := by
    intro sigma hsZero
    have hc := (hclear ((sigma : ℂ) + U * I) (Or.inr hchiNe) hsZero).1
    have hfalse : delta ≤ 0 := by simpa [delta, L] using hc
    linarith
  have hlowerNonzero : ∀ sigma : ℝ,
      DirichletCharacter.LFunction chi ((sigma : ℂ) - U * I) ≠ 0 := by
    intro sigma hsZero
    have hc := (hclear ((sigma : ℂ) - U * I) (Or.inr hchiNe) hsZero).2
    have hfalse : delta ≤ 0 := by simpa [delta, L] using hc
    linarith
  have hupperPath : Continuous (fun sigma : ℝ => (sigma : ℂ) + U * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hlowerPath : Continuous (fun sigma : ℝ => (sigma : ℂ) - U * I) :=
    Complex.continuous_ofReal.sub continuous_const
  have hupperContinuous : Continuous (fun sigma : ℝ =>
      dirichletExplicitFormulaIntegrand chi x ((sigma : ℂ) + U * I)) := by
    rw [continuous_iff_continuousAt]
    intro sigma
    have hdiff :=
      differentiableAt_dirichletExplicitFormulaIntegrand_of_ne_zero
        hchiNe x (hupperNonzero sigma)
    have hpathAt : ContinuousAt
        (fun r : ℝ => (r : ℂ) + U * I) sigma := hupperPath.continuousAt
    have hcomp := hdiff.continuousAt.comp
      (f := fun r : ℝ => (r : ℂ) + U * I) hpathAt
    change ContinuousAt
      (dirichletExplicitFormulaIntegrand chi x ∘
        fun r : ℝ => (r : ℂ) + U * I) sigma
    exact hcomp
  have hlowerContinuous : Continuous (fun sigma : ℝ =>
      dirichletExplicitFormulaIntegrand chi x ((sigma : ℂ) - U * I)) := by
    rw [continuous_iff_continuousAt]
    intro sigma
    have hdiff :=
      differentiableAt_dirichletExplicitFormulaIntegrand_of_ne_zero
        hchiNe x (hlowerNonzero sigma)
    have hpathAt : ContinuousAt
        (fun r : ℝ => (r : ℂ) - U * I) sigma := hlowerPath.continuousAt
    have hcomp := hdiff.continuousAt.comp
      (f := fun r : ℝ => (r : ℂ) - U * I) hpathAt
    change ContinuousAt
      (dirichletExplicitFormulaIntegrand chi x ∘
        fun r : ℝ => (r : ℂ) - U * I) sigma
    exact hcomp
  exact ⟨hupperContinuous.intervalIntegrable _ _,
    hlowerContinuous.intervalIntegrable _ _⟩

/-- Each primitive nonprincipal shallow horizontal edge has the source-scale
modified explicit-formula bound. -/
theorem
    exists_nat_norm_intervalIntegral_dirichletExplicitFormulaIntegrand_primitive_horizontal_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ C : ℕ, 2 ≤ C →
        ∀ (q : ℕ) [NeZero q], 1 < q →
          ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
            ∀ (x T U : ℝ), 2 ≤ T → T ≤ x →
              U ∈ Icc T (T + 1) →
                (∀ rho : ℂ,
                  (rho ≠ 1 ∨ chi ≠ 1) →
                    DirichletCharacter.LFunction chi rho = 0 →
                      (1 / ((C : ℝ) *
                          Real.log ((q : ℝ) * (T + 2))) ≤
                        |U - rho.im|) ∧
                      (1 / ((C : ℝ) *
                          Real.log ((q : ℝ) * (T + 2))) ≤
                        |U + rho.im|)) →
                  ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
                      dirichletExplicitFormulaIntegrand chi x
                        ((sigma : ℂ) + U * I)‖ ≤
                    640 * (A : ℝ) * C * x *
                      Real.log ((q : ℝ) * x) ^ 2 / T ∧
                  ‖∫ sigma in (-1 / 2)..(1 + 1 / Real.log x),
                      dirichletExplicitFormulaIntegrand chi x
                        ((sigma : ℂ) - U * I)‖ ≤
                    640 * (A : ℝ) * C * x *
                      Real.log ((q : ℝ) * x) ^ 2 / T := by
  obtain ⟨A, hA, hpointwise⟩ :=
    exists_nat_norm_logDeriv_LFunction_primitive_horizontal_le
  refine ⟨A, hA, ?_⟩
  intro C hC q _ hq chi hchi x T U hT hTx hU hclear
  let a : ℝ := -1 / 2
  let b : ℝ := 1 + 1 / Real.log x
  let L : ℝ := Real.log ((q : ℝ) * (T + 2))
  let Q : ℝ := Real.log ((q : ℝ) * x)
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
  have hbThree : b ≤ 3 := by
    dsimp [b]
    linarith
  have hlength : b - a ≤ 4 := by
    dsimp [a]
    linarith
  have hTpos : 0 < T := by linarith
  have hU0 : 0 ≤ U := by linarith [hT, hU.1]
  have htUpper : T ≤ |U| := by simpa [abs_of_nonneg hU0] using hU.1
  have htLower : T ≤ |-U| := by simpa [abs_neg] using htUpper
  have hLone : (1 : ℝ) ≤ L := by
    simpa [L] using one_le_dirichletHorizontalLogScale (q := q) hT
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hintegrable :=
    intervalIntegrable_dirichletExplicitFormulaIntegrand_primitive_horizontal
      hC hq chi hchi hT hU hclear hx
  have hupperLog : ∀ r ∈ Icc a b,
      ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + U * I)‖ ≤ K := by
    intro r hr
    have hp := hpointwise C hC q hq chi hchi T U r hT hU
      (by dsimp [a] at hr; linarith [hr.1])
      (hr.2.trans hbThree) hclear
    simpa [K, L] using hp.1
  have hlowerLog : ∀ r ∈ Icc a b,
      ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + ((-U : ℝ) : ℂ) * I)‖ ≤ K := by
    intro r hr
    have hp := hpointwise C hC q hq chi hchi T U r hT hU
      (by dsimp [a] at hr; linarith [hr.1])
      (hr.2.trans hbThree) hclear
    simpa [K, L, sub_eq_add_neg] using hp.2
  have hlowerIntegrable : IntervalIntegrable
      (fun r : ℝ => dirichletExplicitFormulaIntegrand chi x
        ((r : ℂ) + ((-U : ℝ) : ℂ) * I)) volume a b := by
    simpa [a, b, sub_eq_add_neg] using hintegrable.2
  have hupperRaw :=
    norm_intervalIntegral_dirichletExplicitFormulaIntegrand_horizontal_le
      chi (x := x) (a := a) (b := b) (t := U) (T := T) (K := K)
      hx hab (by simp [b]) hTpos htUpper hK0
      (by simpa [a, b] using hintegrable.1) hupperLog
  have hlowerRaw :=
    norm_intervalIntegral_dirichletExplicitFormulaIntegrand_horizontal_le
      chi (x := x) (a := a) (b := b) (t := -U) (T := T) (K := K)
      hx hab (by simp [b]) hTpos htLower hK0 hlowerIntegrable hlowerLog
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsourceArg : (4 : ℝ) ≤ (q : ℝ) * x := by nlinarith
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact Real.log_nonneg (by linarith)
  have hbaseArgPos : 0 < (q : ℝ) * (T + 2) := by positivity
  have hargFirst : (q : ℝ) * (T + 2) ≤ 2 * ((q : ℝ) * x) := by
    have hheight : T + 2 ≤ 2 * x := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hheight hq0]
  have hargSecond : 2 * ((q : ℝ) * x) ≤ ((q : ℝ) * x) ^ 2 := by
    nlinarith [hsourceArg, sq_nonneg ((q : ℝ) * x - 2)]
  have hLQ : L ≤ 2 * Q := by
    calc
      L = Real.log ((q : ℝ) * (T + 2)) := rfl
      _ ≤ Real.log (((q : ℝ) * x) ^ 2) :=
        Real.log_le_log hbaseArgPos (hargFirst.trans hargSecond)
      _ = 2 * Q := by
        rw [Real.log_pow]
        simp [Q]
  have hLsq : L ^ 2 ≤ 4 * Q ^ 2 := by
    calc
      L ^ 2 ≤ (2 * Q) ^ 2 := pow_le_pow_left₀ hL0 hLQ 2
      _ = 4 * Q ^ 2 := by ring
  have hselectedUpper :
      ‖∫ r in a..b, dirichletExplicitFormulaIntegrand chi x
          ((r : ℂ) + U * I)‖ ≤
        160 * (A : ℝ) * C * x * L ^ 2 / T := by
    calc
      ‖∫ r in a..b, dirichletExplicitFormulaIntegrand chi x
          ((r : ℂ) + U * I)‖ ≤ (4 * K * x / T) * (b - a) := hupperRaw
      _ ≤ (4 * K * x / T) * 4 :=
        mul_le_mul_of_nonneg_left hlength (by positivity)
      _ = 160 * (A : ℝ) * C * x * L ^ 2 / T := by
        simp [K]
        ring
  have hselectedLower :
      ‖∫ r in a..b, dirichletExplicitFormulaIntegrand chi x
          ((r : ℂ) + ((-U : ℝ) : ℂ) * I)‖ ≤
        160 * (A : ℝ) * C * x * L ^ 2 / T := by
    calc
      ‖∫ r in a..b, dirichletExplicitFormulaIntegrand chi x
          ((r : ℂ) + ((-U : ℝ) : ℂ) * I)‖ ≤
            (4 * K * x / T) * (b - a) := hlowerRaw
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
      160 * (A : ℝ) * C * x * L ^ 2 ≤
          (160 * (A : ℝ) * C * x) * (4 * Q ^ 2) :=
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
