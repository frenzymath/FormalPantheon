import BoundedGaps.BombieriVinogradov.Analytic.CharacterOrthogonality
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaContourEdges
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaShallowCorrection
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronVonMangoldt
import BoundedGaps.BombieriVinogradov.Analytic.ThreeFourOne
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The modified Perron bridge

The explicit-formula right edge uses `(x^s - 1) / s`. This file identifies it
exactly with the ordinary twisted Perron integral at base `x` minus the same
integral at base one, then proves the source-shaped arithmetic approximation.
The additive `log x` term is retained until the selected-height corollary.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

private noncomputable def twistVonMangoldt
    {q : ℕ} (chi : DirichletCharacter ℂ q) : ℕ → ℂ :=
  (fun n : ℕ => chi n) *
    fun n => (ArithmeticFunction.vonMangoldt n : ℂ)

private lemma one_lt_perronAbscissa {x : ℝ} (hx : 1 < x) :
    1 < 1 + 1 / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have : 0 < 1 / Real.log x := by positivity
  linarith

/-- The modified right edge is exactly raw Perron at base `x` minus raw
Perron at base one. -/
theorem
    dirichletExplicitFormulaNormalizedRightEdge_eq_rawPerron_sub_baseOne
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x U : ℝ} (hx : 1 < x) :
    dirichletExplicitFormulaNormalizedRightEdge chi x U =
      dirichletPerronIntegral
          ((fun n : ℕ => chi n) *
            fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          x (1 + 1 / Real.log x) U -
        dirichletPerronIntegral
          ((fun n : ℕ => chi n) *
            fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          1 (1 + 1 / Real.log x) U := by
  let alpha : ℝ := 1 + 1 / Real.log x
  let a : ℕ → ℂ := twistVonMangoldt chi
  have hxPos : 0 < x := zero_lt_one.trans hx
  have halphaOne : 1 < alpha := one_lt_perronAbscissa hx
  have halpha : 0 < alpha := zero_lt_one.trans halphaOne
  have hsum : LSeriesSummable a (alpha : ℂ) := by
    simpa [a, twistVonMangoldt] using
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi halphaOne
  have hpoint (t : ℝ) :
      dirichletExplicitFormulaIntegrand chi x
          ((alpha : ℂ) + t * I) =
        LSeries a ((alpha : ℂ) + t * I) *
            (x : ℂ) ^ ((alpha : ℂ) + t * I) /
              ((alpha : ℂ) + t * I) -
          LSeries a ((alpha : ℂ) + t * I) *
            (1 : ℂ) ^ ((alpha : ℂ) + t * I) /
              ((alpha : ℂ) + t * I) := by
    let s : ℂ := (alpha : ℂ) + t * I
    have hsRe : s.re = alpha := by simp [s]
    have hs : 1 < s.re := by simpa [hsRe] using halphaOne
    have hsNe : s ≠ 0 := by
      intro hsZero
      have hre := congrArg Complex.re hsZero
      simp [s] at hre
      linarith
    have hlogDeriv :
        -logDeriv (DirichletCharacter.LFunction chi) s = LSeries a s := by
      rw [neg_logDeriv_LFunction_eq_LSeries chi hs,
        logDeriv_apply, ← neg_div,
        ← DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs]
      rfl
    rw [dirichletExplicitFormulaIntegrand, hlogDeriv,
      dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hxPos hsNe]
    dsimp [a, s]
    simp only [one_cpow]
    ring
  have hxInt := intervalIntegrable_dirichletPerronLSeriesIntegrand
    (U := U) hsum hxPos halpha
  have hOneInt := intervalIntegrable_dirichletPerronLSeriesIntegrand
    (U := U) hsum (by norm_num : (0 : ℝ) < 1) halpha
  have hOneInt' : IntervalIntegrable
      (fun t : ℝ =>
        LSeries a ((alpha : ℂ) + t * I) *
          (1 : ℂ) ^ ((alpha : ℂ) + t * I) /
            ((alpha : ℂ) + t * I)) volume (-U) U := by
    simpa using hOneInt
  have hintegral :
      (∫ t in -U..U,
        dirichletExplicitFormulaIntegrand chi x
          ((alpha : ℂ) + t * I)) =
        (∫ t in -U..U,
          LSeries a ((alpha : ℂ) + t * I) *
            (x : ℂ) ^ ((alpha : ℂ) + t * I) /
              ((alpha : ℂ) + t * I)) -
        ∫ t in -U..U,
          LSeries a ((alpha : ℂ) + t * I) *
            (1 : ℂ) ^ ((alpha : ℂ) + t * I) /
              ((alpha : ℂ) + t * I) := by
    rw [← intervalIntegral.integral_sub hxInt hOneInt']
    exact intervalIntegral.integral_congr fun t _ => hpoint t
  rw [dirichletExplicitFormulaNormalizedRightEdge,
    dirichletPerronIntegral, dirichletPerronIntegral]
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        (∫ t in -U..U,
          dirichletExplicitFormulaIntegrand chi x
            ((alpha : ℂ) + t * I)) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          (∫ t in -U..U,
            LSeries a ((alpha : ℂ) + t * I) *
              (x : ℂ) ^ ((alpha : ℂ) + t * I) /
                ((alpha : ℂ) + t * I)) -
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          (∫ t in -U..U,
            LSeries a ((alpha : ℂ) + t * I) *
              (1 : ℂ) ^ ((alpha : ℂ) + t * I) /
                ((alpha : ℂ) + t * I))
  rw [hintegral]
  ring

private lemma dirichletPerronStarredSum_twistVonMangoldt_eq
    {q x : ℕ} (chi : DirichletCharacter ℂ q) (hx : 0 < x) :
    twistedChebyshevSum x q chi =
      dirichletPerronStarredSum (twistVonMangoldt chi) x +
        (1 / 2 : ℂ) * twistVonMangoldt chi x := by
  rw [twistedChebyshevSum, dirichletPerronStarredSum]
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hx.ne')]
  simp only [twistVonMangoldt, Pi.mul_apply]
  ring

@[simp]
private lemma dirichletPerronStarredSum_twistVonMangoldt_one
    {q : ℕ} (chi : DirichletCharacter ℂ q) :
    dirichletPerronStarredSum (twistVonMangoldt chi) 1 = 0 := by
  simp [dirichletPerronStarredSum, twistVonMangoldt,
    ArithmeticFunction.vonMangoldt_apply_one]

@[simp]
private lemma dirichletPerronNearMass_twistVonMangoldt_one
    {q : ℕ} (chi : DirichletCharacter ℂ q) (U : ℝ) :
    dirichletPerronNearMass (twistVonMangoldt chi) 1 U = 0 := by
  rw [dirichletPerronNearMass]
  have hzero :
      (fun n : ℕ => ‖twistVonMangoldt chi n‖ *
        dirichletPerronNearError 1 U n) = fun _ => 0 := by
    funext n
    rw [dirichletPerronNearError]
    split_ifs with h
    · norm_num at h
      have hnUpper : n ≤ 1 := by exact_mod_cast h.2.2.1
      have hn : n = 1 := by omega
      exact (h.2.2.2 hn).elim
    · simp
  rw [hzero, tsum_zero]

private lemma rpow_perronAbscissa_le_three_mul
    {x : ℝ} (hx : 1 < x) :
    x ^ (1 + 1 / Real.log x) ≤ 3 * x := by
  have hxPos : 0 < x := zero_lt_one.trans hx
  have hxNe : x ≠ 1 := hx.ne'
  rw [Real.rpow_add hxPos, Real.rpow_one, one_div,
    Real.rpow_inv_log hxPos hxNe]
  nlinarith [Real.exp_one_lt_three]

private lemma norm_half_twistVonMangoldt_le_log
    {q x : ℕ} (chi : DirichletCharacter ℂ q) :
    ‖(1 / 2 : ℂ) * twistVonMangoldt chi x‖ ≤ Real.log x := by
  have hcoeff : ‖twistVonMangoldt chi x‖ ≤
      ArithmeticFunction.vonMangoldt x := by
    simp only [twistVonMangoldt, Pi.mul_apply, norm_mul]
    rw [Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    simpa using mul_le_mul_of_nonneg_right
      (chi.norm_le_one (x : ZMod q))
      ArithmeticFunction.vonMangoldt_nonneg
  calc
    ‖(1 / 2 : ℂ) * twistVonMangoldt chi x‖ =
        (1 / 2 : ℝ) * ‖twistVonMangoldt chi x‖ := by
      rw [norm_mul, norm_div, norm_one]
      norm_num
    _ ≤ ArithmeticFunction.vonMangoldt x := by
      have hv : 0 ≤ ArithmeticFunction.vonMangoldt x :=
        ArithmeticFunction.vonMangoldt_nonneg
      calc
        (1 / 2 : ℝ) * ‖twistVonMangoldt chi x‖ ≤
            (1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt x :=
          mul_le_mul_of_nonneg_left hcoeff (by norm_num)
        _ ≤ ArithmeticFunction.vonMangoldt x := by nlinarith
    _ ≤ Real.log x := ArithmeticFunction.vonMangoldt_le_log

/-- The source-shaped modified Perron estimate before any relation between
the cutoff and integration height is imposed. -/
theorem
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaNormalizedRightEdge_le_raw :
    ∃ P : ℕ, 1 ≤ P ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q)
        (x : ℕ) (U : ℝ),
          4 ≤ x → 2 ≤ U →
            ‖twistedChebyshevSum x q chi -
              dirichletExplicitFormulaNormalizedRightEdge chi x U‖ ≤
              P * ((x : ℝ) * Real.log x ^ 2 / U + Real.log x) := by
  rcases exists_nat_dirichletPerronCoefficientMass_twist_vonMangoldt_le with
    ⟨B, hB, hmass⟩
  let P : ℕ := 128 * (B + 1)
  refine ⟨P, by dsimp [P]; omega, ?_⟩
  intro q _ chi x U hx hU
  let a : ℕ → ℂ := twistVonMangoldt chi
  let alpha : ℝ := 1 + 1 / Real.log x
  let A : ℝ := (x : ℝ) * Real.log x ^ 2 / U
  let L : ℝ := Real.log x
  have hxPos : 0 < x := by omega
  have hxReal : (0 : ℝ) < x := by exact_mod_cast hxPos
  have hxOne : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlogOne : (1 : ℝ) ≤ L := by
    dsimp [L]
    have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    calc
      (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
      _ = Real.log 4 := Real.log_four_eq.symm
      _ ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hlogPos : 0 < L := zero_lt_one.trans_le hlogOne
  have halphaOne : 1 < alpha := by
    dsimp [alpha, L] at *
    have : 0 < 1 / Real.log x := by positivity
    linarith
  have halpha : 0 < alpha := zero_lt_one.trans halphaOne
  have halphaTwo : alpha ≤ 2 := by
    dsimp [alpha, L] at *
    have hinv : 1 / Real.log x ≤ 1 :=
      (div_le_one hlogPos).2 hlogOne
    linarith
  have hUPos : 0 < U := zero_lt_two.trans_le hU
  have hsum : LSeriesSummable a (alpha : ℂ) := by
    simpa [a, twistVonMangoldt] using
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi halphaOne
  have hmassBound : dirichletPerronCoefficientMass a alpha ≤ B * L := by
    simpa [a, alpha, L, twistVonMangoldt] using hmass chi hx
  have hmassNonneg : 0 ≤ dirichletPerronCoefficientMass a alpha :=
    tsum_nonneg fun _ => norm_nonneg _
  have hnearBound : dirichletPerronNearMass a x U ≤ 32 * A := by
    have hnear :=
      dirichletPerronNearMass_twist_vonMangoldt_le chi hx hUPos
    change dirichletPerronNearMass a x U ≤ 32 * A
    calc
      dirichletPerronNearMass a x U ≤
          32 * (x : ℝ) * Real.log x ^ 2 / U := by
        simpa [a, twistVonMangoldt] using hnear
      _ = 32 * A := by dsimp [A]; ring
  have hxPerron := norm_dirichletPerronStarredSum_sub_integral_le
    hsum hxPos halpha halphaTwo hUPos
  have hxPow : (x : ℝ) ^ alpha ≤ 3 * x := by
    simpa [alpha] using rpow_perronAbscissa_le_three_mul hxOne
  have hfactor : 32 * (x : ℝ) ^ alpha / U ≤ 96 * x / U := by
    exact div_le_div_of_nonneg_right
      (by nlinarith [hxPow]) hUPos.le
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hmassTerm :
      (32 * (x : ℝ) ^ alpha / U) *
          dirichletPerronCoefficientMass a alpha ≤
        96 * B * A := by
    calc
      (32 * (x : ℝ) ^ alpha / U) *
          dirichletPerronCoefficientMass a alpha ≤
          (96 * (x : ℝ) / U) * (B * L) :=
        mul_le_mul hfactor hmassBound hmassNonneg (by positivity)
      _ = 96 * B * ((x : ℝ) * L / U) := by ring
      _ ≤ 96 * B * ((x : ℝ) * L ^ 2 / U) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLsq hxReal.le) hUPos.le
      _ = 96 * B * A := by rfl
  have hxError :
      ‖dirichletPerronStarredSum a x -
          dirichletPerronIntegral a x alpha U‖ ≤
        (32 + 96 * B) * A := by
    exact hxPerron.trans <| calc
      dirichletPerronNearMass a x U +
          (32 * (x : ℝ) ^ alpha / U) *
            dirichletPerronCoefficientMass a alpha ≤
          32 * A + 96 * B * A := add_le_add hnearBound hmassTerm
      _ = (32 + 96 * B) * A := by ring
  have hbasePerron := norm_dirichletPerronStarredSum_sub_integral_le
    (x := 1) hsum one_pos halpha halphaTwo hUPos
  have hbaseError :
      ‖dirichletPerronIntegral a 1 alpha U‖ ≤ 16 * B * L := by
    have hfactorOne : (32 : ℝ) / U ≤ 16 := by
      rw [div_le_iff₀ hUPos]
      nlinarith
    have hraw :
        ‖dirichletPerronIntegral a 1 alpha U‖ ≤
          (32 / U) * dirichletPerronCoefficientMass a alpha := by
      simpa [a, Real.one_rpow] using hbasePerron
    exact hraw.trans <| calc
      (32 / U) * dirichletPerronCoefficientMass a alpha ≤
          16 * (B * L) :=
        mul_le_mul hfactorOne hmassBound hmassNonneg (by norm_num)
      _ = 16 * B * L := by ring
  have hstar := dirichletPerronStarredSum_twistVonMangoldt_eq chi hxPos
  have hright :=
    dirichletExplicitFormulaNormalizedRightEdge_eq_rawPerron_sub_baseOne
      (U := U) chi hxOne
  have hendpoint := norm_half_twistVonMangoldt_le_log (x := x) chi
  have hdecomp :
      twistedChebyshevSum x q chi -
          dirichletExplicitFormulaNormalizedRightEdge chi x U =
        (1 / 2 : ℂ) * a x +
          (dirichletPerronStarredSum a x -
            dirichletPerronIntegral a x alpha U) +
          dirichletPerronIntegral a 1 alpha U := by
    rw [hright, hstar]
    dsimp [a, alpha, twistVonMangoldt]
    ring
  have hA : 0 ≤ A := by dsimp [A, L]; positivity
  have hcoeffA : (32 : ℝ) + 96 * B ≤ P := by
    dsimp [P]
    push_cast
    nlinarith [show (1 : ℝ) ≤ B by exact_mod_cast hB]
  have hcoeffL : (1 : ℝ) + 16 * B ≤ P := by
    dsimp [P]
    push_cast
    nlinarith [show (1 : ℝ) ≤ B by exact_mod_cast hB]
  rw [hdecomp]
  calc
    ‖(1 / 2 : ℂ) * a x +
        (dirichletPerronStarredSum a x -
          dirichletPerronIntegral a x alpha U) +
        dirichletPerronIntegral a 1 alpha U‖ ≤
      ‖(1 / 2 : ℂ) * a x‖ +
        ‖dirichletPerronStarredSum a x -
          dirichletPerronIntegral a x alpha U‖ +
        ‖dirichletPerronIntegral a 1 alpha U‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ L + (32 + 96 * B) * A + 16 * B * L :=
      add_le_add (add_le_add (by simpa [a, L] using hendpoint) hxError)
        hbaseError
    _ = (32 + 96 * B) * A + (1 + 16 * B) * L := by ring
    _ ≤ P * A + P * L :=
      add_le_add (mul_le_mul_of_nonneg_right hcoeffA hA)
        (mul_le_mul_of_nonneg_right hcoeffL hlogPos.le)
    _ = (P : ℝ) *
        ((x : ℝ) * Real.log x ^ 2 / U + Real.log x) := by
      dsimp [A, L]
      ring

/-- At a selected height `U` above the requested `T`, both terms of the raw
Perron error are absorbed by the explicit-formula error scale. -/
theorem
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaNormalizedRightEdge_le :
    ∃ P : ℕ, 1 ≤ P ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q)
        (x : ℕ) (T U : ℝ),
          4 ≤ x → 2 ≤ T → T ≤ x → U ∈ Set.Icc T (T + 1) →
            ‖twistedChebyshevSum x q chi -
              dirichletExplicitFormulaNormalizedRightEdge chi x U‖ ≤
              P * dirichletExplicitFormulaErrorScale x q T := by
  rcases
      exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaNormalizedRightEdge_le_raw
    with ⟨P, hP, hraw⟩
  refine ⟨2 * P, by omega, ?_⟩
  intro q _ chi x T U hx hT hTx hU
  have hUtwo : 2 ≤ U := hT.trans hU.1
  have hrawBound := hraw q chi x U hx hUtwo
  have hxPos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hTPos : 0 < T := zero_lt_two.trans_le hT
  have hUPos : 0 < U := hTPos.trans_le hU.1
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxProduct : (x : ℝ) ≤ (x : ℝ) * q := by
    simpa using mul_le_mul_of_nonneg_left hqOne hxPos.le
  have hlog : Real.log x ≤ Real.log ((x : ℝ) * q) :=
    Real.log_le_log hxPos hxProduct
  have hlogOne : (1 : ℝ) ≤ Real.log x := by
    have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    calc
      (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
      _ = Real.log 4 := Real.log_four_eq.symm
      _ ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hlogProductOne :
      (1 : ℝ) ≤ Real.log ((x : ℝ) * q) := hlogOne.trans hlog
  have hlogSq : Real.log x ^ 2 ≤
      Real.log ((x : ℝ) * q) ^ 2 := by
    nlinarith
  let E : ℝ := dirichletExplicitFormulaErrorScale x q T
  have hE : 0 ≤ E := by
    dsimp [E, dirichletExplicitFormulaErrorScale]
    positivity
  have hreciprocal :
      (x : ℝ) * Real.log x ^ 2 / U ≤ E := by
    calc
      (x : ℝ) * Real.log x ^ 2 / U ≤
          (x : ℝ) * Real.log x ^ 2 / T :=
        div_le_div_of_nonneg_left (by positivity) hTPos hU.1
      _ ≤ (x : ℝ) * Real.log ((x : ℝ) * q) ^ 2 / T :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogSq hxPos.le) hTPos.le
      _ = E := by rfl
  have hstandalone : Real.log x ≤ E := by
    have hxT : (1 : ℝ) ≤ (x : ℝ) / T :=
      (le_div_iff₀ hTPos).2 (by simpa using hTx)
    have hlogLeSquare : Real.log x ≤
        Real.log ((x : ℝ) * q) ^ 2 := by
      nlinarith
    calc
      Real.log x ≤ Real.log ((x : ℝ) * q) ^ 2 := hlogLeSquare
      _ = 1 * Real.log ((x : ℝ) * q) ^ 2 := by ring
      _ ≤ ((x : ℝ) / T) *
          Real.log ((x : ℝ) * q) ^ 2 :=
        mul_le_mul_of_nonneg_right hxT (sq_nonneg _)
      _ = E := by
        dsimp [E, dirichletExplicitFormulaErrorScale]
        ring
  exact hrawBound.trans <| calc
    (P : ℝ) *
        ((x : ℝ) * Real.log x ^ 2 / U + Real.log x) ≤
        (P : ℝ) * (E + E) :=
      mul_le_mul_of_nonneg_left (add_le_add hreciprocal hstandalone)
        (by positivity)
    _ = ((2 * P : ℕ) : ℝ) * E := by
      push_cast
      ring

end


end BoundedGaps.Maynard
