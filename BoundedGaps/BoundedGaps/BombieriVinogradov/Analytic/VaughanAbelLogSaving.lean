import BoundedGaps.BombieriVinogradov.Analytic.ElementaryCorrectionAbsorption
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic saving for the Vaughan Abel term

This file bounds SEM-461's four-term Abel envelope at the common cutoff
`floor ((log x) ^ (A + 5))`. It treats only SEM-568's large Abel term; the
small Siegel--Walfisz term and the below-cutoff modulus range remain separate.

Sources: `AkbaryHambrook2013v2`, Theorem 1.3 and Section 7, printed pp. 3 and
24--25, and `Vaughan1980`, p. 113. The constant-40 natural-floor corollary is
project-derived. Semantic review: `SEM-569`.
-/

namespace BoundedGaps.Maynard

noncomputable section

private theorem exists_log_rpow_natCast_le_rpow
    (r s : ℝ) (hs : 0 < s) :
    ∃ X0 : ℕ, 4 ≤ X0 ∧ ∀ x : ℕ, X0 ≤ x →
      Real.rpow (Real.log (x : ℝ)) r ≤ Real.rpow (x : ℝ) s := by
  have hlittle := isLittleO_log_rpow_rpow_atTop r hs
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    hlittle.eventuallyLE
  rw [Filter.eventually_atTop] at hnat
  obtain ⟨N, hN⟩ := hnat
  refine ⟨max 4 N, le_max_left _ _, ?_⟩
  intro x hx
  have hNx : N ≤ x := (le_max_right 4 N).trans hx
  have hx4 : 4 ≤ x := (le_max_left 4 N).trans hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogNonneg : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlogNonneg r),
    abs_of_nonneg (Real.rpow_nonneg hxpos.le s)] using hN x hNx

private theorem vaughanPrimitiveMeanEquationOneTwoLogPower_le_fifth
    {x : ℕ} (hx : 4 ≤ x) :
    vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
      Real.log (x : ℝ) ^ 5 := by
  have hlog := one_le_log_natCast hx
  have hsqrt : Real.sqrt (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hlog)
  unfold vaughanPrimitiveMeanEquationOneTwoLogPower
  calc
    Real.log (x : ℝ) ^ 4 * Real.sqrt (Real.log (x : ℝ)) ≤
        Real.log (x : ℝ) ^ 4 * Real.log (x : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = Real.log (x : ℝ) ^ 5 := by ring

private theorem vaughanCubeRoot_sq_eq_rpow_two_thirds
    {x : ℕ} (hx : 1 ≤ x) :
    vaughanCubeRoot x ^ 2 = Real.rpow (x : ℝ) (2 / 3 : ℝ) := by
  have hx0 : 0 ≤ (x : ℝ) := by positivity
  unfold vaughanCubeRoot
  calc
    Real.rpow (x : ℝ) (1 / 3 : ℝ) ^ 2 =
        Real.rpow (Real.rpow (x : ℝ) (1 / 3 : ℝ)) (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = Real.rpow (x : ℝ) ((1 / 3 : ℝ) * 2) :=
      (Real.rpow_mul hx0 (1 / 3 : ℝ) 2).symm
    _ = Real.rpow (x : ℝ) (2 / 3 : ℝ) := by norm_num

private theorem sqrt_sqrt_natCast_eq_rpow_one_fourth
    {x : ℕ} (hx : 1 ≤ x) :
    Real.sqrt (Real.sqrt (x : ℝ)) =
      Real.rpow (x : ℝ) (1 / 4 : ℝ) := by
  have hx0 : 0 ≤ (x : ℝ) := by positivity
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow (x : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) =
        Real.rpow (x : ℝ) ((1 / 2 : ℝ) * (1 / 2 : ℝ)) :=
      (Real.rpow_mul hx0 (1 / 2 : ℝ) (1 / 2 : ℝ)).symm
    _ = Real.rpow (x : ℝ) (1 / 4 : ℝ) := by norm_num

private theorem vaughanCubeRoot_sq_mul_sqrt_le_rpow_eleven_twelfths
    {x Q : ℕ} (hx : 1 ≤ x)
    (hQ : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    vaughanCubeRoot x ^ 2 * Real.sqrt (Q : ℝ) ≤
      Real.rpow (x : ℝ) (11 / 12 : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hsqrtQ : Real.sqrt (Q : ℝ) ≤ Real.sqrt (Real.sqrt (x : ℝ)) :=
    Real.sqrt_le_sqrt hQ
  rw [sqrt_sqrt_natCast_eq_rpow_one_fourth hx] at hsqrtQ
  rw [vaughanCubeRoot_sq_eq_rpow_two_thirds hx]
  calc
    Real.rpow (x : ℝ) (2 / 3 : ℝ) * Real.sqrt (Q : ℝ) ≤
        Real.rpow (x : ℝ) (2 / 3 : ℝ) *
          Real.rpow (x : ℝ) (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrtQ
        (Real.rpow_nonneg (Nat.cast_nonneg x) _)
    _ = Real.rpow (x : ℝ) ((2 / 3 : ℝ) + (1 / 4 : ℝ)) :=
      (Real.rpow_add hxpos (2 / 3 : ℝ) (1 / 4 : ℝ)).symm
    _ = Real.rpow (x : ℝ) (11 / 12 : ℝ) := by norm_num

private theorem sqrt_mul_vaughanCubeRoot_eq_rpow_five_sixths
    {x : ℕ} (hx : 1 ≤ x) :
    Real.sqrt (x : ℝ) * vaughanCubeRoot x =
      Real.rpow (x : ℝ) (5 / 6 : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  unfold vaughanCubeRoot
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (x : ℝ) (1 / 2 : ℝ) *
        Real.rpow (x : ℝ) (1 / 3 : ℝ) =
      Real.rpow (x : ℝ) ((1 / 2 : ℝ) + (1 / 3 : ℝ)) :=
        (Real.rpow_add hxpos (1 / 2 : ℝ) (1 / 3 : ℝ)).symm
    _ = Real.rpow (x : ℝ) (5 / 6 : ℝ) := by norm_num

/-- On the shared `A+5` logarithmic range, the complete Vaughan Abel envelope
and its exact equation-(1.2) logarithmic power have an `A`th log saving. -/
theorem exists_vaughanPrimitiveMeanAbelEnvelope_mul_logPower_le_logSaving
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ∀ Q : ℕ, siegelWalfiszConductorCutoff (A + 5) x ≤ Q →
          (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) (A + 5) →
            vaughanPrimitiveMeanAbelEnvelope x
                (siegelWalfiszConductorCutoff (A + 5) x : ℝ) Q *
                vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
              40 * (x : ℝ) /
                Real.rpow (Real.log (x : ℝ)) A := by
  obtain ⟨Xthird, hXthird, hthirdGrowth⟩ :=
    exists_log_rpow_natCast_le_rpow (A + 5) (1 / 12) (by norm_num)
  obtain ⟨Xfourth, hXfourth, hfourthGrowth⟩ :=
    exists_log_rpow_natCast_le_rpow (A + 6) (1 / 6) (by norm_num)
  refine ⟨max Xthird Xfourth,
    hXthird.trans (le_max_left Xthird Xfourth), ?_⟩
  intro x hx Q hRQ hQrange
  have hxThird : Xthird ≤ x :=
    (le_max_left Xthird Xfourth).trans hx
  have hxFourth : Xfourth ≤ x :=
    (le_max_right Xthird Xfourth).trans hx
  have hx4 : 4 ≤ x := hXthird.trans hxThird
  have hxone : 1 ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogOne : 1 ≤ Real.log (x : ℝ) := one_le_log_natCast hx4
  have hlogPos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlogOne
  have hApFive : 0 < A + 5 := by linarith
  have hApFiveNonneg : 0 ≤ A + 5 := hApFive.le
  have hscaleOne :
      1 ≤ Real.rpow (Real.log (x : ℝ)) (A + 5) :=
    Real.one_le_rpow hlogOne hApFiveNonneg
  have hscalePos :
      0 < Real.rpow (Real.log (x : ℝ)) (A + 5) :=
    Real.rpow_pos_of_pos hlogPos _
  have hsavePos : 0 < Real.rpow (Real.log (x : ℝ)) A :=
    Real.rpow_pos_of_pos hlogPos _
  have hRone : 1 ≤ siegelWalfiszConductorCutoff (A + 5) x :=
    one_le_siegelWalfiszConductorCutoff hApFive hx4
  have hRoneReal :
      (1 : ℝ) ≤ (siegelWalfiszConductorCutoff (A + 5) x : ℝ) := by
    exact_mod_cast hRone
  have hRpos :
      (0 : ℝ) < (siegelWalfiszConductorCutoff (A + 5) x : ℝ) :=
    zero_lt_one.trans_le hRoneReal
  have hRQReal :
      (siegelWalfiszConductorCutoff (A + 5) x : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast hRQ
  have hQone : (1 : ℝ) ≤ (Q : ℝ) := hRoneReal.trans hRQReal
  have hQpos : (0 : ℝ) < (Q : ℝ) := zero_lt_one.trans_le hQone
  have hQnonneg : (0 : ℝ) ≤ (Q : ℝ) := hQpos.le
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ) := by
    exact hQrange.trans (div_le_self (Real.sqrt_nonneg _) hscaleOne)
  have hlogPowerNonneg :=
    vaughanPrimitiveMeanEquationOneTwoLogPower_nonneg x
  have hlogPowerLe :=
    vaughanPrimitiveMeanEquationOneTwoLogPower_le_fifth hx4
  have hrpowFive :
      Real.rpow (Real.log (x : ℝ)) (5 : ℝ) =
        Real.log (x : ℝ) ^ 5 := by
    exact Real.rpow_natCast (Real.log (x : ℝ)) 5
  have hrpowSix :
      Real.rpow (Real.log (x : ℝ)) (6 : ℝ) =
        Real.log (x : ℝ) ^ 6 := by
    exact Real.rpow_natCast (Real.log (x : ℝ)) 6
  have hscaleSplit :
      Real.rpow (Real.log (x : ℝ)) (A + 5) =
        Real.rpow (Real.log (x : ℝ)) A * Real.log (x : ℝ) ^ 5 := by
    calc
      Real.rpow (Real.log (x : ℝ)) (A + 5) =
          Real.rpow (Real.log (x : ℝ)) A *
            Real.rpow (Real.log (x : ℝ)) (5 : ℝ) :=
        Real.rpow_add hlogPos A 5
      _ = Real.rpow (Real.log (x : ℝ)) A *
          Real.log (x : ℝ) ^ 5 := by rw [hrpowFive]
  have hscaleSixSplit :
      Real.rpow (Real.log (x : ℝ)) (A + 6) =
        Real.rpow (Real.log (x : ℝ)) A * Real.log (x : ℝ) ^ 6 := by
    calc
      Real.rpow (Real.log (x : ℝ)) (A + 6) =
          Real.rpow (Real.log (x : ℝ)) A *
            Real.rpow (Real.log (x : ℝ)) (6 : ℝ) :=
        Real.rpow_add hlogPos A 6
      _ = Real.rpow (Real.log (x : ℝ)) A *
          Real.log (x : ℝ) ^ 6 := by rw [hrpowSix]
  have hfloor :
      Real.rpow (Real.log (x : ℝ)) (A + 5) / 2 <
        (siegelWalfiszConductorCutoff (A + 5) x : ℝ) := by
    change Real.rpow (Real.log (x : ℝ)) (A + 5) / 2 <
      ((Nat.floor (Real.rpow (Real.log (x : ℝ)) (A + 5)) : ℕ) : ℝ)
    exact Nat.div_two_lt_floor hscaleOne
  have hlogFifthDivFloor :
      Real.log (x : ℝ) ^ 5 /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) ≤
        2 / Real.rpow (Real.log (x : ℝ)) A := by
    apply (div_le_div_iff₀ hRpos hsavePos).2
    rw [mul_comm, ← hscaleSplit]
    nlinarith
  have hfirst :
      (4 * (x : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
        8 * ((x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
    calc
      (4 * (x : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
        (4 * (x : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) *
            Real.log (x : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left hlogPowerLe (by positivity)
      _ = 4 * (x : ℝ) *
          (Real.log (x : ℝ) ^ 5 /
            (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) := by ring
      _ ≤ 4 * (x : ℝ) *
          (2 / Real.rpow (Real.log (x : ℝ)) A) :=
        mul_le_mul_of_nonneg_left hlogFifthDivFloor (by positivity)
      _ = 8 * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) := by ring
  have hQScale :
      (Q : ℝ) * Real.rpow (Real.log (x : ℝ)) (A + 5) ≤
        Real.sqrt (x : ℝ) :=
    (le_div_iff₀ hscalePos).1 hQrange
  have hQLogFifth :
      (Q : ℝ) * Real.log (x : ℝ) ^ 5 ≤
        Real.sqrt (x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A := by
    apply (le_div_iff₀ hsavePos).2
    calc
      (Q : ℝ) * Real.log (x : ℝ) ^ 5 *
          Real.rpow (Real.log (x : ℝ)) A =
        (Q : ℝ) * Real.rpow (Real.log (x : ℝ)) (A + 5) := by
          rw [hscaleSplit]
          ring
      _ ≤ Real.sqrt (x : ℝ) := hQScale
  have hsecond :
      (4 * Real.sqrt (x : ℝ) * (Q : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
        4 * ((x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
    calc
      (4 * Real.sqrt (x : ℝ) * (Q : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
        (4 * Real.sqrt (x : ℝ) * (Q : ℝ)) *
          Real.log (x : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left hlogPowerLe (by positivity)
      _ = 4 * Real.sqrt (x : ℝ) *
          ((Q : ℝ) * Real.log (x : ℝ) ^ 5) := by ring
      _ ≤ 4 * Real.sqrt (x : ℝ) *
          (Real.sqrt (x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) A) :=
        mul_le_mul_of_nonneg_left hQLogFifth (by positivity)
      _ = 4 * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) := by
        rw [show 4 * Real.sqrt (x : ℝ) *
            (Real.sqrt (x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) A) =
          4 * (Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ)) /
            Real.rpow (Real.log (x : ℝ)) A by ring,
          Real.mul_self_sqrt hxpos.le]
        ring
  have hthirdPower := hthirdGrowth x hxThird
  have hXElevenAdd :
      Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          Real.rpow (x : ℝ) (1 / 12 : ℝ) = (x : ℝ) := by
    calc
      Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          Real.rpow (x : ℝ) (1 / 12 : ℝ) =
        Real.rpow (x : ℝ) ((11 / 12 : ℝ) + (1 / 12 : ℝ)) :=
          (Real.rpow_add hxpos (11 / 12 : ℝ) (1 / 12 : ℝ)).symm
      _ = (x : ℝ) := by norm_num [Real.rpow_one]
  have hthirdScale :
      Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          Real.log (x : ℝ) ^ 5 ≤
        (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := by
    apply (le_div_iff₀ hsavePos).2
    calc
      Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          Real.log (x : ℝ) ^ 5 *
            Real.rpow (Real.log (x : ℝ)) A =
        Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          Real.rpow (Real.log (x : ℝ)) (A + 5) := by
            rw [hscaleSplit]
            ring
      _ ≤ Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          Real.rpow (x : ℝ) (1 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_left hthirdPower
          (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) := hXElevenAdd
  have hthirdRoot :=
    vaughanCubeRoot_sq_mul_sqrt_le_rpow_eleven_twelfths hxone hQsqrt
  have hthird :
      (18 * vaughanCubeRoot x ^ 2 * Real.sqrt (Q : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
        18 * ((x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
    calc
      (18 * vaughanCubeRoot x ^ 2 * Real.sqrt (Q : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x =
        18 * (vaughanCubeRoot x ^ 2 * Real.sqrt (Q : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by ring
      _ ≤ 18 * Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hthirdRoot (by norm_num))
          hlogPowerNonneg
      _ ≤ 18 * Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          Real.log (x : ℝ) ^ 5 := by
        exact mul_le_mul_of_nonneg_left hlogPowerLe
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hxpos.le _))
      _ = 18 * (Real.rpow (x : ℝ) (11 / 12 : ℝ) *
          Real.log (x : ℝ) ^ 5) := by ring
      _ ≤ 18 * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) :=
        mul_le_mul_of_nonneg_left hthirdScale (by norm_num)
  have hQdivRone :
      (1 : ℝ) ≤ (Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) :=
    (one_le_div hRpos).2 hRQReal
  have hargOne :
      (1 : ℝ) ≤ Real.exp 1 * (Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp 1 * ((Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) :=
        mul_le_mul (Real.one_le_exp (by norm_num)) hQdivRone
          (by norm_num) (Real.exp_pos 1).le
      _ = Real.exp 1 * (Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) := by ring
  have hargPos :
      0 < Real.exp 1 * (Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) :=
    zero_lt_one.trans_le hargOne
  have hargLe :
      Real.exp 1 * (Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) ≤
        Real.exp 1 * Real.sqrt (x : ℝ) := by
    calc
      Real.exp 1 * (Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) =
        Real.exp 1 * ((Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) := by ring
      _ ≤ Real.exp 1 * (Q : ℝ) :=
        mul_le_mul_of_nonneg_left (div_le_self hQnonneg hRoneReal)
          (Real.exp_pos 1).le
      _ ≤ Real.exp 1 * Real.sqrt (x : ℝ) :=
        mul_le_mul_of_nonneg_left hQsqrt (Real.exp_pos 1).le
  have hlogRatio :
      Real.log (Real.exp 1 * (Q : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) ≤
        (5 / 4 : ℝ) * Real.log (x : ℝ) := by
    exact (Real.log_le_log hargPos hargLe).trans
      (log_exp_mul_sqrt_lt_five_fourths_mul_log
        (show (4 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx4)).le
  have hfourthPower := hfourthGrowth x hxFourth
  have hXFiveAdd :
      Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          Real.rpow (x : ℝ) (1 / 6 : ℝ) = (x : ℝ) := by
    calc
      Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          Real.rpow (x : ℝ) (1 / 6 : ℝ) =
        Real.rpow (x : ℝ) ((5 / 6 : ℝ) + (1 / 6 : ℝ)) :=
          (Real.rpow_add hxpos (5 / 6 : ℝ) (1 / 6 : ℝ)).symm
      _ = (x : ℝ) := by norm_num [Real.rpow_one]
  have hfourthScale :
      Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          Real.log (x : ℝ) ^ 6 ≤
        (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := by
    apply (le_div_iff₀ hsavePos).2
    calc
      Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          Real.log (x : ℝ) ^ 6 *
            Real.rpow (Real.log (x : ℝ)) A =
        Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          Real.rpow (Real.log (x : ℝ)) (A + 6) := by
            rw [hscaleSixSplit]
            ring
      _ ≤ Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          Real.rpow (x : ℝ) (1 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_left hfourthPower
          (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) := hXFiveAdd
  have hfourthRoot :=
    sqrt_mul_vaughanCubeRoot_eq_rpow_five_sixths hxone
  have hfourth :
      (5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
          Real.log (Real.exp 1 * (Q : ℝ) /
            (siegelWalfiszConductorCutoff (A + 5) x : ℝ))) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
        (25 / 4 : ℝ) * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) := by
    rw [hfourthRoot]
    have hfiveRootNonneg :
        0 ≤ 5 * Real.rpow (x : ℝ) (5 / 6 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hxpos.le _)
    have hlogStep :
        5 * Real.rpow (x : ℝ) (5 / 6 : ℝ) *
            Real.log (Real.exp 1 * (Q : ℝ) /
              (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) ≤
          5 * Real.rpow (x : ℝ) (5 / 6 : ℝ) *
            ((5 / 4 : ℝ) * Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogRatio hfiveRootNonneg
    have hupperCoefficientNonneg :
        0 ≤ 5 * Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          ((5 / 4 : ℝ) * Real.log (x : ℝ)) := by
      positivity
    calc
      (5 * Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          Real.log (Real.exp 1 * (Q : ℝ) /
            (siegelWalfiszConductorCutoff (A + 5) x : ℝ))) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
        (5 * Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          ((5 / 4 : ℝ) * Real.log (x : ℝ))) *
            vaughanPrimitiveMeanEquationOneTwoLogPower x :=
        mul_le_mul_of_nonneg_right hlogStep hlogPowerNonneg
      _ ≤ (5 * Real.rpow (x : ℝ) (5 / 6 : ℝ) *
          ((5 / 4 : ℝ) * Real.log (x : ℝ))) *
            Real.log (x : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left hlogPowerLe hupperCoefficientNonneg
      _ = (25 / 4 : ℝ) *
          (Real.rpow (x : ℝ) (5 / 6 : ℝ) *
            Real.log (x : ℝ) ^ 6) := by ring
      _ ≤ (25 / 4 : ℝ) * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) :=
        mul_le_mul_of_nonneg_left hfourthScale (by norm_num)
  have htargetNonneg :
      0 ≤ (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := by positivity
  unfold vaughanPrimitiveMeanAbelEnvelope
  calc
    (4 * (x : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) +
        4 * Real.sqrt (x : ℝ) * (Q : ℝ) +
        18 * vaughanCubeRoot x ^ 2 * Real.sqrt (Q : ℝ) +
        5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
          Real.log (Real.exp 1 * (Q : ℝ) /
            (siegelWalfiszConductorCutoff (A + 5) x : ℝ))) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x =
      (4 * (x : ℝ) /
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x +
        (4 * Real.sqrt (x : ℝ) * (Q : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x +
        (18 * vaughanCubeRoot x ^ 2 * Real.sqrt (Q : ℝ)) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x +
        (5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
          Real.log (Real.exp 1 * (Q : ℝ) /
            (siegelWalfiszConductorCutoff (A + 5) x : ℝ))) *
          vaughanPrimitiveMeanEquationOneTwoLogPower x := by ring
    _ ≤ 8 * ((x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) +
        4 * ((x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) +
        18 * ((x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) +
        (25 / 4 : ℝ) * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) := by
      exact add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
    _ ≤ 40 * (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) A := by
      rw [show 40 * (x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A =
        40 * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) by ring]
      nlinarith

end

end BoundedGaps.Maynard
