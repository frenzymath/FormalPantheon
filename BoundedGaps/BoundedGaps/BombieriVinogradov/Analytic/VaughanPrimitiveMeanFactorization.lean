import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanPowers
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanAssembly

/-!
# Factorization of the Vaughan primitive mean majorant

This file factors the five-term majorant from `SEM-459` into the coefficient,
algebraic, and logarithmic scales used immediately after Akbary--Hambrook
equation (6.15). It does not choose the low- or high-range cutoff parameters.

Source: `AkbaryHambrook2013v2`, Section 6, printed pp. 23--24. Semantic
review: `SEM-460`.
-/

namespace BoundedGaps.Maynard

noncomputable section

/-- A safe common coefficient for the five terms in the primitive-mean
majorant. Unlike the source's numerical `c4`, this retains the generic proved
Chebyshev coefficient `A`. -/
noncomputable def vaughanPrimitiveMeanCoefficient (A : ℝ) : ℝ :=
  max A (max (akbaryHambrookC3 / Real.log 2)
    (vaughanFourthBlockConstant A / Real.log 2))

/-- The logarithmic coefficient obtained from the low-range cutoff choice. -/
noncomputable def vaughanPrimitiveMeanLowLogCoefficient : ℝ :=
  2 * (7 / 6 : ℝ) * Real.sqrt (7 / 6 : ℝ) *
    (1 / 3 + 3 / (2 * Real.log 2))

/-- The logarithmic coefficient obtained from the high-range cutoff choice. -/
noncomputable def vaughanPrimitiveMeanHighLogCoefficient : ℝ :=
  2 * (4 / 3 : ℝ) * Real.sqrt (4 / 3 : ℝ) *
    (1 / 3 + 3 / (2 * Real.log 2))

/-- The common coefficient in the equation-(1.1)-shaped bound. -/
noncomputable def vaughanPrimitiveMeanEquationOneOneConstant (A : ℝ) : ℝ :=
  vaughanPrimitiveMeanCoefficient A *
    vaughanPrimitiveMeanHighLogCoefficient

/-- The exact sum of the five coefficient-free algebraic bases in the
`SEM-459` majorant. -/
noncomputable def vaughanPrimitiveMeanAlgebraicScale
    (U V : ℝ) (x : ℕ) (q : ℝ) : ℝ :=
  U * q ^ 2 +
    ((x : ℝ) + q ^ 2 * Real.sqrt q * V) +
    ((x : ℝ) + q ^ 2 * Real.sqrt q * U) +
    ((x : ℝ) + q * Real.sqrt ((x : ℝ) * U * V) +
      Real.sqrt 2 * q * (x : ℝ) / Real.sqrt U +
      q ^ 2 * Real.sqrt (x : ℝ)) +
    ((x : ℝ) + q * (x : ℝ) / Real.sqrt V +
      Real.sqrt 2 * q * (x : ℝ) / Real.sqrt U +
      q ^ 2 * Real.sqrt (x : ℝ))

/-- The maximum of the four exact logarithmic factors in the `SEM-459`
majorant. The fourth entry retains the totalized scale logarithm from
`SEM-458`. -/
noncomputable def vaughanPrimitiveMeanLogScale
    (U V : ℝ) (x : ℕ) : ℝ :=
  max ((Real.log ((x : ℝ) * V)) ^ 2)
    (max ((Real.log ((x : ℝ) * U)) ^ 2)
      (max ((Real.log (2 * U * V)) ^ 2 * Real.log (4 * (x : ℝ)))
        (vaughanFourthScaleLog V x *
          Real.sqrt (vaughanFourthScaleLog V x) *
          Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ)))))

theorem vaughanPrimitiveMeanCoefficient_nonneg (A : ℝ) :
    0 ≤ vaughanPrimitiveMeanCoefficient A := by
  have hc3 : 0 ≤ akbaryHambrookC3 / Real.log 2 := by
    positivity [akbaryHambrookC3_pos]
  exact hc3.trans ((le_max_left _ _).trans (le_max_right _ _))

theorem self_le_vaughanPrimitiveMeanCoefficient (A : ℝ) :
    A ≤ vaughanPrimitiveMeanCoefficient A :=
  le_max_left _ _

theorem akbaryHambrookC3_div_log_two_le_vaughanPrimitiveMeanCoefficient
    (A : ℝ) :
    akbaryHambrookC3 / Real.log 2 ≤
      vaughanPrimitiveMeanCoefficient A :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem vaughanFourthBlockConstant_div_log_two_le_vaughanPrimitiveMeanCoefficient
    (A : ℝ) :
    vaughanFourthBlockConstant A / Real.log 2 ≤
      vaughanPrimitiveMeanCoefficient A :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem one_le_vaughanPrimitiveMeanCoefficient
    {A : ℝ} (hA : 1 ≤ A) :
    1 ≤ vaughanPrimitiveMeanCoefficient A :=
  hA.trans (self_le_vaughanPrimitiveMeanCoefficient A)

theorem vaughanPrimitiveMeanLowLogCoefficient_pos :
    0 < vaughanPrimitiveMeanLowLogCoefficient := by
  unfold vaughanPrimitiveMeanLowLogCoefficient
  positivity

theorem vaughanPrimitiveMeanHighLogCoefficient_pos :
    0 < vaughanPrimitiveMeanHighLogCoefficient := by
  unfold vaughanPrimitiveMeanHighLogCoefficient
  positivity

theorem vaughanPrimitiveMeanEquationOneOneConstant_nonneg (A : ℝ) :
    0 ≤ vaughanPrimitiveMeanEquationOneOneConstant A := by
  unfold vaughanPrimitiveMeanEquationOneOneConstant
  exact mul_nonneg (vaughanPrimitiveMeanCoefficient_nonneg A)
    vaughanPrimitiveMeanHighLogCoefficient_pos.le

theorem vaughanPrimitiveMeanAlgebraicScale_nonneg
    {U V q : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hq : 0 ≤ q) (x : ℕ) :
    0 ≤ vaughanPrimitiveMeanAlgebraicScale U V x q := by
  unfold vaughanPrimitiveMeanAlgebraicScale
  positivity

theorem vaughanPrimitiveMeanLogScale_nonneg (U V : ℝ) (x : ℕ) :
    0 ≤ vaughanPrimitiveMeanLogScale U V x := by
  exact (sq_nonneg _).trans (le_max_left _ _)

theorem vaughanPrimitiveMeanLogScale_first_le (U V : ℝ) (x : ℕ) :
    Real.log ((x : ℝ) * V) ^ 2 ≤ vaughanPrimitiveMeanLogScale U V x :=
  le_max_left _ _

theorem vaughanPrimitiveMeanLogScale_second_le (U V : ℝ) (x : ℕ) :
    Real.log ((x : ℝ) * U) ^ 2 ≤ vaughanPrimitiveMeanLogScale U V x :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem vaughanPrimitiveMeanLogScale_third_le (U V : ℝ) (x : ℕ) :
    Real.log (2 * U * V) ^ 2 * Real.log (4 * (x : ℝ)) ≤
      vaughanPrimitiveMeanLogScale U V x :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem vaughanPrimitiveMeanLogScale_fourth_le (U V : ℝ) (x : ℕ) :
    vaughanFourthScaleLog V x * Real.sqrt (vaughanFourthScaleLog V x) *
        Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ)) ≤
      vaughanPrimitiveMeanLogScale U V x :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem one_le_vaughanPrimitiveMeanLogScale
    {U V : ℝ} {x : ℕ} (hx : 4 ≤ x) (hV : 1 ≤ V) :
    1 ≤ vaughanPrimitiveMeanLogScale U V x := by
  have hx0 : 0 ≤ (x : ℝ) := by positivity
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hxV : (x : ℝ) ≤ (x : ℝ) * V := by
    calc
      (x : ℝ) = (x : ℝ) * 1 := by ring
      _ ≤ (x : ℝ) * V := mul_le_mul_of_nonneg_left hV hx0
  have hlog : 1 ≤ Real.log ((x : ℝ) * V) :=
    (one_le_log_natCast hx).trans (Real.log_le_log hxpos hxV)
  have hsq : 1 ≤ Real.log ((x : ℝ) * V) ^ 2 := by nlinarith
  exact hsq.trans (vaughanPrimitiveMeanLogScale_first_le U V x)

/-- Factor the five terms of the SEM-459 majorant through their common
coefficient and logarithmic envelopes. -/
theorem vaughanPrimitiveMeanMajorant_le_coefficient_mul_scales
    {A U V : ℝ} {x Q : ℕ}
    (hA : 1 ≤ A) (hx : 4 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    vaughanPrimitiveMeanMajorant A U V x Q ≤
      vaughanPrimitiveMeanCoefficient A *
        vaughanPrimitiveMeanAlgebraicScale U V x (Q : ℝ) *
          vaughanPrimitiveMeanLogScale U V x := by
  let q : ℝ := Q
  let B1 : ℝ := U * q ^ 2
  let B2 : ℝ := (x : ℝ) + q ^ 2 * Real.sqrt q * V
  let B3 : ℝ := (x : ℝ) + q ^ 2 * Real.sqrt q * U
  let B4 : ℝ :=
    (x : ℝ) + q * Real.sqrt ((x : ℝ) * U * V) +
      Real.sqrt 2 * q * (x : ℝ) / Real.sqrt U +
      q ^ 2 * Real.sqrt (x : ℝ)
  let B5 : ℝ :=
    (x : ℝ) + q * (x : ℝ) / Real.sqrt V +
      Real.sqrt 2 * q * (x : ℝ) / Real.sqrt U +
      q ^ 2 * Real.sqrt (x : ℝ)
  let L1 : ℝ := Real.log ((x : ℝ) * V) ^ 2
  let L2 : ℝ := Real.log ((x : ℝ) * U) ^ 2
  let L3 : ℝ := Real.log (2 * U * V) ^ 2 * Real.log (4 * (x : ℝ))
  let L4 : ℝ :=
    vaughanFourthScaleLog V x * Real.sqrt (vaughanFourthScaleLog V x) *
      Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ))
  let C : ℝ := vaughanPrimitiveMeanCoefficient A
  let L : ℝ := vaughanPrimitiveMeanLogScale U V x
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hC0 : 0 ≤ C := vaughanPrimitiveMeanCoefficient_nonneg A
  have hCone : 1 ≤ C := one_le_vaughanPrimitiveMeanCoefficient hA
  have hL0 : 0 ≤ L := vaughanPrimitiveMeanLogScale_nonneg U V x
  have hLone : 1 ≤ L := one_le_vaughanPrimitiveMeanLogScale hx hV
  have hlogFourX : 0 ≤ Real.log (4 * (x : ℝ)) := by
    apply Real.log_nonneg
    have hxReal : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    nlinarith
  have hlogExpV : 0 ≤ Real.log (Real.exp 3 * V) := by
    apply Real.log_nonneg
    have hexp : 1 ≤ Real.exp (3 : ℝ) := (Real.one_le_exp_iff).2 (by norm_num)
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp 3 * V :=
        mul_le_mul hexp hV (by norm_num) (Real.exp_pos 3).le
  have hB1 : 0 ≤ B1 := by dsimp only [B1]; positivity
  have hB2 : 0 ≤ B2 := by dsimp only [B2]; positivity
  have hB3 : 0 ≤ B3 := by dsimp only [B3]; positivity
  have hB4 : 0 ≤ B4 := by dsimp only [B4]; positivity
  have hB5 : 0 ≤ B5 := by dsimp only [B5]; positivity
  have hL1 : 0 ≤ L1 := by dsimp only [L1]; positivity
  have hL2 : 0 ≤ L2 := by dsimp only [L2]; positivity
  have hL3 : 0 ≤ L3 := by dsimp only [L3]; positivity
  have hL4 : 0 ≤ L4 := by
    dsimp only [L4]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (vaughanFourthScaleLog_nonneg V x)
          (Real.sqrt_nonneg _)) hlogExpV) hlogFourX
  have hL1L : L1 ≤ L := by
    exact vaughanPrimitiveMeanLogScale_first_le U V x
  have hL2L : L2 ≤ L := by
    exact vaughanPrimitiveMeanLogScale_second_le U V x
  have hL3L : L3 ≤ L := by
    exact vaughanPrimitiveMeanLogScale_third_le U V x
  have hL4L : L4 ≤ L := by
    exact vaughanPrimitiveMeanLogScale_fourth_le U V x
  have hterm1 : A * B1 ≤ C * B1 * L := by
    calc
      A * B1 ≤ C * B1 :=
        mul_le_mul_of_nonneg_right
          (self_le_vaughanPrimitiveMeanCoefficient A) hB1
      _ = C * B1 * 1 := by ring
      _ ≤ C * B1 * L :=
        mul_le_mul_of_nonneg_left hLone (mul_nonneg hC0 hB1)
  have hterm2 : B2 * L1 ≤ C * B2 * L := by
    calc
      B2 * L1 ≤ B2 * L := mul_le_mul_of_nonneg_left hL1L hB2
      _ = 1 * (B2 * L) := by ring
      _ ≤ C * (B2 * L) :=
        mul_le_mul_of_nonneg_right hCone (mul_nonneg hB2 hL0)
      _ = C * B2 * L := by ring
  have hterm3 : B3 * L2 ≤ C * B3 * L := by
    calc
      B3 * L2 ≤ B3 * L := mul_le_mul_of_nonneg_left hL2L hB3
      _ = 1 * (B3 * L) := by ring
      _ ≤ C * (B3 * L) :=
        mul_le_mul_of_nonneg_right hCone (mul_nonneg hB3 hL0)
      _ = C * B3 * L := by ring
  have hterm4 :
      akbaryHambrookC3 / Real.log 2 * B4 * L3 ≤ C * B4 * L := by
    calc
      akbaryHambrookC3 / Real.log 2 * B4 * L3 =
          (akbaryHambrookC3 / Real.log 2) * (B4 * L3) := by ring
      _ ≤ C * (B4 * L3) := mul_le_mul_of_nonneg_right
        (akbaryHambrookC3_div_log_two_le_vaughanPrimitiveMeanCoefficient A)
        (mul_nonneg hB4 hL3)
      _ = C * B4 * L3 := by ring
      _ ≤ C * B4 * L :=
        mul_le_mul_of_nonneg_left hL3L (mul_nonneg hC0 hB4)
  have hterm5 :
      vaughanFourthBlockConstant A / Real.log 2 * B5 * L4 ≤
        C * B5 * L := by
    calc
      vaughanFourthBlockConstant A / Real.log 2 * B5 * L4 =
          (vaughanFourthBlockConstant A / Real.log 2) * (B5 * L4) := by ring
      _ ≤ C * (B5 * L4) := mul_le_mul_of_nonneg_right
        (vaughanFourthBlockConstant_div_log_two_le_vaughanPrimitiveMeanCoefficient A)
        (mul_nonneg hB5 hL4)
      _ = C * B5 * L4 := by ring
      _ ≤ C * B5 * L :=
        mul_le_mul_of_nonneg_left hL4L (mul_nonneg hC0 hB5)
  have hmajorant :
      vaughanPrimitiveMeanMajorant A U V x Q =
        A * B1 + B2 * L1 + B3 * L2 +
          akbaryHambrookC3 / Real.log 2 * B4 * L3 +
          vaughanFourthBlockConstant A / Real.log 2 * B5 * L4 := by
    unfold vaughanPrimitiveMeanMajorant
    dsimp only [q, B1, B2, B3, B4, B5, L1, L2, L3, L4]
    ring
  have hscale :
      vaughanPrimitiveMeanAlgebraicScale U V x (Q : ℝ) =
        B1 + B2 + B3 + B4 + B5 := by
    unfold vaughanPrimitiveMeanAlgebraicScale
    dsimp only [q, B1, B2, B3, B4, B5]
  rw [hmajorant, hscale]
  change _ ≤ C * (B1 + B2 + B3 + B4 + B5) * L
  calc
    _ ≤ C * B1 * L + C * B2 * L + C * B3 * L +
        C * B4 * L + C * B5 * L := by linarith
    _ = C * (B1 + B2 + B3 + B4 + B5) * L := by ring

end

end BoundedGaps.Maynard
