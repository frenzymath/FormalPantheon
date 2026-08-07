import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanFactorization

/-!
# Logarithmic optimization for the Vaughan primitive mean estimate

This file bounds the four logarithmic factors in the low- and high-parameter
choices after Akbary--Hambrook equation (6.15). The fourth factor is handled
through the totalized scale logarithm from `SEM-458`.

Source: `AkbaryHambrook2013v2`, Section 6, printed pp. 23--24. Semantic
review: `SEM-460`.
-/

namespace BoundedGaps.Maynard

noncomputable section

private theorem log_two_le_half_log_natCast
    {x : ℕ} (hx : 4 ≤ x) :
    Real.log 2 ≤ (1 / 2 : ℝ) * Real.log (x : ℝ) := by
  have hlogFour : Real.log 4 ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hx
  rw [Real.log_four_eq] at hlogFour
  linarith

private theorem log_natCast_mul_cubeRoot_eq
    {x : ℕ} (hx : 1 ≤ x) :
    Real.log ((x : ℝ) * vaughanCubeRoot x) =
      (4 / 3 : ℝ) * Real.log (x : ℝ) := by
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hx)
  have hcpos := vaughanCubeRoot_pos hx
  have hlogCube : Real.log (vaughanCubeRoot x) =
      (1 / 3 : ℝ) * Real.log (x : ℝ) := by
    unfold vaughanCubeRoot
    exact Real.log_rpow hxpos _
  rw [Real.log_mul hxpos.ne' hcpos.ne', hlogCube]
  ring

private theorem log_two_mul_cubeRoot_sq_eq
    {x : ℕ} (hx : 1 ≤ x) :
    Real.log (2 * vaughanCubeRoot x * vaughanCubeRoot x) =
      Real.log 2 + (2 / 3 : ℝ) * Real.log (x : ℝ) := by
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hx)
  have hcpos := vaughanCubeRoot_pos hx
  have hlogCube : Real.log (vaughanCubeRoot x) =
      (1 / 3 : ℝ) * Real.log (x : ℝ) := by
    unfold vaughanCubeRoot
    exact Real.log_rpow hxpos _
  rw [Real.log_mul (mul_ne_zero (by norm_num) hcpos.ne') hcpos.ne',
    Real.log_mul (by norm_num) hcpos.ne', hlogCube]
  ring

private theorem log_two_mul_cubeRoot_sq_le
    {x : ℕ} (hx : 4 ≤ x) :
    Real.log (2 * vaughanCubeRoot x * vaughanCubeRoot x) ≤
      (7 / 6 : ℝ) * Real.log (x : ℝ) := by
  rw [log_two_mul_cubeRoot_sq_eq (by omega : 1 ≤ x)]
  linarith [log_two_le_half_log_natCast hx]

private theorem log_exp_three_mul_cubeRoot_eq
    {x : ℕ} (hx : 1 ≤ x) :
    Real.log (Real.exp 3 * vaughanCubeRoot x) =
      3 + (1 / 3 : ℝ) * Real.log (x : ℝ) := by
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hx)
  have hcpos := vaughanCubeRoot_pos hx
  have hlogCube : Real.log (vaughanCubeRoot x) =
      (1 / 3 : ℝ) * Real.log (x : ℝ) := by
    unfold vaughanCubeRoot
    exact Real.log_rpow hxpos _
  rw [Real.log_mul (Real.exp_ne_zero 3) hcpos.ne', Real.log_exp,
    hlogCube]

private theorem log_exp_three_mul_cubeRoot_le
    {x : ℕ} (hx : 4 ≤ x) :
    Real.log (Real.exp 3 * vaughanCubeRoot x) ≤
      (1 / 3 + 3 / (2 * Real.log 2)) * Real.log (x : ℝ) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio :
      1 ≤ Real.log (x : ℝ) / (2 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    have hlogFour : Real.log 4 ≤ Real.log (x : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hx
    rw [Real.log_four_eq] at hlogFour
    simpa only [one_mul] using hlogFour
  rw [log_exp_three_mul_cubeRoot_eq (by omega : 1 ≤ x)]
  have hthree : (3 : ℝ) ≤
      3 * (Real.log (x : ℝ) / (2 * Real.log 2)) := by
    nlinarith
  calc
    3 + (1 / 3 : ℝ) * Real.log (x : ℝ) ≤
        3 * (Real.log (x : ℝ) / (2 * Real.log 2)) +
          (1 / 3 : ℝ) * Real.log (x : ℝ) := by
      nlinarith [hthree]
    _ = (1 / 3 + 3 / (2 * Real.log 2)) * Real.log (x : ℝ) := by
      field_simp; ring

private theorem log_four_mul_natCast_le
    {x : ℕ} (hx : 4 ≤ x) :
    Real.log (4 * (x : ℝ)) ≤ 2 * Real.log (x : ℝ) := by
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  rw [Real.log_mul (by norm_num) hxpos.ne']
  have hlogFour : Real.log 4 ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hx
  linarith

private theorem eleven_six_le_log_coefficient_base :
    (11 / 6 : ℝ) ≤ 1 / 3 + 3 / (2 * Real.log 2) := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoLe : Real.log 2 ≤ 1 :=
    (le_of_lt Real.log_two_lt_d9).trans (by norm_num)
  have hfrac : (3 / 2 : ℝ) ≤ 3 / (2 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- The source's low logarithmic coefficient is no smaller than `11/3`. -/
private theorem eleven_thirds_le_low_log_coefficient :
    (11 / 3 : ℝ) ≤ vaughanPrimitiveMeanLowLogCoefficient := by
  unfold vaughanPrimitiveMeanLowLogCoefficient
  calc
    (11 / 3 : ℝ) = 2 * 1 * 1 * (11 / 6 : ℝ) := by ring
    _ ≤ 2 * (7 / 6 : ℝ) * Real.sqrt (7 / 6 : ℝ) *
        (1 / 3 + 3 / (2 * Real.log 2)) := by
      gcongr
      · norm_num
      · exact Real.one_le_sqrt.mpr (by norm_num)
      · exact eleven_six_le_log_coefficient_base

private theorem sq_le_log_envelope
    {ell z b C : ℝ} (hell : 1 ≤ ell) (hz0 : 0 ≤ z) (hb0 : 0 ≤ b)
    (hz : z ≤ b * ell) (hcoef : b ^ 2 ≤ C) :
    z ^ 2 ≤ C * (ell ^ 3 * Real.sqrt ell) := by
  have hsqrt : 1 ≤ Real.sqrt ell := Real.one_le_sqrt.mpr hell
  have htail : ell ^ 2 ≤ ell ^ 3 * Real.sqrt ell := by
    calc
      ell ^ 2 = ell ^ 2 * 1 := by ring
      _ ≤ ell ^ 2 * (ell * Real.sqrt ell) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg ell)
        nlinarith
      _ = ell ^ 3 * Real.sqrt ell := by ring
  calc
    z ^ 2 ≤ (b * ell) ^ 2 :=
      (sq_le_sq₀ hz0 (mul_nonneg hb0 (zero_le_one.trans hell))).2 hz
    _ = b ^ 2 * ell ^ 2 := by ring
    _ ≤ C * ell ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg ell)
    _ ≤ C * (ell ^ 3 * Real.sqrt ell) :=
      mul_le_mul_of_nonneg_left htail ((sq_nonneg b).trans hcoef)

private theorem sq_mul_le_log_envelope
    {ell z b f C : ℝ} (hell : 1 ≤ ell) (hz0 : 0 ≤ z) (hb0 : 0 ≤ b)
    (hz : z ≤ b * ell) (hf0 : 0 ≤ f) (hf : f ≤ 2 * ell)
    (hcoef : 2 * b ^ 2 ≤ C) :
    z ^ 2 * f ≤ C * (ell ^ 3 * Real.sqrt ell) := by
  have hsqrt : 1 ≤ Real.sqrt ell := Real.one_le_sqrt.mpr hell
  have hzsq : z ^ 2 ≤ (b * ell) ^ 2 :=
    (sq_le_sq₀ hz0 (mul_nonneg hb0 (zero_le_one.trans hell))).2 hz
  calc
    z ^ 2 * f ≤ (b * ell) ^ 2 * (2 * ell) :=
      mul_le_mul hzsq hf hf0 (sq_nonneg _)
    _ = (2 * b ^ 2) * ell ^ 3 := by ring
    _ ≤ C * ell ^ 3 := by
      apply mul_le_mul_of_nonneg_right hcoef
      positivity
    _ ≤ C * (ell ^ 3 * Real.sqrt ell) := by
      apply mul_le_mul_of_nonneg_left _ ((mul_nonneg (by norm_num) (sq_nonneg b)).trans hcoef)
      calc
        ell ^ 3 = ell ^ 3 * 1 := by ring
        _ ≤ ell ^ 3 * Real.sqrt ell :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)

private theorem fourth_log_factor_le
    {ell scale b e D f : ℝ} (hell : 1 ≤ ell)
    (_hscale0 : 0 ≤ scale) (hscale : scale ≤ b * ell)
    (hb0 : 0 ≤ b) (he0 : 0 ≤ e) (he : e ≤ D * ell)
    (hD0 : 0 ≤ D) (hf0 : 0 ≤ f) (hf : f ≤ 2 * ell) :
    scale * Real.sqrt scale * e * f ≤
      (2 * b * Real.sqrt b * D) * (ell ^ 3 * Real.sqrt ell) := by
  have hell0 : 0 ≤ ell := zero_le_one.trans hell
  have hsqrt : Real.sqrt scale ≤ Real.sqrt (b * ell) :=
    Real.sqrt_le_sqrt hscale
  calc
    scale * Real.sqrt scale * e * f ≤
        (b * ell) * Real.sqrt (b * ell) * (D * ell) * (2 * ell) := by
      gcongr
    _ = (2 * b * Real.sqrt b * D) * (ell ^ 3 * Real.sqrt ell) := by
      rw [Real.sqrt_mul hb0]
      ring

private theorem fourthScaleLog_low_le
    {x : ℕ} (hx : 4 ≤ x) :
    vaughanFourthScaleLog (vaughanCubeRoot x) x ≤
      (7 / 6 : ℝ) * Real.log (x : ℝ) := by
  have hcpos := vaughanCubeRoot_pos (by omega : 1 ≤ x)
  have harg :
      2 * (x : ℝ) / vaughanCubeRoot x =
        2 * vaughanCubeRoot x * vaughanCubeRoot x := by
    rw [← vaughanCubeRoot_cube x]
    field_simp [hcpos.ne']
  have hraw0 : 0 ≤ Real.log (2 * (x : ℝ) / vaughanCubeRoot x) := by
    rw [harg]
    apply Real.log_nonneg
    nlinarith [one_le_vaughanCubeRoot (by omega : 1 ≤ x),
      sq_nonneg (vaughanCubeRoot x)]
  rw [vaughanFourthScaleLog, max_eq_right hraw0, harg]
  exact log_two_mul_cubeRoot_sq_le hx

/-- Low-range logarithmic optimization with `U=V=x^(1/3)`. -/
theorem vaughanPrimitiveMeanLogScale_low_le
    {x : ℕ} (hx : 4 ≤ x) :
    vaughanPrimitiveMeanLogScale
        (vaughanCubeRoot x) (vaughanCubeRoot x) x ≤
      vaughanPrimitiveMeanLowLogCoefficient *
        vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hxone : 1 ≤ x := by omega
  have hell := one_le_log_natCast hx
  have hcpos := vaughanCubeRoot_pos hxone
  have hfirst0 : 0 ≤ Real.log ((x : ℝ) * vaughanCubeRoot x) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast hxone) (one_le_vaughanCubeRoot hxone))
  have hfirst : Real.log ((x : ℝ) * vaughanCubeRoot x) ≤
      (4 / 3 : ℝ) * Real.log (x : ℝ) := by
    rw [log_natCast_mul_cubeRoot_eq hxone]
  have hthird0 :
      0 ≤ Real.log (2 * vaughanCubeRoot x * vaughanCubeRoot x) := by
    apply Real.log_nonneg
    nlinarith [one_le_vaughanCubeRoot hxone,
      sq_nonneg (vaughanCubeRoot x)]
  have hthird := log_two_mul_cubeRoot_sq_le hx
  have hfourLog0 : 0 ≤ Real.log (4 * (x : ℝ)) := by
    apply Real.log_nonneg
    have hxReal : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxone
    nlinarith
  have hfourLog := log_four_mul_natCast_le hx
  have hExp0 : 0 ≤ Real.log (Real.exp 3 * vaughanCubeRoot x) := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num))
      (one_le_vaughanCubeRoot hxone)
  have hExp := log_exp_three_mul_cubeRoot_le hx
  have hbase0 : 0 ≤ 1 / 3 + 3 / (2 * Real.log 2) := by positivity
  have hlowFirst : (4 / 3 : ℝ) ^ 2 ≤
      vaughanPrimitiveMeanLowLogCoefficient := by
    exact (by norm_num : (4 / 3 : ℝ) ^ 2 ≤ 11 / 3).trans
      eleven_thirds_le_low_log_coefficient
  have hlowThird : 2 * (7 / 6 : ℝ) ^ 2 ≤
      vaughanPrimitiveMeanLowLogCoefficient := by
    exact (by norm_num : 2 * (7 / 6 : ℝ) ^ 2 ≤ 11 / 3).trans
      eleven_thirds_le_low_log_coefficient
  unfold vaughanPrimitiveMeanLogScale
  apply max_le
  · exact sq_le_log_envelope hell hfirst0 (by norm_num) hfirst hlowFirst
  · apply max_le
    · exact sq_le_log_envelope hell hfirst0 (by norm_num) hfirst hlowFirst
    · apply max_le
      · exact sq_mul_le_log_envelope hell hthird0 (by norm_num) hthird hfourLog0
          hfourLog hlowThird
      · unfold vaughanPrimitiveMeanLowLogCoefficient
        exact fourth_log_factor_le hell
          (vaughanFourthScaleLog_nonneg (vaughanCubeRoot x) x)
          (fourthScaleLog_low_le hx) (by norm_num) hExp0 hExp hbase0
          hfourLog0 hfourLog

/-- The low-range logarithmic coefficient is bounded by the common high-range
coefficient. -/
theorem vaughanPrimitiveMeanLowLogCoefficient_le_high :
    vaughanPrimitiveMeanLowLogCoefficient ≤
      vaughanPrimitiveMeanHighLogCoefficient := by
  unfold vaughanPrimitiveMeanLowLogCoefficient
    vaughanPrimitiveMeanHighLogCoefficient
  have hab : (7 / 6 : ℝ) ≤ 4 / 3 := by norm_num
  have hsqrt : Real.sqrt (7 / 6 : ℝ) ≤ Real.sqrt (4 / 3 : ℝ) :=
    Real.sqrt_le_sqrt hab
  have hD : 0 ≤ 1 / 3 + 3 / (2 * Real.log 2) := by positivity
  have hproduct :
      (7 / 6 : ℝ) * Real.sqrt (7 / 6 : ℝ) ≤
        (4 / 3 : ℝ) * Real.sqrt (4 / 3 : ℝ) :=
    mul_le_mul hab hsqrt (Real.sqrt_nonneg _) (by norm_num)
  apply mul_le_mul_of_nonneg_right _ hD
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℝ) ≤ 2)

private theorem highCutoff_pos
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq : vaughanCubeRoot x ≤ q) :
    0 < vaughanCubeRoot x ^ 2 / q := by
  have hcpos := vaughanCubeRoot_pos (by omega : 1 ≤ x)
  have hqpos : 0 < q := hcpos.trans_le hq
  positivity

private theorem highCutoff_le_cubeRoot
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq : vaughanCubeRoot x ≤ q) :
    vaughanCubeRoot x ^ 2 / q ≤ vaughanCubeRoot x := by
  have hcpos := vaughanCubeRoot_pos (by omega : 1 ≤ x)
  have hqpos : 0 < q := hcpos.trans_le hq
  rw [div_le_iff₀ hqpos]
  nlinarith

private theorem fourthScaleLog_high_le
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq : vaughanCubeRoot x ≤ q)
    (hqsqrt : q ≤ Real.sqrt (x : ℝ)) :
    vaughanFourthScaleLog (vaughanCubeRoot x ^ 2 / q) x ≤
      (4 / 3 : ℝ) * Real.log (x : ℝ) := by
  have hxone : 1 ≤ x := by omega
  have hcpos := vaughanCubeRoot_pos hxone
  have hqpos : 0 < q := hcpos.trans_le hq
  have hcutpos := highCutoff_pos hx hq
  have hsqrtTwo : 2 ≤ Real.sqrt (x : ℝ) := by
    calc
      (2 : ℝ) = Real.sqrt 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hx)
  have htwoQ : 2 * q ≤ (x : ℝ) := by
    have hsqrtSq := Real.sq_sqrt (show 0 ≤ (x : ℝ) by positivity)
    nlinarith
  have hargEq :
      2 * (x : ℝ) / (vaughanCubeRoot x ^ 2 / q) =
        2 * vaughanCubeRoot x * q := by
    rw [← vaughanCubeRoot_cube x]
    field_simp [hcpos.ne', hqpos.ne']
  have hargLe :
      2 * (x : ℝ) / (vaughanCubeRoot x ^ 2 / q) ≤
        (x : ℝ) * vaughanCubeRoot x := by
    rw [hargEq]
    calc
      2 * vaughanCubeRoot x * q = vaughanCubeRoot x * (2 * q) := by ring
      _ ≤ vaughanCubeRoot x * (x : ℝ) :=
        mul_le_mul_of_nonneg_left htwoQ hcpos.le
      _ = (x : ℝ) * vaughanCubeRoot x := by ring
  have hraw0 :
      0 ≤ Real.log (2 * (x : ℝ) /
        (vaughanCubeRoot x ^ 2 / q)) := by
    rw [hargEq]
    apply Real.log_nonneg
    nlinarith [one_le_vaughanCubeRoot hxone]
  rw [vaughanFourthScaleLog, max_eq_right hraw0]
  exact (Real.log_le_log (by positivity) hargLe).trans_eq
    (log_natCast_mul_cubeRoot_eq hxone)

/-- High-range logarithmic optimization with `U=V=x^(2/3)/q`. -/
theorem vaughanPrimitiveMeanLogScale_high_le
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq : vaughanCubeRoot x ≤ q)
    (hqsqrt : q ≤ Real.sqrt (x : ℝ)) :
    vaughanPrimitiveMeanLogScale
        (vaughanCubeRoot x ^ 2 / q)
        (vaughanCubeRoot x ^ 2 / q) x ≤
      vaughanPrimitiveMeanHighLogCoefficient *
        vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hxone : 1 ≤ x := by omega
  have hcpos := vaughanCubeRoot_pos hxone
  have hqpos : 0 < q := hcpos.trans_le hq
  let U := vaughanCubeRoot x ^ 2 / q
  have hUpos : 0 < U := highCutoff_pos hx hq
  have hUone : 1 ≤ U :=
    one_le_vaughanPrimitiveMeanHighCutoff hx hq hqsqrt
  have hUle : U ≤ vaughanCubeRoot x := highCutoff_le_cubeRoot hx hq
  have hell := one_le_log_natCast hx
  have hxpos : 0 < (x : ℝ) := by positivity
  have hfirstArg : (x : ℝ) * U ≤ (x : ℝ) * vaughanCubeRoot x :=
    mul_le_mul_of_nonneg_left hUle (by positivity)
  have hfirst0 : 0 ≤ Real.log ((x : ℝ) * U) := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hxone)
      hUone
  have hfirst : Real.log ((x : ℝ) * U) ≤
      (4 / 3 : ℝ) * Real.log (x : ℝ) :=
    (Real.log_le_log (by positivity) hfirstArg).trans_eq
      (log_natCast_mul_cubeRoot_eq hxone)
  have hthirdArg : 2 * U * U ≤
      2 * vaughanCubeRoot x * vaughanCubeRoot x := by
    nlinarith [hUpos.le, hcpos.le]
  have hthird0 : 0 ≤ Real.log (2 * U * U) := by
    apply Real.log_nonneg
    nlinarith [hUone]
  have hthird : Real.log (2 * U * U) ≤
      (7 / 6 : ℝ) * Real.log (x : ℝ) :=
    (Real.log_le_log (by positivity) hthirdArg).trans
      (log_two_mul_cubeRoot_sq_le hx)
  have hfourLog0 : 0 ≤ Real.log (4 * (x : ℝ)) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxone
      nlinarith)
  have hfourLog := log_four_mul_natCast_le hx
  have hExpArg : Real.exp 3 * U ≤
      Real.exp 3 * vaughanCubeRoot x :=
    mul_le_mul_of_nonneg_left hUle (Real.exp_pos 3).le
  have hExp0 : 0 ≤ Real.log (Real.exp 3 * U) := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_exp (by norm_num)) hUone
  have hExp : Real.log (Real.exp 3 * U) ≤
      (1 / 3 + 3 / (2 * Real.log 2)) * Real.log (x : ℝ) :=
    (Real.log_le_log (by positivity) hExpArg).trans
      (log_exp_three_mul_cubeRoot_le hx)
  have hbase0 : 0 ≤ 1 / 3 + 3 / (2 * Real.log 2) := by positivity
  have hhighFirst : (4 / 3 : ℝ) ^ 2 ≤
      vaughanPrimitiveMeanHighLogCoefficient :=
    (by norm_num : (4 / 3 : ℝ) ^ 2 ≤ 11 / 3).trans
      (eleven_thirds_le_low_log_coefficient.trans
        vaughanPrimitiveMeanLowLogCoefficient_le_high)
  have hhighThird : 2 * (7 / 6 : ℝ) ^ 2 ≤
      vaughanPrimitiveMeanHighLogCoefficient :=
    (by norm_num : 2 * (7 / 6 : ℝ) ^ 2 ≤ 11 / 3).trans
      (eleven_thirds_le_low_log_coefficient.trans
        vaughanPrimitiveMeanLowLogCoefficient_le_high)
  change vaughanPrimitiveMeanLogScale U U x ≤ _
  unfold vaughanPrimitiveMeanLogScale
  apply max_le
  · exact sq_le_log_envelope hell hfirst0 (by norm_num) hfirst hhighFirst
  · apply max_le
    · exact sq_le_log_envelope hell hfirst0 (by norm_num) hfirst hhighFirst
    · apply max_le
      · exact sq_mul_le_log_envelope hell hthird0 (by norm_num) hthird hfourLog0
          hfourLog hhighThird
      · unfold vaughanPrimitiveMeanHighLogCoefficient
        exact fourth_log_factor_le hell
          (vaughanFourthScaleLog_nonneg U x)
          (fourthScaleLog_high_le hx hq hqsqrt) (by norm_num)
          hExp0 hExp hbase0 hfourLog0 hfourLog

end

end BoundedGaps.Maynard
