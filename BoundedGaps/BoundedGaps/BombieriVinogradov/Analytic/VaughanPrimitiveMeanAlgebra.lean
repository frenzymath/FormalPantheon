import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanFactorization

/-!
# Algebraic cutoff comparisons for the Vaughan primitive mean estimate

This file performs the two parameter substitutions following
Akbary--Hambrook equation (6.15) and compares their algebraic scales with the
power polynomial in equation (1.1).

Source: `AkbaryHambrook2013v2`, Section 6, printed pp. 23--24. Semantic
review: `SEM-460`.
-/

namespace BoundedGaps.Maynard

noncomputable section

private theorem sqrt_vaughanCubeRoot (x : ℕ) :
    Real.sqrt (vaughanCubeRoot x) = vaughanSixthRoot x := by
  rw [← vaughanSixthRoot_sq x]
  exact Real.sqrt_sq (vaughanSixthRoot_nonneg x)

private theorem sqrt_natCast_mul_cubeRoots (x : ℕ) :
    Real.sqrt ((x : ℝ) * vaughanCubeRoot x * vaughanCubeRoot x) =
      Real.sqrt (x : ℝ) * vaughanCubeRoot x := by
  calc
    Real.sqrt ((x : ℝ) * vaughanCubeRoot x * vaughanCubeRoot x) =
        Real.sqrt ((vaughanSixthRoot x ^ 5) ^ 2) := by
      congr 1
      rw [← vaughanSixthRoot_pow_six x, ← vaughanSixthRoot_sq x]
      ring
    _ = vaughanSixthRoot x ^ 5 :=
      Real.sqrt_sq (by positivity [vaughanSixthRoot_nonneg x])
    _ = Real.sqrt (x : ℝ) * vaughanCubeRoot x :=
      vaughanSixthRoot_pow_five x

private theorem natCast_div_sixthRoot {x : ℕ} (hx : 1 ≤ x) :
    (x : ℝ) / vaughanSixthRoot x =
      Real.sqrt (x : ℝ) * vaughanCubeRoot x := by
  have hs : 0 < vaughanSixthRoot x := vaughanSixthRoot_pos hx
  calc
    (x : ℝ) / vaughanSixthRoot x =
        vaughanSixthRoot x ^ 6 / vaughanSixthRoot x := by
      rw [vaughanSixthRoot_pow_six]
    _ = vaughanSixthRoot x ^ 5 := by
      field_simp [ne_of_gt hs]
    _ = Real.sqrt (x : ℝ) * vaughanCubeRoot x :=
      vaughanSixthRoot_pow_five x

private theorem sqrt_mul_self_factor
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    Real.sqrt (a * u * u) = Real.sqrt a * u := by
  calc
    Real.sqrt (a * u * u) = Real.sqrt ((Real.sqrt a * u) ^ 2) := by
      congr 1
      rw [mul_pow, Real.sq_sqrt ha]
      ring
    _ = Real.sqrt a * u := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg a) hu)

theorem vaughanPrimitiveMeanAlgebraicScale_low_le
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq0 : 0 ≤ q) (hq : q ≤ vaughanCubeRoot x) :
    vaughanPrimitiveMeanAlgebraicScale
        (vaughanCubeRoot x) (vaughanCubeRoot x) x q ≤
      4 * (x : ℝ) + 2 * Real.sqrt (x : ℝ) * q ^ 2 +
        3 * (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 +
        (2 + 2 * Real.sqrt 2) * q *
          (Real.sqrt (x : ℝ) * vaughanCubeRoot x) := by
  have hx1 : 1 ≤ x := by omega
  have hc0 : 0 ≤ vaughanCubeRoot x := vaughanCubeRoot_nonneg x
  have hc1 : 1 ≤ vaughanCubeRoot x := one_le_vaughanCubeRoot hx1
  have hsqrtq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsqrtq_le_c : Real.sqrt q ≤ vaughanCubeRoot x := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hc0
    · have hc_le_sq : vaughanCubeRoot x ≤ vaughanCubeRoot x ^ 2 := by
        nlinarith
      exact hq.trans hc_le_sq
  have hq_le_sqrtq_mul_c :
      q ≤ Real.sqrt q * vaughanCubeRoot x := by
    calc
      q = Real.sqrt q * Real.sqrt q := by
        nlinarith [Real.sq_sqrt hq0]
      _ ≤ Real.sqrt q * vaughanCubeRoot x :=
        mul_le_mul_of_nonneg_left hsqrtq_le_c hsqrtq0
  have hfirst :
      vaughanCubeRoot x * q ^ 2 ≤
        (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by
    calc
      vaughanCubeRoot x * q ^ 2 =
          (q * vaughanCubeRoot x) * q := by ring
      _ ≤ (q * vaughanCubeRoot x) *
          (Real.sqrt q * vaughanCubeRoot x) :=
        mul_le_mul_of_nonneg_left hq_le_sqrtq_mul_c
          (mul_nonneg hq0 hc0)
      _ = (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by ring
  have hsecond :
      q ^ 2 * Real.sqrt q * vaughanCubeRoot x ≤
        (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by
    calc
      q ^ 2 * Real.sqrt q * vaughanCubeRoot x =
          (q * Real.sqrt q * vaughanCubeRoot x) * q := by ring
      _ ≤ (q * Real.sqrt q * vaughanCubeRoot x) *
          vaughanCubeRoot x :=
        mul_le_mul_of_nonneg_left hq
          (mul_nonneg (mul_nonneg hq0 hsqrtq0) hc0)
      _ = (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by ring
  have hcollect :
      vaughanPrimitiveMeanAlgebraicScale
          (vaughanCubeRoot x) (vaughanCubeRoot x) x q =
        4 * (x : ℝ) + 2 * Real.sqrt (x : ℝ) * q ^ 2 +
          vaughanCubeRoot x * q ^ 2 +
          2 * (q ^ 2 * Real.sqrt q * vaughanCubeRoot x) +
          (2 + 2 * Real.sqrt 2) * q *
            (Real.sqrt (x : ℝ) * vaughanCubeRoot x) := by
    unfold vaughanPrimitiveMeanAlgebraicScale
    rw [sqrt_natCast_mul_cubeRoots x, sqrt_vaughanCubeRoot x]
    simp only [mul_div_assoc]
    rw [natCast_div_sixthRoot hx1]
    ring
  rw [hcollect]
  nlinarith

theorem vaughanPrimitiveMeanAlgebraicScale_high_le
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq : vaughanCubeRoot x ≤ q)
    (hqsqrt : q ≤ Real.sqrt (x : ℝ)) :
    vaughanPrimitiveMeanAlgebraicScale
        (vaughanCubeRoot x ^ 2 / q)
        (vaughanCubeRoot x ^ 2 / q) x q ≤
      4 * (x : ℝ) + 2 * Real.sqrt (x : ℝ) * q ^ 2 +
        (3 + 2 * Real.sqrt 2) * (q * Real.sqrt q) *
          vaughanCubeRoot x ^ 2 +
        2 * q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) := by
  have hx1 : 1 ≤ x := by omega
  have hc0 : 0 ≤ vaughanCubeRoot x := vaughanCubeRoot_nonneg x
  have hcpos : 0 < vaughanCubeRoot x := vaughanCubeRoot_pos hx1
  have hqpos : 0 < q := hcpos.trans_le hq
  have hq0 : 0 ≤ q := hqpos.le
  have hsqrtqpos : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have hU0 : 0 ≤ vaughanCubeRoot x ^ 2 / q := by positivity
  have hsqrtU :
      Real.sqrt (vaughanCubeRoot x ^ 2 / q) =
        vaughanCubeRoot x / Real.sqrt q := by
    rw [Real.sqrt_div (sq_nonneg (vaughanCubeRoot x)) q,
      Real.sqrt_sq hc0]
  have hUqSq :
      (vaughanCubeRoot x ^ 2 / q) * q ^ 2 =
        vaughanCubeRoot x ^ 2 * q := by
    field_simp [ne_of_gt hqpos]
  have hqSqSqrtU :
      q ^ 2 * Real.sqrt q * (vaughanCubeRoot x ^ 2 / q) =
        (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by
    field_simp [ne_of_gt hqpos]
  have hmixed :
      q * Real.sqrt ((x : ℝ) *
          (vaughanCubeRoot x ^ 2 / q) *
          (vaughanCubeRoot x ^ 2 / q)) =
        Real.sqrt (x : ℝ) * vaughanCubeRoot x ^ 2 := by
    rw [sqrt_mul_self_factor (Nat.cast_nonneg x) hU0]
    field_simp [ne_of_gt hqpos]
  have hplainDiv :
      q * (x : ℝ) /
          Real.sqrt (vaughanCubeRoot x ^ 2 / q) =
        (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by
    rw [hsqrtU, ← vaughanCubeRoot_cube x]
    field_simp [ne_of_gt hcpos, ne_of_gt hsqrtqpos]
  have hsqrtTwoDiv :
      Real.sqrt 2 * q * (x : ℝ) /
          Real.sqrt (vaughanCubeRoot x ^ 2 / q) =
        Real.sqrt 2 * (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by
    rw [hsqrtU, ← vaughanCubeRoot_cube x]
    field_simp [ne_of_gt hcpos, ne_of_gt hsqrtqpos]
  have hcollect :
      vaughanPrimitiveMeanAlgebraicScale
          (vaughanCubeRoot x ^ 2 / q)
          (vaughanCubeRoot x ^ 2 / q) x q =
        4 * (x : ℝ) + 2 * Real.sqrt (x : ℝ) * q ^ 2 +
          (3 + 2 * Real.sqrt 2) * (q * Real.sqrt q) *
            vaughanCubeRoot x ^ 2 +
          q * vaughanCubeRoot x ^ 2 +
          Real.sqrt (x : ℝ) * vaughanCubeRoot x ^ 2 := by
    unfold vaughanPrimitiveMeanAlgebraicScale
    rw [hUqSq, hqSqSqrtU, hmixed, hsqrtTwoDiv, hplainDiv]
    ring
  have hc_le_sqrt :
      vaughanCubeRoot x ≤ Real.sqrt (x : ℝ) :=
    hq.trans hqsqrt
  have hcSq_le :
      vaughanCubeRoot x ^ 2 ≤
        Real.sqrt (x : ℝ) * vaughanCubeRoot x := by
    simpa [pow_two] using mul_le_mul_of_nonneg_right hc_le_sqrt hc0
  have hlinearOne :
      q * vaughanCubeRoot x ^ 2 ≤
        q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) :=
    mul_le_mul_of_nonneg_left hcSq_le hq0
  have hlinearTwo :
      Real.sqrt (x : ℝ) * vaughanCubeRoot x ^ 2 ≤
        q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) := by
    calc
      Real.sqrt (x : ℝ) * vaughanCubeRoot x ^ 2 =
          (Real.sqrt (x : ℝ) * vaughanCubeRoot x) *
            vaughanCubeRoot x := by ring
      _ ≤ (Real.sqrt (x : ℝ) * vaughanCubeRoot x) * q :=
        mul_le_mul_of_nonneg_left hq
          (mul_nonneg (Real.sqrt_nonneg _) hc0)
      _ = q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) := by ring
  rw [hcollect]
  nlinarith

private theorem two_add_two_sqrt_two_le_five :
    (2 : ℝ) + 2 * Real.sqrt 2 ≤ 5 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_nonneg (2 : ℝ)]

private theorem three_add_two_sqrt_two_le_six :
    (3 : ℝ) + 2 * Real.sqrt 2 ≤ 6 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_nonneg (2 : ℝ)]

theorem vaughanPrimitiveMeanAlgebraicScale_low_le_polynomial
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq0 : 0 ≤ q) (hq : q ≤ vaughanCubeRoot x) :
    vaughanPrimitiveMeanAlgebraicScale
        (vaughanCubeRoot x) (vaughanCubeRoot x) x q ≤
      vaughanPrimitiveMeanEquationOneOnePolynomial x q := by
  have hbase := vaughanPrimitiveMeanAlgebraicScale_low_le hx hq0 hq
  have hthree : 0 ≤ (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by
    positivity
  have hlinear :
      0 ≤ q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) := by
    exact mul_nonneg hq0
      (mul_nonneg (Real.sqrt_nonneg _) (vaughanCubeRoot_nonneg x))
  have hthreeCoeff :
      3 * ((q * Real.sqrt q) * vaughanCubeRoot x ^ 2) ≤
        6 * ((q * Real.sqrt q) * vaughanCubeRoot x ^ 2) := by
    nlinarith
  have hlinearCoeff :
      (2 + 2 * Real.sqrt 2) *
          (q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x)) ≤
        5 * (q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x)) :=
    mul_le_mul_of_nonneg_right two_add_two_sqrt_two_le_five hlinear
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  nlinarith

theorem vaughanPrimitiveMeanAlgebraicScale_high_le_polynomial
    {x : ℕ} {q : ℝ} (hx : 4 ≤ x)
    (hq : vaughanCubeRoot x ≤ q)
    (hqsqrt : q ≤ Real.sqrt (x : ℝ)) :
    vaughanPrimitiveMeanAlgebraicScale
        (vaughanCubeRoot x ^ 2 / q)
        (vaughanCubeRoot x ^ 2 / q) x q ≤
      vaughanPrimitiveMeanEquationOneOnePolynomial x q := by
  have hbase := vaughanPrimitiveMeanAlgebraicScale_high_le hx hq hqsqrt
  have hq0 : 0 ≤ q :=
    (vaughanCubeRoot_nonneg x).trans hq
  have hthree : 0 ≤ (q * Real.sqrt q) * vaughanCubeRoot x ^ 2 := by
    positivity
  have hlinear :
      0 ≤ q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) := by
    exact mul_nonneg hq0
      (mul_nonneg (Real.sqrt_nonneg _) (vaughanCubeRoot_nonneg x))
  have hthreeCoeff :
      (3 + 2 * Real.sqrt 2) *
          ((q * Real.sqrt q) * vaughanCubeRoot x ^ 2) ≤
        6 * ((q * Real.sqrt q) * vaughanCubeRoot x ^ 2) :=
    mul_le_mul_of_nonneg_right three_add_two_sqrt_two_le_six hthree
  have hlinearCoeff :
      2 * (q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x)) ≤
        5 * (q * (Real.sqrt (x : ℝ) * vaughanCubeRoot x)) := by
    nlinarith
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  nlinarith

end

end BoundedGaps.Maynard
