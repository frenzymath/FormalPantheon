import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaSmoothedSquareLower

/-!
# Square-root scale of the smoothed square sum

The bare square weights in the linearly smoothed quadratic convolution have
an explicit square-root lower bound. The constant is sharp on the stated
natural-endpoint range.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 125, proof
of Theorem 12.8. Semantic review: `SEM-541`.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace BoundedGaps.Maynard

/-- The positive square weights below a natural cutoff have square-root
scale. -/
theorem three_eighths_mul_real_sqrt_le_sum_square_linearCutoff
    {X : ℕ} (hX : 4 ≤ X) :
    (3 / 8 : ℝ) * Real.sqrt (X : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 X.sqrt,
        (1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) := by
  have hXpos : 0 < X := by omega
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hsqrt_two : 2 ≤ X.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hsum_sq : ∀ r : ℕ,
      (∑ m ∈ Finset.Icc 1 r, (m : ℝ) ^ 2) =
        (r : ℝ) * ((r : ℝ) + 1) * (2 * (r : ℝ) + 1) / 6 := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring
  have hsum_weights :
      (∑ m ∈ Finset.Icc 1 X.sqrt,
          (1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ)) =
        (X.sqrt : ℝ) -
          (X.sqrt : ℝ) * ((X.sqrt : ℝ) + 1) *
            (2 * (X.sqrt : ℝ) + 1) / (6 * (X : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum_sq]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    push_cast
    simp
    ring
  rw [hsum_weights]
  let r : ℝ := X.sqrt
  let R : ℝ := Real.sqrt (X : ℝ)
  let u : ℝ := R - r
  change (3 / 8 : ℝ) * R ≤
    r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ))
  have hr : (2 : ℝ) ≤ r := by
    dsimp only [r]
    exact_mod_cast hsqrt_two
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hR_sq : R ^ 2 = (X : ℝ) := by
    dsimp only [R]
    exact Real.sq_sqrt hXreal.le
  have hrR : r ≤ R := by
    dsimp only [r, R]
    exact Real.nat_sqrt_le_real_sqrt
  have hRlt : R < r + 1 := by
    dsimp only [r, R]
    exact Real.real_sqrt_lt_nat_sqrt_succ
  have hu0 : (0 : ℝ) ≤ u := by
    dsimp only [u]
    linarith
  have hu1 : u < 1 := by
    dsimp only [u]
    linarith
  have hru : r * u ≤ r := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hu1.le)]
  have hu_sq : u ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1.le)]
  have hr_sq : (4 : ℝ) ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ r + 2)]
  have hbracket :
      (0 : ℝ) ≤ 21 * r ^ 2 - 3 * r * u - 9 * u ^ 2 := by
    nlinarith
  have hfirst :
      (0 : ℝ) ≤ r * (r - 2) * (7 * r + 2) :=
    mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr)) (by nlinarith)
  have hsecond :
      (0 : ℝ) ≤ u * (21 * r ^ 2 - 3 * r * u - 9 * u ^ 2) :=
    mul_nonneg hu0 hbracket
  have hidentity :
      24 * (X : ℝ) *
          (r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ)) -
            (3 / 8 : ℝ) * R) =
        r * (r - 2) * (7 * r + 2) +
          u * (21 * r ^ 2 - 3 * r * u - 9 * u ^ 2) := by
    rw [← hR_sq]
    dsimp only [u]
    field_simp [show R ≠ 0 by positivity]
    ring
  have hscaled :
      (0 : ℝ) ≤ 24 * (X : ℝ) *
        (r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ)) -
          (3 / 8 : ℝ) * R) := by
    rw [hidentity]
    exact add_nonneg hfirst hsecond
  have hscale_pos : (0 : ℝ) < 24 * (X : ℝ) := by positivity
  have := (mul_nonneg_iff_of_pos_left hscale_pos).mp hscaled
  linarith

/-- The linearly smoothed quadratic zeta convolution has square-root scale. -/
theorem three_eighths_mul_real_sqrt_le_quadraticZetaLinearSmoothedSum
    {q X : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hX : 4 ≤ X) :
    (((3 / 8 : ℝ) * Real.sqrt (X : ℝ) : ℝ) : ℂ) ≤
      quadraticZetaLinearSmoothedSum chi X := by
  have hscalar :
      (((3 / 8 : ℝ) * Real.sqrt (X : ℝ) : ℝ) : ℂ) ≤
        ∑ m ∈ Finset.Icc 1 X.sqrt,
          ((1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    exact_mod_cast
      three_eighths_mul_real_sqrt_le_sum_square_linearCutoff hX
  exact hscalar.trans
    (sum_square_linearCutoff_le_quadraticZetaLinearSmoothedSum
      hsquare (by omega))

end BoundedGaps.Maynard
