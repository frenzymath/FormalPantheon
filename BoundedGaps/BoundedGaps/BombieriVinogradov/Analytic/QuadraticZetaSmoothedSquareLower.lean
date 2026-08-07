import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaConvolutionSquare

/-!
# A smoothed quadratic convolution lower bound

For a square-principal Dirichlet character, the linearly smoothed finite sum
of the coefficients of `1 * chi` is bounded below by its bare square weights.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125,
proof of Theorem 12.8. Semantic review: `SEM-540`.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace BoundedGaps.Maynard

/-- The linearly smoothed finite sum of the coefficients of `1 * chi`. -/
noncomputable def quadraticZetaLinearSmoothedSum
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    chi.zetaMul n * ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)

/-- Dropping nonsquares from the smoothed quadratic convolution gives a lower
bound by the bare square weights. -/
theorem sum_square_linearCutoff_le_quadraticZetaLinearSmoothedSum
    {q X : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hX : 0 < X) :
    (∑ m ∈ Finset.Icc 1 X.sqrt,
        ((1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) : ℂ)) ≤
      quadraticZetaLinearSmoothedSum chi X := by
  classical
  let squares := Finset.Icc 1 X.sqrt
  let indices := Finset.Icc 1 X
  let square : ℕ → ℕ := fun m ↦ m ^ 2
  let weight : ℕ → ℂ := fun n ↦
    ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)
  let summand : ℕ → ℂ := fun n ↦ chi.zetaMul n * weight n
  have hXreal : (0 : ℝ) < X := by
    exact_mod_cast hX
  have hweight : ∀ n ∈ indices, (0 : ℂ) ≤ weight n := by
    intro n hn
    have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
    dsimp only [weight]
    rw [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨sub_nonneg.mpr ((div_le_one hXreal).2 (by exact_mod_cast hnX)), rfl⟩
  have hsquare_subset : squares.image square ⊆ indices := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    have hm_bounds := Finset.mem_Icc.mp hm
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_pow 2 m (by omega)
    · exact Nat.le_sqrt'.mp hm_bounds.2
  have hsquare_injective : Set.InjOn square squares :=
    (Nat.pow_left_injective (by decide : 2 ≠ 0)).injOn
  have hselected :
      (∑ m ∈ squares, weight (square m)) ≤
        ∑ m ∈ squares, summand (square m) := by
    apply Finset.sum_le_sum
    intro m hm
    have hm_ne : m ≠ 0 := by
      have hm_one : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      omega
    have hm_image : square m ∈ squares.image square :=
      Finset.mem_image.mpr ⟨m, hm, rfl⟩
    simpa only [summand, square, one_mul] using
      mul_le_mul_of_nonneg_right
        (one_le_zetaMul_sq (chi := chi) hsquare hm_ne)
        (hweight _ (hsquare_subset hm_image))
  have hmain :
      (∑ m ∈ squares, weight (square m)) ≤ ∑ n ∈ indices, summand n := by
    calc
      (∑ m ∈ squares, weight (square m)) ≤
          ∑ m ∈ squares, summand (square m) := hselected
      _ = ∑ n ∈ squares.image square, summand n :=
        (Finset.sum_image hsquare_injective).symm
      _ ≤ ∑ n ∈ indices, summand n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsquare_subset fun n hn _ ↦
          mul_nonneg (chi.zetaMul_nonneg hsquare n) (hweight n hn)
  simpa [squares, indices, square, weight, summand,
    quadraticZetaLinearSmoothedSum, Nat.cast_pow] using hmain

end BoundedGaps.Maynard
