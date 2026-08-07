import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanOptimization

/-!
# Equation-(1.1)-shaped primitive mean bound

This file applies the two optimized Vaughan parameter regimes to the raw
primitive cumulative mean. It includes the separate levels `Q=0,1` and then
enlarges the natural-floor bound to a continuous real right-hand side for the
later Abel integral.

The result covers only `Q<=sqrt(x)`. Akbary--Hambrook's separate direct
large-sieve argument for larger `Q` is not claimed here.

Source: `AkbaryHambrook2013v2`, Theorem 1.2, equation (1.1), and Section 6,
printed pp. 23--24. Semantic review: `SEM-460`.
-/

namespace BoundedGaps.Maynard

noncomputable section

private theorem one_le_vaughanPrimitiveMeanHighLogCoefficient :
    1 ≤ vaughanPrimitiveMeanHighLogCoefficient := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoLe : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hfrac : (1 : ℝ) ≤ 3 / (2 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hD : (1 : ℝ) ≤ 1 / 3 + 3 / (2 * Real.log 2) := by
    linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (4 / 3 : ℝ) :=
    Real.one_le_sqrt.mpr (by norm_num)
  unfold vaughanPrimitiveMeanHighLogCoefficient
  calc
    (1 : ℝ) ≤ 2 * 1 * 1 * 1 := by norm_num
    _ ≤ 2 * (4 / 3 : ℝ) * Real.sqrt (4 / 3 : ℝ) *
        (1 / 3 + 3 / (2 * Real.log 2)) := by
      gcongr
      norm_num

private theorem self_le_vaughanPrimitiveMeanEquationOneOneConstant
    (A : ℝ) :
    A ≤ vaughanPrimitiveMeanEquationOneOneConstant A := by
  unfold vaughanPrimitiveMeanEquationOneOneConstant
  calc
    A ≤ vaughanPrimitiveMeanCoefficient A :=
      self_le_vaughanPrimitiveMeanCoefficient A
    _ = vaughanPrimitiveMeanCoefficient A * 1 := by ring
    _ ≤ vaughanPrimitiveMeanCoefficient A *
        vaughanPrimitiveMeanHighLogCoefficient :=
      mul_le_mul_of_nonneg_left
        one_le_vaughanPrimitiveMeanHighLogCoefficient
        (vaughanPrimitiveMeanCoefficient_nonneg A)

private theorem natCast_le_vaughanPrimitiveMeanEquationOneOnePolynomial
    (x : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (x : ℝ) ≤ vaughanPrimitiveMeanEquationOneOnePolynomial x q := by
  have hc0 : 0 ≤ vaughanCubeRoot x := vaughanCubeRoot_nonneg x
  have hsecond : 0 ≤ 2 * Real.sqrt (x : ℝ) * q ^ 2 := by positivity
  have hthird :
      0 ≤ 6 * vaughanCubeRoot x ^ 2 * (q * Real.sqrt q) := by
    positivity
  have hfourth :
      0 ≤ 5 * (Real.sqrt (x : ℝ) * vaughanCubeRoot x) * q := by
    positivity
  unfold vaughanPrimitiveMeanEquationOneOnePolynomial
  have hx0 : 0 ≤ (x : ℝ) := by positivity
  linarith

/-- Generic natural-cutoff equation-(1.1)-shaped bound in the range consumed
by the later Abel argument. The cases `Q=0,1` use the Chebyshev fallback. -/
theorem primitiveRawMeanValueCumulative_nat_le_equationOneOne_of_psi
    {A : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x Q : ℕ} (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    primitiveRawMeanValueCumulative x Q ≤
      vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  by_cases hQlarge : 2 ≤ Q
  · by_cases hQlow : (Q : ℝ) ≤ vaughanCubeRoot x
    · exact
        (primitiveRawMeanValueCumulative_nat_le_vaughanPrimitiveMeanMajorant_of_psi
          hA0 hpsi hx (one_le_vaughanCubeRoot (by omega))
            (one_le_vaughanCubeRoot (by omega)) hQlarge hQsqrt).trans
          (vaughanPrimitiveMeanMajorant_low_le_equationOneOne hA hx hQlow)
    · have hQhigh : vaughanCubeRoot x ≤ (Q : ℝ) := le_of_not_ge hQlow
      have hcutoff : 1 ≤ vaughanCubeRoot x ^ 2 / (Q : ℝ) :=
        one_le_vaughanPrimitiveMeanHighCutoff hx hQhigh hQsqrt
      exact
        (primitiveRawMeanValueCumulative_nat_le_vaughanPrimitiveMeanMajorant_of_psi
          hA0 hpsi hx hcutoff hcutoff hQlarge hQsqrt).trans
          (vaughanPrimitiveMeanMajorant_high_le_equationOneOne
            hA hx hQhigh hQsqrt)
  · have hQone : Q ≤ 1 := by omega
    have hQoneReal : (Q : ℝ) ≤ 1 := by exact_mod_cast hQone
    have hQsq : (Q : ℝ) ^ 2 ≤ 1 := by
      have hQ0 : (0 : ℝ) ≤ Q := by positivity
      nlinarith
    have hpsiX : Chebyshev.psi x ≤ A * (x : ℝ) :=
      hpsi (x : ℝ) (by positivity)
    have hsmall : primitiveRawMeanValueCumulative x Q ≤ A * (x : ℝ) := by
      calc
        primitiveRawMeanValueCumulative x Q ≤
            Chebyshev.psi x * (Q : ℝ) ^ 2 :=
          primitiveRawMeanValueCumulative_nat_le_psi_mul_sq x Q
        _ ≤ (A * (x : ℝ)) * (Q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hpsiX (sq_nonneg _)
        _ ≤ A * (x : ℝ) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hQsq
              (mul_nonneg hA0 (by positivity : (0 : ℝ) ≤ x))
    have hconstant : A ≤ vaughanPrimitiveMeanEquationOneOneConstant A :=
      self_le_vaughanPrimitiveMeanEquationOneOneConstant A
    have hconstant0 : 0 ≤ vaughanPrimitiveMeanEquationOneOneConstant A :=
      vaughanPrimitiveMeanEquationOneOneConstant_nonneg A
    have hpolynomial : (x : ℝ) ≤
        vaughanPrimitiveMeanEquationOneOnePolynomial x (Q : ℝ) :=
      natCast_le_vaughanPrimitiveMeanEquationOneOnePolynomial x (by positivity)
    have hpolynomial0 : 0 ≤
        vaughanPrimitiveMeanEquationOneOnePolynomial x (Q : ℝ) :=
      vaughanPrimitiveMeanEquationOneOnePolynomial_nonneg x (by positivity)
    have hlogPower : 1 ≤ vaughanPrimitiveMeanEquationOneOneLogPower x :=
      one_le_vaughanPrimitiveMeanEquationOneOneLogPower hx
    apply hsmall.trans
    calc
      A * (x : ℝ) ≤
          vaughanPrimitiveMeanEquationOneOneConstant A *
            vaughanPrimitiveMeanEquationOneOnePolynomial x Q :=
        mul_le_mul hconstant hpolynomial (by positivity) hconstant0
      _ = vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q * 1 := by ring
      _ ≤ vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
            vaughanPrimitiveMeanEquationOneOneLogPower x :=
        mul_le_mul_of_nonneg_left hlogPower
          (mul_nonneg hconstant0 hpolynomial0)

/-- Unconditional natural-cutoff specialization using Mathlib's verified
Chebyshev constant. -/
theorem primitiveRawMeanValueCumulative_nat_le_equationOneOne
    {x Q : ℕ} (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    primitiveRawMeanValueCumulative x Q ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x Q *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  apply primitiveRawMeanValueCumulative_nat_le_equationOneOne_of_psi
    (A := Real.log 4 + 4)
  · have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz
  · exact hx
  · exact hQsqrt

/-- Continuous all-floor form: the cumulative sum remains through
`floor(t)`, while the source polynomial is enlarged to the literal real
endpoint `t`. -/
theorem primitiveRawMeanValueCumulative_le_equationOneOne_of_psi
    {A t : ℝ} (hA : 1 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    {x : ℕ} (hx : 4 ≤ x) (ht0 : 0 ≤ t)
    (htsqrt : t ≤ Real.sqrt (x : ℝ)) :
    primitiveRawMeanValueCumulative x t ≤
      vaughanPrimitiveMeanEquationOneOneConstant A *
        vaughanPrimitiveMeanEquationOneOnePolynomial x t *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have hfloorSqrt : (⌊t⌋₊ : ℝ) ≤ Real.sqrt (x : ℝ) :=
    hfloor.trans htsqrt
  have hnatural :=
    primitiveRawMeanValueCumulative_nat_le_equationOneOne_of_psi
      hA hpsi hx hfloorSqrt
  have hpolynomial :=
    vaughanPrimitiveMeanEquationOneOnePolynomial_mono x
      (Nat.cast_nonneg ⌊t⌋₊) hfloor
  have hconstant0 : 0 ≤ vaughanPrimitiveMeanEquationOneOneConstant A :=
    vaughanPrimitiveMeanEquationOneOneConstant_nonneg A
  have hlogPower0 : 0 ≤ vaughanPrimitiveMeanEquationOneOneLogPower x :=
    vaughanPrimitiveMeanEquationOneOneLogPower_nonneg x
  have henlarged :
      primitiveRawMeanValueCumulative x (⌊t⌋₊ : ℝ) ≤
        vaughanPrimitiveMeanEquationOneOneConstant A *
          vaughanPrimitiveMeanEquationOneOnePolynomial x t *
            vaughanPrimitiveMeanEquationOneOneLogPower x := by
    apply hnatural.trans
    apply mul_le_mul_of_nonneg_right _ hlogPower0
    exact mul_le_mul_of_nonneg_left hpolynomial hconstant0
  simpa only [primitiveRawMeanValueCumulative, Nat.floor_natCast] using
    henlarged

/-- Unconditional continuous all-floor specialization using Mathlib's
verified Chebyshev constant. -/
theorem primitiveRawMeanValueCumulative_le_equationOneOne
    {t : ℝ} {x : ℕ} (hx : 4 ≤ x) (ht0 : 0 ≤ t)
    (htsqrt : t ≤ Real.sqrt (x : ℝ)) :
    primitiveRawMeanValueCumulative x t ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x t *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  apply primitiveRawMeanValueCumulative_le_equationOneOne_of_psi
    (A := Real.log 4 + 4)
  · have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz
  · exact hx
  · exact ht0
  · exact htsqrt

end

end BoundedGaps.Maynard
