import BoundedGaps.Maynard.MaynardLogSimplex
import BoundedGaps.Maynard.VariationalBridge

noncomputable section

namespace BoundedGaps.Maynard

open Filter MeasureTheory Set
open scoped BigOperators

/-! Expand the concrete diagonal into the certified 42-by-42 pair terms. -/

def engelsmaMaynardYDiagonalPairSum
    (alpha : ℝ) (N : ℕ) (i j : Fin 42) : ℝ :=
  ∑ u ∈ maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
    smallKRealPairTerm i j (fun m =>
      normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) u (engelsmaIndexEquiv.symm m)) /
      ∏ h : BoundedGaps.engelsmaTuple,
        (Nat.totient (u h) : ℝ)

def engelsmaMaynardYDiagonalQuadraticMomentSum
    (alpha : ℝ) (N b c : ℕ) : ℝ :=
  ∑ u ∈ maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
    simplexQuadraticIntegrand 105 b c (fun m =>
      normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) u (engelsmaIndexEquiv.symm m)) /
      ∏ h : BoundedGaps.engelsmaTuple,
        (Nat.totient (u h) : ℝ)

set_option maxRecDepth 2000 in
theorem engelsmaMaynardYDiagonalPairSum_eq_quadraticMomentSum
    (alpha : ℝ) (N : ℕ) (i j : Fin 42) :
    engelsmaMaynardYDiagonalPairSum alpha N i j =
      (smallKRealCoefficient i * smallKRealCoefficient j) *
        engelsmaMaynardYDiagonalQuadraticMomentSum alpha N
          (smallKExponentB i + smallKExponentB j)
          (smallKExponentC i + smallKExponentC j) := by
  classical
  unfold engelsmaMaynardYDiagonalPairSum
    engelsmaMaynardYDiagonalQuadraticMomentSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [smallKRealPairTerm_eq_simplexQuadratic]
  ring

set_option maxRecDepth 2000 in
theorem engelsmaMaynardYDiagonal_eq_pair_sum
    {alpha : ℝ} {N : ℕ}
    (hR : 1 < engelsmaMaynardRadius alpha N) :
    engelsmaMaynardYDiagonal alpha N =
      ∑ i : Fin 42, ∑ j : Fin 42,
        engelsmaMaynardYDiagonalPairSum alpha N i j := by
  rw [engelsmaMaynardYDiagonal_eq_polynomial_sum hR]
  unfold engelsmaMaynardYDiagonalPairSum
  simp_rw [smallKRealPolynomial_eq_sum_terms, pow_two,
    Finset.sum_mul_sum, smallKRealPairTerm, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

set_option maxRecDepth 2000 in
theorem engelsmaMaynardYDiagonal_eq_quadraticMoment_sum
    {alpha : ℝ} {N : ℕ}
    (hR : 1 < engelsmaMaynardRadius alpha N) :
    engelsmaMaynardYDiagonal alpha N =
      ∑ i : Fin 42, ∑ j : Fin 42,
        (smallKRealCoefficient i * smallKRealCoefficient j) *
          engelsmaMaynardYDiagonalQuadraticMomentSum alpha N
            (smallKExponentB i + smallKExponentB j)
            (smallKExponentC i + smallKExponentC j) := by
  rw [engelsmaMaynardYDiagonal_eq_pair_sum hR]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact engelsmaMaynardYDiagonalPairSum_eq_quadraticMomentSum alpha N i j

def normalizedEngelsmaMaynardYDiagonalQuadraticMoment
    (alpha : ℝ) (N b c : ℕ) : ℝ :=
  (((N : ℝ) / engelsmaMaynardModulus N) *
      engelsmaMaynardYDiagonalQuadraticMomentSum alpha N b c) /
    engelsmaMaynardScale alpha N

theorem maynardI_eq_quadraticMoment_sum :
    maynardI 105 smallKCandidate =
      ∑ i : Fin 42, ∑ j : Fin 42,
        (smallKRealCoefficient i * smallKRealCoefficient j) *
          ∫ t in maynardSimplex 105,
            simplexQuadraticIntegrand 105
              (smallKExponentB i + smallKExponentB j)
              (smallKExponentC i + smallKExponentC j) t := by
  rw [maynardI_eq_pair_integral_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show smallKRealPairTerm i j = fun t =>
      (smallKRealCoefficient i * smallKRealCoefficient j) *
        simplexQuadraticIntegrand 105
          (smallKExponentB i + smallKExponentB j)
          (smallKExponentC i + smallKExponentC j) t by
    funext t
    exact smallKRealPairTerm_eq_simplexQuadratic i j t]
  rw [integral_const_mul]

set_option maxRecDepth 2000 in
theorem tendsto_engelsmaMaynardYDiagonal_of_quadraticMoment_limits
    {alpha : ℝ} (halpha : 0 < alpha)
    (hMoment : ∀ i j : Fin 42,
      Tendsto (fun N : ℕ =>
        normalizedEngelsmaMaynardYDiagonalQuadraticMoment alpha N
          (smallKExponentB i + smallKExponentB j)
          (smallKExponentC i + smallKExponentC j))
        atTop (nhds
          (∫ t in maynardSimplex 105,
            simplexQuadraticIntegrand 105
              (smallKExponentB i + smallKExponentB j)
              (smallKExponentC i + smallKExponentC j) t))) :
    Tendsto (fun N : ℕ =>
      (((N : ℝ) / engelsmaMaynardModulus N) *
        engelsmaMaynardYDiagonal alpha N) /
          engelsmaMaynardScale alpha N)
      atTop (nhds (maynardI 105 smallKCandidate)) := by
  have hsum : Tendsto (fun N : ℕ =>
      ∑ i : Fin 42, ∑ j : Fin 42,
        (smallKRealCoefficient i * smallKRealCoefficient j) *
          normalizedEngelsmaMaynardYDiagonalQuadraticMoment alpha N
            (smallKExponentB i + smallKExponentB j)
            (smallKExponentC i + smallKExponentC j))
      atTop (nhds
        (∑ i : Fin 42, ∑ j : Fin 42,
          (smallKRealCoefficient i * smallKRealCoefficient j) *
            ∫ t in maynardSimplex 105,
              simplexQuadraticIntegrand 105
                (smallKExponentB i + smallKExponentB j)
                (smallKExponentC i + smallKExponentC j) t)) := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact (hMoment i j).const_mul
      (smallKRealCoefficient i * smallKRealCoefficient j)
  rw [← maynardI_eq_quadraticMoment_sum] at hsum
  apply hsum.congr'
  filter_upwards [eventually_one_lt_engelsmaMaynardRadius halpha] with N hR
  rw [engelsmaMaynardYDiagonal_eq_quadraticMoment_sum hR]
  unfold normalizedEngelsmaMaynardYDiagonalQuadraticMoment
  simp_rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end BoundedGaps.Maynard
