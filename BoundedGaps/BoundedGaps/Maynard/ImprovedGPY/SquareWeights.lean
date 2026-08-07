import BoundedGaps.Maynard.ImprovedGPY.Positivity

/-!
# Finite multidimensional square weights

This is the finite-support form of Maynard2013v3, equation `eq:WChoice`
(source lines 171--175).  The later arithmetic restrictions on the
coefficients are deliberately separate from this elementary wrapper.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- A divisor tuple assigns one natural divisor to each shift in `H`. -/
def divisorTupleCondition (H : Finset ℕ) (n : ℕ) (d : H → ℕ) : Prop :=
  ∀ h : H, d h ∣ n + h.1

/-- A finite-support multidimensional Selberg square weight. -/
noncomputable def squareDivisorWeight (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (n : ℕ) : ℝ :=
  by
    classical
    exact (∑ d ∈ D.filter (divisorTupleCondition H n), lambda d)^2

theorem squareDivisorWeight_nonneg (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (n : ℕ) :
    0 ≤ squareDivisorWeight H D lambda n := by
  exact sq_nonneg _

/-- Eventual positive excess using finite-support square divisor weights. -/
def HasEventuallyPositiveSquareDivisorSieveExcess
    (H : Finset ℕ) (rho : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ D : Finset (H → ℕ), ∃ lambda : (H → ℕ) → ℝ,
      0 < sieveExcess H N rho (squareDivisorWeight H D lambda)

theorem hasEventuallyPositiveSquareDivisorSieveExcess_implies
    {H : Finset ℕ} {rho : ℝ}
    (h : HasEventuallyPositiveSquareDivisorSieveExcess H rho) :
    HasEventuallyPositiveSieveExcess H rho := by
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨D, lambda, hpositive⟩ := hN₀ N hN
  refine ⟨squareDivisorWeight H D lambda, ?_, hpositive⟩
  intro n _
  exact squareDivisorWeight_nonneg H D lambda n

theorem boundedGapsStatement_of_engelsma_eventuallyPositiveSquareDivisorSieveExcess
    (h : HasEventuallyPositiveSquareDivisorSieveExcess BoundedGaps.engelsmaTuple 1) :
    BoundedGaps.boundedGapsStatement :=
  boundedGapsStatement_of_engelsma_eventuallyPositiveSieveExcess
    (hasEventuallyPositiveSquareDivisorSieveExcess_implies h)

end BoundedGaps.Maynard
