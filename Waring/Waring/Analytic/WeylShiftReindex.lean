import Waring.Analytic.WeylCorrelation

/-!
# Positive-shift reindexing of finite correlations

The strict upper triangle in a finite correlation sum is reindexed by the
zero-based gap `h = x - y - 1`.  Thus the actual positive shift is `h + 1`.
This is the finite reindexing used at the start of Weyl differencing in Chen's
Lemma 9 [CHEN1964-EN, pp. 1555-1557].
-/

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate

/-- The strict upper-triangle correlation, reindexed by a positive shift
`h + 1` and the lower endpoint `y`. -/
theorem strictUpperCorrelation_eq_sum_positiveShift
    (z : Nat → Complex) (P : Nat) :
    strictUpperCorrelation z P =
      ∑ h ∈ Finset.range P, ∑ y ∈ Finset.range (P - h - 1),
        z (y + h + 1) * conj (z y) := by
  rw [strictUpperCorrelation, Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij
      (fun p _ ↦ ⟨p.1 - p.2 - 1, p.2⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    constructor
    · omega
    · omega
  · intro a ha b hb hab
    simp only [Finset.mem_sigma, Finset.mem_range] at ha hb
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at hab
    apply Sigma.ext
    · omega
    · exact heq_of_eq hab.2
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    refine ⟨⟨p.2 + p.1 + 1, p.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      constructor <;> omega
    · apply Sigma.ext
      · change p.2 + p.1 + 1 - p.2 - 1 = p.1
        omega
      · rfl
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    have hx : p.2 + (p.1 - p.2 - 1) + 1 = p.1 := by omega
    change z p.1 * conj (z p.2) =
      z (p.2 + (p.1 - p.2 - 1) + 1) * conj (z p.2)
    rw [hx]

end Waring.Analytic
