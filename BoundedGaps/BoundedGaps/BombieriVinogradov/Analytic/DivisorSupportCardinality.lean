import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Cardinality of analytic divisor support

This file converts the complete multiplicity-weighted divisor mass of an
analytic function on a compact set into a bound for its distinct divisor
support. Finiteness is established before using `Set.ncard`, and analyticity
excludes negative pole coefficients.

Semantic review: `SEM-508`.
-/

namespace BoundedGaps.Maynard

noncomputable section

private theorem cast_ncard_support_le_finsum
    {α : Type*} (f : α → ℤ) (hf : (Function.support f).Finite)
    (hone : ∀ x ∈ Function.support f, 1 ≤ f x) :
    ((Function.support f).ncard : ℝ) ≤
      ((∑ᶠ x : α, f x : ℤ) : ℝ) := by
  have hInt : ((Function.support f).ncard : ℤ) ≤ ∑ᶠ x : α, f x := by
    rw [Set.ncard_eq_toFinset_card _ hf]
    rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset)]
    · simpa using
        (Finset.card_nsmul_le_sum hf.toFinset f (1 : ℤ)
          (fun x hx => hone x (by simpa using hx)))
    · intro x hx
      simpa using hx
  exact_mod_cast hInt

/-- Distinct support of an analytic divisor on a compact set is bounded by
its complete multiplicity-weighted divisor mass. -/
theorem cast_ncard_support_divisor_le_finsum
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {K : Set 𝕜}
    (hf : AnalyticOnNhd 𝕜 f K) (hK : IsCompact K) :
    ((MeromorphicOn.divisor f K).support.ncard : ℝ) ≤
      ((∑ᶠ z : 𝕜, MeromorphicOn.divisor f K z : ℤ) : ℝ) := by
  let D : 𝕜 → ℤ := MeromorphicOn.divisor f K
  have hfinite : (Function.support D).Finite := by
    simpa [D] using
      hf.meromorphicOn.divisor_support_finite_of_subset hK Set.Subset.rfl
  have hone : ∀ z ∈ Function.support D, 1 ≤ D z := by
    intro z hz
    have hne : D z ≠ 0 := Function.mem_support.mp hz
    have hnonneg : 0 ≤ D z := by
      exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf) z
    omega
  simpa [D] using cast_ncard_support_le_finsum D hfinite hone

end

end BoundedGaps.Maynard
