import PrimesRestrictedDigits.Fourier.ClosedWindowMaximum
import PrimesRestrictedDigits.Fourier.HybridSourceResidueRelaxation

/-!
# Finite and compact-window factorization for the alternative hybrid bound

This file supplies the exact carrier and product algebra used before the `Sigma_2`--`Sigma_5`
estimates in published Lemma 10.7.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- Full mixed-radix coprimality implies that the first coordinate is reduced
modulo the first radix. -/
theorem hybridFullReduced_implies_firstReduced
    {d₁ d₂ d₃ : Nat} {b₁ : Fin d₁} {b₂ : Fin d₂} {b₃ : Fin d₃}
    (hfull :
      (mixedRadixTripleEquiv d₁ d₂ d₃ ((b₁, b₂), b₃)).val.Coprime
        (d₁ * d₂ * d₃)) :
    b₁.val.Coprime d₁ := by
  have hpair := hybridFullReduced_implies_pairReduced hfull
  let pair := (lowHighFinEquiv d₁ d₂ (b₁, b₂)).val
  have hzero : d₁ * b₂.val ≡ 0 [MOD d₁] :=
    Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_right d₁ b₂.val)
  have hmod : pair ≡ b₁.val [MOD d₁] := by
    have hadd := (Nat.ModEq.refl (n := d₁) b₁.val).add hzero
    convert hadd using 1
    all_goals simp [pair, lowHighFinEquiv_val]
  have hcop : pair.Coprime d₁ := by
    apply hpair.coprime_dvd_right
    exact ⟨d₂, by simp⟩
  apply Nat.coprime_iff_gcd_eq_one.mpr
  rw [← hmod.gcd_eq]
  exact hcop.gcd_eq_one

/-- The full carrier is contained in the carrier with reduced first
coordinate and unrestricted remaining coordinates. -/
theorem hybridFullReducedCarrier_subset_firstProduct (d₁ d₂ d₃ : Nat) :
    hybridFullReducedCarrier d₁ d₂ d₃ ⊆
      (reducedResidueCarrier d₁ ×ˢ (Finset.univ : Finset (Fin d₂))) ×ˢ
        (Finset.univ : Finset (Fin d₃)) := by
  intro x hx
  have hfull := (Finset.mem_filter.mp hx).2
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩,
    Finset.mem_univ _⟩
  exact mem_reducedResidueCarrier_iff.mpr
    (hybridFullReduced_implies_firstReduced hfull)

/-- Nonnegative sums may be enlarged from the full carrier to the
first-coordinate relaxed product carrier. -/
theorem sum_hybridFullReducedCarrier_le_sum_firstProduct
    {d₁ d₂ d₃ : Nat} (f : ((Fin d₁ × Fin d₂) × Fin d₃) → Real)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ hybridFullReducedCarrier d₁ d₂ d₃, f x) ≤
      ∑ x ∈
        (reducedResidueCarrier d₁ ×ˢ (Finset.univ : Finset (Fin d₂))) ×ˢ
          (Finset.univ : Finset (Fin d₃)),
        f x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (hybridFullReducedCarrier_subset_firstProduct d₁ d₂ d₃)
  intro x _ _
  exact hf x

/-- Exact reindexing of a complete low-first mixed-radix sum. -/
theorem sum_lowHighFinEquiv {M : Type*} [AddCommMonoid M]
    (m n : Nat) (f : Fin (m * n) → M) :
    (∑ x : Fin m × Fin n, f (lowHighFinEquiv m n x)) = ∑ y, f y := by
  exact (lowHighFinEquiv m n).sum_comp f

/-- A nonnegative finite fiber bound factors through a multiplier depending
only on the base coordinate. -/
theorem sum_product_mul_le_mul_sum_of_fiber_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (A : α → β → Real) (B : α → Real)
    (C : Real) (hB0 : ∀ x ∈ s, 0 ≤ B x)
    (hfiber : ∀ x ∈ s, (∑ y ∈ t, A x y) ≤ C) :
    (∑ z ∈ s ×ˢ t, A z.1 z.2 * B z.1) ≤
      C * ∑ x ∈ s, B x := by
  rw [Finset.sum_product]
  calc
    (∑ x ∈ s, ∑ y ∈ t, A x y * B x) =
        ∑ x ∈ s, (∑ y ∈ t, A x y) * B x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ s, C * B x := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hfiber x hx) (hB0 x hx)
    _ = C * ∑ x ∈ s, B x := by rw [Finset.mul_sum]

/-- A coupled compact-window maximum of a nonnegative product is at most the
product of separate maxima. The second window is enlarged by the scale. -/
theorem closedWindowMaximum_coupled_mul_le_mul
    {f g : Real → Real} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    {delta scale : Real} (hdelta : 0 ≤ delta) (hscale : 0 ≤ scale)
    (x y : Real) :
    closedWindowMaximum
        (fun eta => f (x + eta) * g (y + scale * eta)) delta 0 ≤
      closedWindowMaximum f delta x *
        closedWindowMaximum g (scale * delta) y := by
  have hleft : Continuous (fun eta => f (x + eta)) :=
    hf.comp (continuous_const.add continuous_id)
  have hright : Continuous (fun eta => g (y + scale * eta)) :=
    hg.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hproduct :
      Continuous (fun eta => f (x + eta) * g (y + scale * eta)) :=
    hleft.mul hright
  obtain ⟨eta, heta, hmax⟩ :=
    exists_closedWindowMaximum_eq hproduct hdelta 0
  rw [hmax]
  have hf_le : f (x + eta) ≤ closedWindowMaximum f delta x :=
    le_closedWindowMaximum hf hdelta x heta
  have hscaled :
      scale * eta ∈ Set.Icc (-(scale * delta)) (scale * delta) := by
    rw [Set.mem_Icc] at heta ⊢
    constructor <;> nlinarith
  have hg_le :
      g (y + scale * eta) ≤ closedWindowMaximum g (scale * delta) y :=
    le_closedWindowMaximum hg (mul_nonneg hscale hdelta) y hscaled
  simpa using mul_le_mul hf_le hg_le (hg0 _)
    (closedWindowMaximum_nonneg hf hf0 hdelta x)

end

end PrimesRestrictedDigits
