import BoundedGaps.BombieriVinogradov.Analytic.VaughanTwistedDecomposition

/-!
# Vaughan's second-term factor reindex

This file reindexes the second twisted Vaughan term from its endpoint and
factor-antidiagonal form to `AkbaryHambrook2013v2`, Section 6, p. 19.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Positive Möbius indices that can contribute to the second Vaughan term. -/
def vaughanSecondTermIndices (V : ℝ) (y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ V)

private def vaughanSecondTermFactorPairs (y : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 y ×ˢ Finset.Ioc 0 y).filter
    (fun p ↦ p.1 * p.2 ≤ y)

private theorem sum_divisorsAntidiagonal_up_to_eq_sum_secondTermFactorPairs
    {y : ℕ} {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Ioc 0 y,
      ∑ p ∈ n.divisorsAntidiagonal, f p.1 p.2) =
      ∑ p ∈ vaughanSecondTermFactorPairs y, f p.1 p.2 := by
  let T : Finset ℕ := Finset.Ioc 0 y
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  have hmaps : ∀ p ∈ vaughanSecondTermFactorPairs y, g p ∈ T := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp₁.1 hp₂.1, hprod⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := vaughanSecondTermFactorPairs y) (t := T) hmaps
    (fun p ↦ f p.1 p.2)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (N := y)]
  · apply Finset.sum_congr
    · ext p
      simp only [vaughanSecondTermFactorPairs, g, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hprod⟩
        exact ⟨⟨hp, hprod.le.trans (Finset.mem_Ioc.mp hn).2⟩, hprod⟩
      · rintro ⟨⟨hp, _⟩, hprod⟩
        exact ⟨hp, hprod⟩
    · intro p _
      rfl
  · exact (Finset.mem_Ioc.mp hn).1.ne'
  · exact (Finset.mem_Ioc.mp hn).2

private theorem mem_secondTermFactorPairs_filter_iff
    {V : ℝ} {y : ℕ} (p : ℕ × ℕ) :
    p ∈ (vaughanSecondTermFactorPairs y).filter
        (fun p ↦ (p.2 : ℝ) ≤ V) ↔
      p.2 ∈ vaughanSecondTermIndices V y ∧
        p.1 ∈ Finset.Icc 1 (y / p.2) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hpV⟩
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hp₂.1, hp₂.2⟩, hpV⟩,
      Finset.mem_Icc.mpr ⟨hp₁.1,
        (Nat.le_div_iff_mul_le hp₂.1).mpr hprod⟩⟩
  · rintro ⟨hd, hh⟩
    rcases Finset.mem_filter.mp hd with ⟨hd, hdV⟩
    rw [Finset.mem_Icc] at hd hh
    have hprod : p.1 * p.2 ≤ y :=
      (Nat.le_div_iff_mul_le hd.1).mp hh.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Ioc.mpr
              ⟨hh.1, hh.2.trans (Nat.div_le_self y p.2)⟩,
            Finset.mem_Ioc.mpr hd⟩,
          hprod⟩,
        hdV⟩

/-- Reindex the second twisted Vaughan term by its Möbius index and the
positive logarithmic factor. -/
theorem vaughanTwistedSumTwo_eq_divisorLogSums
    (V : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTwistedSumTwo V y q χ =
      ∑ d ∈ vaughanSecondTermIndices V y,
        ((ArithmeticFunction.moebius d : ℝ) : ℂ) * χ d *
          ∑ h ∈ Finset.Icc 1 (y / d),
            χ h * (Real.log h : ℂ) := by
  unfold vaughanTwistedSumTwo
  rw [show Finset.Icc 1 y = Finset.Ioc 0 y by
    simpa using Finset.Icc_succ_left_eq_Ioc 0 y]
  simp_rw [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  calc
    (∑ n ∈ Finset.Ioc 0 y,
        ∑ p ∈ n.divisorsAntidiagonal.filter
            (fun p : ℕ × ℕ ↦ (p.2 : ℝ) ≤ V),
          χ n *
            (((ArithmeticFunction.moebius p.2 : ℝ) : ℂ) *
              (Real.log p.1 : ℂ))) =
        ∑ n ∈ Finset.Ioc 0 y,
          ∑ p ∈ n.divisorsAntidiagonal,
            if (p.2 : ℝ) ≤ V then
              χ (p.1 * p.2) *
                (((ArithmeticFunction.moebius p.2 : ℝ) : ℂ) *
                  (Real.log p.1 : ℂ))
            else 0 := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1]
      simp only [Nat.cast_mul]
    _ = ∑ p ∈ vaughanSecondTermFactorPairs y,
          if (p.2 : ℝ) ≤ V then
            χ (p.1 * p.2) *
              (((ArithmeticFunction.moebius p.2 : ℝ) : ℂ) *
                (Real.log p.1 : ℂ))
          else 0 :=
      sum_divisorsAntidiagonal_up_to_eq_sum_secondTermFactorPairs
        (fun h d ↦ if (d : ℝ) ≤ V then
          χ (h * d) *
            (((ArithmeticFunction.moebius d : ℝ) : ℂ) *
              (Real.log h : ℂ))
          else 0)
    _ = ∑ p ∈ (vaughanSecondTermFactorPairs y).filter
            (fun p ↦ (p.2 : ℝ) ≤ V),
          ((ArithmeticFunction.moebius p.2 : ℝ) : ℂ) * χ p.2 *
            (χ p.1 * (Real.log p.1 : ℂ)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpV : (p.2 : ℝ) ≤ V
      · rw [if_pos hpV, if_pos hpV, map_mul]
        ring
      · rw [if_neg hpV, if_neg hpV]
    _ = ∑ d ∈ vaughanSecondTermIndices V y,
          ∑ h ∈ Finset.Icc 1 (y / d),
            ((ArithmeticFunction.moebius d : ℝ) : ℂ) * χ d *
              (χ h * (Real.log h : ℂ)) := by
      exact Finset.sum_finset_product_right'
        ((vaughanSecondTermFactorPairs y).filter
          (fun p : ℕ × ℕ ↦ (p.2 : ℝ) ≤ V))
        (vaughanSecondTermIndices V y)
        (fun d ↦ Finset.Icc 1 (y / d))
        mem_secondTermFactorPairs_filter_iff
        (f := fun h d ↦
          ((ArithmeticFunction.moebius d : ℝ) : ℂ) * χ d *
            (χ h * (Real.log h : ℂ)))

/-- The number of positive integer indices below a real cutoff is at most the
cutoff itself. -/
theorem card_vaughanSecondTermIndices_le_cutoff
    {V : ℝ} (hV : 1 ≤ V) (y : ℕ) :
    ((vaughanSecondTermIndices V y).card : ℝ) ≤ V := by
  have hsubset : vaughanSecondTermIndices V y ⊆ Finset.Icc 1 ⌊V⌋₊ := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdy, hdV⟩
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hdy).1, Nat.le_floor hdV⟩
  have hcard := Finset.card_le_card hsubset
  calc
    ((vaughanSecondTermIndices V y).card : ℝ) ≤
        ((Finset.Icc 1 ⌊V⌋₊).card : ℝ) := by exact_mod_cast hcard
    _ = (⌊V⌋₊ : ℝ) := by simp [Nat.card_Icc]
    _ ≤ V := Nat.floor_le (zero_le_one.trans hV)

end

end BoundedGaps.Maynard
