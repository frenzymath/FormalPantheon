import BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex
import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermReduction
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdCoefficient

/-!
# Vaughan's third-term endpoint reindex

This file formalizes the exact regrouping and small/large split preceding
Akbary--Hambrook2013v2, Section 6, equation (6.11). It contains no character
sum estimate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Positive grouped indices in the small third Vaughan term. -/
def vaughanThirdSmallIndices (U : ℝ) (y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter (fun t : ℕ ↦ (t : ℝ) ≤ U)

/-- Positive grouped indices in the large third Vaughan term. -/
def vaughanThirdLargeIndices (U V : ℝ) (y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter
    (fun t : ℕ ↦ U < (t : ℝ) ∧ (t : ℝ) ≤ U * V)

/-- The source's small signed component `S3'` of `-S3`. -/
noncomputable def vaughanTwistedSumThreeSmall
    (U V : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ t ∈ vaughanThirdSmallIndices U y,
    ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t *
      dirichletCharacterIntervalSum 1 (y / t) q χ

/-- The source's large signed component `S3''` of `-S3`. -/
noncomputable def vaughanTwistedSumThreeLarge
    (U V : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ t ∈ vaughanThirdLargeIndices U V y,
    ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t *
      dirichletCharacterIntervalSum 1 (y / t) q χ

private theorem mem_positiveFactorPairs_iff
    {y : ℕ} (p : ℕ × ℕ) :
    p ∈ positiveFactorPairs y ↔
      p.1 ∈ Finset.Icc 1 y ∧ p.2 ∈ Finset.Icc 1 (y / p.1) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact ⟨Finset.mem_Icc.mpr ⟨hp₁.1, hp₁.2⟩,
      Finset.mem_Icc.mpr ⟨hp₂.1,
        (Nat.le_div_iff_mul_le hp₁.1).mpr (by simpa [Nat.mul_comm] using hprod)⟩⟩
  · rintro ⟨ht, hr⟩
    rw [Finset.mem_Icc] at ht hr
    have hprod : p.1 * p.2 ≤ y := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ht.1).mp hr.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr ht,
          Finset.mem_Ioc.mpr
            ⟨hr.1, hr.2.trans (Nat.div_le_self y p.1)⟩⟩,
        hprod⟩

/-- Regroup the complete third Vaughan term by `t = m*d` and the remaining
positive factor `r`. -/
theorem neg_vaughanTwistedSumThree_eq_allCoefficientPrefixSums
    (U V : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    -vaughanTwistedSumThree U V y q χ =
      ∑ t ∈ Finset.Icc 1 y,
        ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t *
          dirichletCharacterIntervalSum 1 (y / t) q χ := by
  unfold vaughanTwistedSumThree
  change -(∑ n ∈ Finset.Icc 1 y,
      χ n * ((-∑ tr ∈ n.divisorsAntidiagonal,
        vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ)) = _
  rw [← Finset.sum_neg_distrib]
  calc
    (∑ n ∈ Finset.Icc 1 y,
        -(χ n * ((-∑ tr ∈ n.divisorsAntidiagonal,
          vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ))) =
        ∑ n ∈ Finset.Icc 1 y,
          ∑ tr ∈ n.divisorsAntidiagonal,
            χ n * ((vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Complex.ofReal_neg, Complex.ofReal_sum]
      simp only [mul_neg, neg_neg]
      rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.Ioc 0 y,
        ∑ tr ∈ n.divisorsAntidiagonal,
          χ (tr.1 * tr.2) *
            ((vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) := by
      rw [show Finset.Icc 1 y = Finset.Ioc 0 y by
        simpa using Finset.Icc_succ_left_eq_Ioc 0 y]
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro tr htr
      rw [← (Nat.mem_divisorsAntidiagonal.mp htr).1]
      simp only [Nat.cast_mul]
    _ = ∑ tr ∈ positiveFactorPairs y,
        χ (tr.1 * tr.2) *
          ((vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) :=
      sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
        (fun t r ↦
          χ (t * r) * ((vaughanThirdCoefficient U V t : ℝ) : ℂ))
    _ = ∑ t ∈ Finset.Icc 1 y,
        ∑ r ∈ Finset.Icc 1 (y / t),
          χ (t * r) *
            ((vaughanThirdCoefficient U V t : ℝ) : ℂ) := by
      exact Finset.sum_finset_product
        (positiveFactorPairs y) (Finset.Icc 1 y)
        (fun t ↦ Finset.Icc 1 (y / t)) mem_positiveFactorPairs_iff
    _ = ∑ t ∈ Finset.Icc 1 y,
        ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t *
          dirichletCharacterIntervalSum 1 (y / t) q χ := by
      unfold dirichletCharacterIntervalSum
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [map_mul]
      ring

/-- Above the product of nonnegative cutoffs, the restricted third coefficient
vanishes. -/
theorem vaughanThirdCoefficient_eq_zero_of_cutoffProduct_lt
    {U V : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V) {t : ℕ}
    (ht : U * V < (t : ℝ)) :
    vaughanThirdCoefficient U V t = 0 := by
  unfold vaughanThirdCoefficient
  apply Finset.sum_eq_zero
  intro md hmd
  rcases Finset.mem_filter.mp hmd with ⟨hmd, hcut⟩
  have hanti := Nat.mem_divisorsAntidiagonal.mp hmd
  have hle : (t : ℝ) ≤ U * V := by
    calc
      (t : ℝ) = (md.1 : ℝ) * (md.2 : ℝ) := by
        exact_mod_cast hanti.1.symm
      _ ≤ U * V := mul_le_mul hcut.1 hcut.2 (Nat.cast_nonneg _) hU
  exact False.elim ((not_le_of_gt ht) hle)

/-- Source-shaped regrouping with the coefficient support `t ≤ U*V`
inserted explicitly. -/
theorem neg_vaughanTwistedSumThree_eq_coefficientPrefixSums
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    -vaughanTwistedSumThree U V y q χ =
      ∑ t ∈ (Finset.Icc 1 y).filter
          (fun t : ℕ ↦ (t : ℝ) ≤ U * V),
        ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t *
          dirichletCharacterIntervalSum 1 (y / t) q χ := by
  rw [neg_vaughanTwistedSumThree_eq_allCoefficientPrefixSums]
  symm
  apply Finset.sum_filter_of_ne
  intro t _ht hterm
  by_contra htUV
  have hzero := vaughanThirdCoefficient_eq_zero_of_cutoffProduct_lt
    (zero_le_one.trans hU) (zero_le_one.trans hV) (lt_of_not_ge htUV)
  simp [hzero] at hterm

/-- Exact source split `-S3 = S3' + S3''`. -/
theorem neg_vaughanTwistedSumThree_eq_small_add_large
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    -vaughanTwistedSumThree U V y q χ =
      vaughanTwistedSumThreeSmall U V y q χ +
        vaughanTwistedSumThreeLarge U V y q χ := by
  let f : ℕ → ℂ := fun t ↦
    ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t *
      dirichletCharacterIntervalSum 1 (y / t) q χ
  have hUUV : U ≤ U * V := by
    calc
      U = U * 1 := (mul_one U).symm
      _ ≤ U * V := mul_le_mul_of_nonneg_left hV (zero_le_one.trans hU)
  have hunion :
      vaughanThirdSmallIndices U y ∪ vaughanThirdLargeIndices U V y =
        (Finset.Icc 1 y).filter (fun t : ℕ ↦ (t : ℝ) ≤ U * V) := by
    ext t
    simp only [vaughanThirdSmallIndices, vaughanThirdLargeIndices,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨ht, htU⟩ | ⟨ht, _htU, htUV⟩)
      · exact ⟨ht, htU.trans hUUV⟩
      · exact ⟨ht, htUV⟩
    · rintro ⟨ht, htUV⟩
      by_cases htU : (t : ℝ) ≤ U
      · exact Or.inl ⟨ht, htU⟩
      · exact Or.inr ⟨ht, lt_of_not_ge htU, htUV⟩
  have hdisjoint :
      Disjoint (vaughanThirdSmallIndices U y)
        (vaughanThirdLargeIndices U V y) := by
    rw [Finset.disjoint_left]
    intro t htSmall htLarge
    exact (not_lt_of_ge (Finset.mem_filter.mp htSmall).2)
      (Finset.mem_filter.mp htLarge).2.1
  rw [neg_vaughanTwistedSumThree_eq_coefficientPrefixSums hU hV]
  change (∑ t ∈ (Finset.Icc 1 y).filter
      (fun t : ℕ ↦ (t : ℝ) ≤ U * V), f t) = _
  rw [← hunion, Finset.sum_union hdisjoint]
  rfl

/-- The small positive-index count is at most its real cutoff. -/
theorem card_vaughanThirdSmallIndices_le_cutoff
    {U : ℝ} (hU : 1 ≤ U) (y : ℕ) :
    ((vaughanThirdSmallIndices U y).card : ℝ) ≤ U := by
  have hsubset :
      vaughanThirdSmallIndices U y ⊆ Finset.Icc 1 ⌊U⌋₊ := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨ht, htU⟩
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp ht).1, Nat.le_floor htU⟩
  have hcard := Finset.card_le_card hsubset
  calc
    ((vaughanThirdSmallIndices U y).card : ℝ) ≤
        ((Finset.Icc 1 ⌊U⌋₊).card : ℝ) := by exact_mod_cast hcard
    _ = (⌊U⌋₊ : ℝ) := by simp [Nat.card_Icc]
    _ ≤ U := Nat.floor_le (zero_le_one.trans hU)

end

end BoundedGaps.Maynard
