import Waring.Analytic.ChenTenMajorArcTranslation
import Waring.Analytic.ChenTenSingularSeriesTail

/-!
# Reindexing Chen's finite singular series

Reduced arc indices are reindexed by their denominator and canonical unit
numerator.  The resulting finite sum is exactly the singular-series partial
sum through `Nat.sqrt P`.
-/

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

private theorem sum_chenTenIndexedSingularTerm_fiber
    (P N q : Nat) [NeZero q] (hq : 0 < q) (hqcut : q ^ 2 ≤ P) :
    (∑ i ∈ (Finset.univ : Finset (ChenTenArcIndex P))
        with i.denominator = q, chenTenIndexedSingularTerm N i) =
      chenTenSingularCoefficient q N := by
  let s : Finset (ChenTenArcIndex P) :=
    Finset.univ.filter fun i => i.denominator = q
  let t : Finset (ZMod q) :=
    Finset.univ.filter IsUnit
  have hqleP : q ≤ P := by
    exact (Nat.le_pow (a := q) (b := 2) (by norm_num)).trans hqcut
  have hsum :
      (∑ i ∈ s, chenTenIndexedSingularTerm N i) =
        ∑ a ∈ t, chenTenSingularTerm q N a := by
    apply Finset.sum_bij (fun i _hi => (i.numerator : ZMod q))
    · intro i hi
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      have hiq : i.denominator = q := (Finset.mem_filter.mp hi).2
      have hunit := ChenTenArcIndex.numerator_isUnit i
      rw [hiq] at hunit
      exact hunit
    · intro i₁ hi₁ i₂ hi₂ heq
      have hiq₁ : i₁.denominator = q := (Finset.mem_filter.mp hi₁).2
      have hiq₂ : i₂.denominator = q := (Finset.mem_filter.mp hi₂).2
      apply ChenTenArcIndex.ext
      · have hv := congrArg ZMod.val heq
        have hi₁lt : i₁.numerator < q := by
          simpa [hiq₁] using i₁.numerator_lt_denominator
        have hi₂lt : i₂.numerator < q := by
          simpa [hiq₂] using i₂.numerator_lt_denominator
        simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hi₁lt,
          Nat.mod_eq_of_lt hi₂lt] using hv
      · exact (Finset.mem_filter.mp hi₁).2.trans
          (Finset.mem_filter.mp hi₂).2.symm
    · intro a ha
      have haunit : IsUnit a := (Finset.mem_filter.mp ha).2
      have hcop : Nat.Coprime a.val q := by
        apply (ZMod.isUnit_iff_coprime a.val q).mp
        simpa only [ZMod.natCast_zmod_val] using haunit
      have havalP : a.val < P + 1 := by
        exact Nat.lt_of_lt_of_le (ZMod.val_lt a)
          (hqleP.trans (Nat.le_succ P))
      have hqP : q < P + 1 := Nat.lt_succ_of_le hqleP
      let i : ChenTenArcIndex P :=
        ⟨(⟨a.val, havalP⟩, ⟨q, hqP⟩), by
          refine ⟨hq, ?_, hcop, hqcut⟩
          exact ZMod.val_lt a⟩
      have hi : i ∈ s := by
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      refine ⟨i, hi, ?_⟩
      exact ZMod.natCast_zmod_val a
    · intro i hi
      have hiq : i.denominator = q := (Finset.mem_filter.mp hi).2
      dsimp [chenTenIndexedSingularTerm]
      cases hiq
      rfl
  calc
    (∑ i ∈ (Finset.univ : Finset (ChenTenArcIndex P))
        with i.denominator = q, chenTenIndexedSingularTerm N i) =
        ∑ i ∈ s, chenTenIndexedSingularTerm N i := by rfl
    _ = ∑ a ∈ t, chenTenSingularTerm q N a := hsum
    _ = chenTenSingularCoefficient q N := by
      unfold chenTenSingularCoefficient t
      rw [Finset.sum_filter]

/-- The reduced major-arc indices enumerate exactly the singular-series
coefficients through the squared-denominator cutoff. -/
theorem sum_chenTenIndexedSingularTerm_eq_chenTenSingularSeriesPartial
    (P N : Nat) :
    (∑ i : ChenTenArcIndex P, chenTenIndexedSingularTerm N i) =
      chenTenSingularSeriesPartial N (Nat.sqrt P) := by
  let Q : Nat := Nat.sqrt P
  have hmap : ∀ i ∈ (Finset.univ : Finset (ChenTenArcIndex P)),
      i.denominator ∈ Finset.range (Q + 1) := by
    intro i hi
    rw [Finset.mem_range]
    have hqQ : i.denominator ≤ Nat.sqrt P := by
      rw [Nat.le_sqrt]
      simpa [pow_two] using i.denominator_sq_le
    dsimp [Q]
    omega
  have hgroup :
      (∑ q ∈ Finset.range (Q + 1),
        ∑ i ∈ (Finset.univ : Finset (ChenTenArcIndex P))
          with i.denominator = q, chenTenIndexedSingularTerm N i) =
        ∑ i ∈ (Finset.univ : Finset (ChenTenArcIndex P)),
          chenTenIndexedSingularTerm N i :=
    Finset.sum_fiberwise_of_maps_to hmap
      (fun i : ChenTenArcIndex P => chenTenIndexedSingularTerm N i)
  rw [← hgroup]
  unfold chenTenSingularSeriesPartial
  apply Finset.sum_congr rfl
  intro q hqmem
  by_cases hq0 : q = 0
  · subst q
    simp only [Finset.sum_filter]
    have hden : ∀ i : ChenTenArcIndex P, i.denominator ≠ 0 := by
      intro i
      exact Nat.ne_of_gt i.denominator_pos
    simp [hden]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hqQ : q ≤ Q := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hqmem)
    have hqcut : q ^ 2 ≤ P := by
      have hmul : q * q ≤ P := by
        simpa [Q] using (Nat.le_sqrt.mp (by simpa [Q] using hqQ))
      simpa [pow_two] using hmul
    letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
    rw [sum_chenTenIndexedSingularTerm_fiber P N q hqpos hqcut]
    simp [chenTenSingularCoefficientNat, hq0]

end

end Waring.Analytic
