import PrimesRestrictedDigits.Digits.PaperRepresentation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-! # Intervals -/

open scoped BigOperators

namespace PrimesRestrictedDigits

/- These finsets make the endpoint change between Eq. (5.1) and Section 11
  explicit. Closed membership has its real-interval meaning for nonnegative
  upper endpoints; the underlying finset relations hold for all endpoints. -/
noncomputable def naturalClosedInterval (lower upper : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.ceil lower) (Nat.floor upper)

noncomputable def naturalLeftClosedRightOpenInterval (lower upper : ℝ) : Finset ℕ :=
  Finset.Ico (Nat.ceil lower) (Nat.ceil upper)

theorem mem_naturalClosedInterval {lower upper : ℝ} (hupper : 0 ≤ upper) {n : ℕ} :
    n ∈ naturalClosedInterval lower upper ↔
      lower ≤ (n : ℝ) ∧ (n : ℝ) ≤ upper := by
  simp [naturalClosedInterval, Nat.ceil_le, Nat.le_floor_iff hupper]

theorem mem_naturalLeftClosedRightOpenInterval {lower upper : ℝ} {n : ℕ} :
    n ∈ naturalLeftClosedRightOpenInterval lower upper ↔
      lower ≤ (n : ℝ) ∧ (n : ℝ) < upper := by
  simp [naturalLeftClosedRightOpenInterval, Nat.ceil_le, Nat.lt_ceil]

theorem naturalLeftClosedRightOpenInterval_subset_closed (lower upper : ℝ) :
    naturalLeftClosedRightOpenInterval lower upper ⊆ naturalClosedInterval lower upper := by
  intro n hn
  rw [naturalLeftClosedRightOpenInterval, Finset.mem_Ico] at hn
  rw [naturalClosedInterval, Finset.mem_Icc]
  refine ⟨hn.1, ?_⟩
  apply Nat.succ_le_succ_iff.mp
  exact (Nat.succ_le_iff.mpr hn.2).trans (Nat.ceil_le_floor_add_one upper)

private theorem naturalClosedInterval_sdiff_halfOpen_subset_singleton (lower upper : ℝ) :
    naturalClosedInterval lower upper \ naturalLeftClosedRightOpenInterval lower upper ⊆
      {Nat.floor upper} := by
  intro n hn
  have hnmem := Finset.mem_sdiff.mp hn
  have hnclosed : Nat.ceil lower ≤ n ∧ n ≤ Nat.floor upper := by
    simpa [naturalClosedInterval] using hnmem.1
  have hceil : Nat.ceil upper ≤ n := by
    apply le_of_not_gt
    intro hnceil
    exact hnmem.2 (by
      simp [naturalLeftClosedRightOpenInterval, hnclosed.1, hnceil])
  have hfloor : Nat.floor upper ≤ n := (Nat.floor_le_ceil upper).trans hceil
  simp [le_antisymm hnclosed.2 hfloor]

theorem filteredNaturalClosedInterval_sdiff_halfOpen_subset_singleton
    (P : ℕ → Prop) [DecidablePred P] (lower upper : ℝ) :
    (naturalClosedInterval lower upper).filter P \
        (naturalLeftClosedRightOpenInterval lower upper).filter P ⊆
      {Nat.floor upper} := by
  intro n hn
  have hnmem := Finset.mem_sdiff.mp hn
  have hnclosed := (Finset.mem_filter.mp hnmem.1).1
  have hnP := (Finset.mem_filter.mp hnmem.1).2
  apply naturalClosedInterval_sdiff_halfOpen_subset_singleton lower upper
  exact Finset.mem_sdiff.mpr ⟨hnclosed, fun hnopen =>
    hnmem.2 (Finset.mem_filter.mpr ⟨hnopen, hnP⟩)⟩

theorem sum_filteredNaturalClosedInterval_sub_halfOpen_bounds
    (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (lower upper : ℝ) :
    0 ≤ (∑ n ∈ (naturalClosedInterval lower upper).filter P, f n) -
        ∑ n ∈ (naturalLeftClosedRightOpenInterval lower upper).filter P, f n ∧
    (∑ n ∈ (naturalClosedInterval lower upper).filter P, f n) -
        ∑ n ∈ (naturalLeftClosedRightOpenInterval lower upper).filter P, f n ≤
      f (Nat.floor upper) := by
  let closed := (naturalClosedInterval lower upper).filter P
  let halfOpen := (naturalLeftClosedRightOpenInterval lower upper).filter P
  have hsubset : halfOpen ⊆ closed :=
    Finset.filter_subset_filter _
      (naturalLeftClosedRightOpenInterval_subset_closed lower upper)
  rw [← Finset.sum_sdiff_eq_sub hsubset]
  constructor
  · exact Finset.sum_nonneg fun n hn => hf n
  · calc
      (∑ n ∈ closed \ halfOpen, f n) ≤ ∑ n ∈ {Nat.floor upper}, f n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact filteredNaturalClosedInterval_sdiff_halfOpen_subset_singleton P lower upper
        · intro n hn hndiff
          exact hf n
      _ = f (Nat.floor upper) := Finset.sum_singleton _ _

/- `Nat.lt_ceil` removes the auxiliary range bound and exposes the strict real
  cutoff used in the published theorem. -/
theorem mem_restrictedNumbers {a : Fin 10} {X : ℝ} {n : ℕ} :
    n ∈ restrictedNumbers a X ↔ (n : ℝ) < X ∧ omitsDecimalDigit a n := by
  classical
  simp [restrictedNumbers, Nat.lt_ceil]

theorem restrictedNumbers_subset_range (a : Fin 10) (X : ℝ) :
    restrictedNumbers a X ⊆ Finset.range (Nat.ceil X) := by
  classical
  intro n hn
  exact (Finset.mem_filter.1 hn).1

theorem mem_restrictedNumbers_iff_paperRepresentation {a : Fin 10} {X : ℝ} {n : ℕ} :
    n ∈ restrictedNumbers a X ↔
      (n : ℝ) < X ∧ paperDecimalRepresentation a n := by
  rw [mem_restrictedNumbers, paperDecimalRepresentation_iff_omitsDecimalDigit]

theorem log_pos_of_four_le {X : ℝ} (hX : 4 ≤ X) : 0 < Real.log X := by
  exact Real.log_pos (by linarith)

theorem log_ten_pos : 0 < Real.log (10 : ℝ) := by
  exact Real.log_pos (by norm_num)

theorem restrictedScale_rpow_pos {X : ℝ} (hX : 4 ≤ X) :
    0 < X ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) := by
  exact Real.rpow_pos_of_pos (by linarith) _

end PrimesRestrictedDigits
