import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelTerms
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.GCongr

/-!
# Finite dimension-one Rosser model sums

This forms Iwaniec's finite Section 7 sums and proves their regularity and support properties;
see `IWANIEC-ROSSER-SIEVE-1980`, printed pp. 193--194.
-/

open scoped BigOperators
open Set MeasureTheory

namespace PrimesRestrictedDigits

theorem support_dimensionOneRosserModelPlusTerm_subset (r : Nat) :
    Function.support (dimensionOneRosserModelPlusTerm r) ⊆
      Icc 1 (3 + 2 * (r : Real)) := by
  intro s hs
  simp only [mem_Icc]
  constructor
  · by_contra h
    exact hs (dimensionOneRosserModelPlusTerm_eq_zero_of_lt r
      (lt_of_not_ge h))
  · by_contra h
    exact hs (dimensionOneRosserModelPlusTerm_eq_zero_of_upper_le r
      (le_of_not_ge h))

theorem support_dimensionOneRosserModelMinusTerm_subset (r : Nat) :
    Function.support (dimensionOneRosserModelMinusTerm r) ⊆
      Icc 2 (2 + 2 * (r : Real)) := by
  intro s hs
  simp only [mem_Icc]
  constructor
  · by_contra h
    exact hs (dimensionOneRosserModelMinusTerm_eq_zero_of_lt r
      (lt_of_not_ge h))
  · by_contra h
    exact hs (dimensionOneRosserModelMinusTerm_eq_zero_of_upper_le r
      (le_of_not_ge h))

theorem tsupport_dimensionOneRosserModelPlusTerm_subset (r : Nat) :
    tsupport (dimensionOneRosserModelPlusTerm r) ⊆
      Icc 1 (3 + 2 * (r : Real)) := by
  rw [tsupport]
  exact closure_minimal
    (support_dimensionOneRosserModelPlusTerm_subset r) isClosed_Icc

theorem tsupport_dimensionOneRosserModelMinusTerm_subset (r : Nat) :
    tsupport (dimensionOneRosserModelMinusTerm r) ⊆
      Icc 2 (2 + 2 * (r : Real)) := by
  rw [tsupport]
  exact closure_minimal
    (support_dimensionOneRosserModelMinusTerm_subset r) isClosed_Icc

theorem dimensionOneRosserModelPlusTerm_hasCompactSupport (r : Nat) :
    HasCompactSupport (dimensionOneRosserModelPlusTerm r) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_dimensionOneRosserModelPlusTerm_subset r)

theorem dimensionOneRosserModelMinusTerm_hasCompactSupport (r : Nat) :
    HasCompactSupport (dimensionOneRosserModelMinusTerm r) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_dimensionOneRosserModelMinusTerm_subset r)

/-- The upper model correction through rank `R`. -/
noncomputable def dimensionOneRosserModelPlusPartialSum
    (R : Nat) (s : Real) : Real :=
  ∑ r ∈ Finset.range (R + 1), dimensionOneRosserModelPlusTerm r s

/-- The lower model correction through rank `R`. -/
noncomputable def dimensionOneRosserModelMinusPartialSum
    (R : Nat) (s : Real) : Real :=
  ∑ r ∈ Finset.Icc 1 R, dimensionOneRosserModelMinusTerm r s

@[simp] theorem dimensionOneRosserModelPlusPartialSum_zero (s : Real) :
    dimensionOneRosserModelPlusPartialSum 0 s =
      dimensionOneRosserModelPlusTerm 0 s := by
  simp [dimensionOneRosserModelPlusPartialSum]

@[simp] theorem dimensionOneRosserModelMinusPartialSum_zero (s : Real) :
    dimensionOneRosserModelMinusPartialSum 0 s = 0 := by
  simp [dimensionOneRosserModelMinusPartialSum]

theorem dimensionOneRosserModelPlusPartialSum_succ
    (R : Nat) (s : Real) :
    dimensionOneRosserModelPlusPartialSum (R + 1) s =
      dimensionOneRosserModelPlusPartialSum R s +
        dimensionOneRosserModelPlusTerm (R + 1) s := by
  simp [dimensionOneRosserModelPlusPartialSum, Finset.sum_range_succ]

theorem dimensionOneRosserModelMinusPartialSum_succ
    (R : Nat) (s : Real) :
    dimensionOneRosserModelMinusPartialSum (R + 1) s =
      dimensionOneRosserModelMinusPartialSum R s +
        dimensionOneRosserModelMinusTerm (R + 1) s := by
  rw [dimensionOneRosserModelMinusPartialSum,
    dimensionOneRosserModelMinusPartialSum,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ R + 1)]

theorem dimensionOneRosserModelPlusPartialSum_nonneg
    (R : Nat) (s : Real) :
    0 ≤ dimensionOneRosserModelPlusPartialSum R s := by
  apply Finset.sum_nonneg
  intro r hr
  exact dimensionOneRosserModelPlusTerm_nonneg r s

theorem dimensionOneRosserModelMinusPartialSum_nonneg
    (R : Nat) (s : Real) :
    0 ≤ dimensionOneRosserModelMinusPartialSum R s := by
  apply Finset.sum_nonneg
  intro r hr
  exact dimensionOneRosserModelMinusTerm_nonneg r s

theorem dimensionOneRosserModelPlusPartialSum_continuousOn (R : Nat) :
    ContinuousOn (dimensionOneRosserModelPlusPartialSum R) (Ici 1) := by
  unfold dimensionOneRosserModelPlusPartialSum
  apply continuousOn_finsetSum
  intro r hr
  exact dimensionOneRosserModelPlusTerm_continuousOn r

theorem dimensionOneRosserModelMinusPartialSum_continuousOn (R : Nat) :
    ContinuousOn (dimensionOneRosserModelMinusPartialSum R) (Ici 2) := by
  unfold dimensionOneRosserModelMinusPartialSum
  apply continuousOn_finsetSum
  intro r hr
  exact dimensionOneRosserModelMinusTerm_continuousOn r

theorem dimensionOneRosserModelPartialSum_antitoneOn (R : Nat) :
    AntitoneOn (dimensionOneRosserModelPlusPartialSum R) (Ici 1) ∧
      AntitoneOn (dimensionOneRosserModelMinusPartialSum R) (Ici 2) := by
  constructor
  · intro x hx y hy hxy
    apply Finset.sum_le_sum
    intro r hr
    exact (dimensionOneRosserModelTerm_antitoneOn r).1 hx hy hxy
  · intro x hx y hy hxy
    apply Finset.sum_le_sum
    intro r hr
    exact (dimensionOneRosserModelTerm_antitoneOn r).2 hx hy hxy

theorem dimensionOneRosserModelPlusPartialSum_eq_zero_of_lt
    (R : Nat) {s : Real} (hs : s < 1) :
    dimensionOneRosserModelPlusPartialSum R s = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  exact dimensionOneRosserModelPlusTerm_eq_zero_of_lt r hs

theorem dimensionOneRosserModelMinusPartialSum_eq_zero_of_lt
    (R : Nat) {s : Real} (hs : s < 2) :
    dimensionOneRosserModelMinusPartialSum R s = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  exact dimensionOneRosserModelMinusTerm_eq_zero_of_lt r hs

theorem dimensionOneRosserModelPlusPartialSum_eq_zero_of_upper_le
    (R : Nat) {s : Real} (hs : 3 + 2 * (R : Real) ≤ s) :
    dimensionOneRosserModelPlusPartialSum R s = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  apply dimensionOneRosserModelPlusTerm_eq_zero_of_upper_le r
  have hrR : r ≤ R := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  exact le_trans (by gcongr) hs

theorem dimensionOneRosserModelMinusPartialSum_eq_zero_of_upper_le
    (R : Nat) {s : Real} (hs : 2 + 2 * (R : Real) ≤ s) :
    dimensionOneRosserModelMinusPartialSum R s = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  apply dimensionOneRosserModelMinusTerm_eq_zero_of_upper_le r
  have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
  exact le_trans (by gcongr) hs

theorem support_dimensionOneRosserModelPlusPartialSum_subset (R : Nat) :
    Function.support (dimensionOneRosserModelPlusPartialSum R) ⊆
      Icc 1 (3 + 2 * (R : Real)) := by
  intro s hs
  simp only [mem_Icc]
  constructor
  · by_contra h
    exact hs (dimensionOneRosserModelPlusPartialSum_eq_zero_of_lt R
      (lt_of_not_ge h))
  · by_contra h
    exact hs (dimensionOneRosserModelPlusPartialSum_eq_zero_of_upper_le R
      (le_of_not_ge h))

theorem support_dimensionOneRosserModelMinusPartialSum_subset (R : Nat) :
    Function.support (dimensionOneRosserModelMinusPartialSum R) ⊆
      Icc 2 (2 + 2 * (R : Real)) := by
  intro s hs
  simp only [mem_Icc]
  constructor
  · by_contra h
    exact hs (dimensionOneRosserModelMinusPartialSum_eq_zero_of_lt R
      (lt_of_not_ge h))
  · by_contra h
    exact hs (dimensionOneRosserModelMinusPartialSum_eq_zero_of_upper_le R
      (le_of_not_ge h))

theorem tsupport_dimensionOneRosserModelPlusPartialSum_subset (R : Nat) :
    tsupport (dimensionOneRosserModelPlusPartialSum R) ⊆
      Icc 1 (3 + 2 * (R : Real)) := by
  rw [tsupport]
  exact closure_minimal
    (support_dimensionOneRosserModelPlusPartialSum_subset R) isClosed_Icc

theorem tsupport_dimensionOneRosserModelMinusPartialSum_subset (R : Nat) :
    tsupport (dimensionOneRosserModelMinusPartialSum R) ⊆
      Icc 2 (2 + 2 * (R : Real)) := by
  rw [tsupport]
  exact closure_minimal
    (support_dimensionOneRosserModelMinusPartialSum_subset R) isClosed_Icc

theorem dimensionOneRosserModelPlusPartialSum_hasCompactSupport (R : Nat) :
    HasCompactSupport (dimensionOneRosserModelPlusPartialSum R) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_dimensionOneRosserModelPlusPartialSum_subset R)

theorem dimensionOneRosserModelMinusPartialSum_hasCompactSupport (R : Nat) :
    HasCompactSupport (dimensionOneRosserModelMinusPartialSum R) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_dimensionOneRosserModelMinusPartialSum_subset R)

theorem integrable_shiftedRosserKernel_plusPartialSum (R : Nat) :
    Integrable
      (shiftedRosserKernel (dimensionOneRosserModelPlusPartialSum R)) :=
  integrable_shiftedRosserKernel (by norm_num)
    (dimensionOneRosserModelPlusPartialSum_continuousOn R)
    (fun s => dimensionOneRosserModelPlusPartialSum_eq_zero_of_lt R)
    (fun s => dimensionOneRosserModelPlusPartialSum_eq_zero_of_upper_le R)

theorem integrable_shiftedRosserKernel_minusPartialSum (R : Nat) :
    Integrable
      (shiftedRosserKernel (dimensionOneRosserModelMinusPartialSum R)) :=
  integrable_shiftedRosserKernel (by norm_num)
    (dimensionOneRosserModelMinusPartialSum_continuousOn R)
    (fun s => dimensionOneRosserModelMinusPartialSum_eq_zero_of_lt R)
    (fun s => dimensionOneRosserModelMinusPartialSum_eq_zero_of_upper_le R)

theorem integrable_shiftedRosserKernel_plusTerm (r : Nat) :
    Integrable (shiftedRosserKernel (dimensionOneRosserModelPlusTerm r)) :=
  integrable_shiftedRosserKernel (by norm_num)
    (dimensionOneRosserModelPlusTerm_continuousOn r)
    (fun s => dimensionOneRosserModelPlusTerm_eq_zero_of_lt r)
    (fun s => dimensionOneRosserModelPlusTerm_eq_zero_of_upper_le r)

theorem integrable_shiftedRosserKernel_minusTerm (r : Nat) :
    Integrable (shiftedRosserKernel (dimensionOneRosserModelMinusTerm r)) :=
  integrable_shiftedRosserKernel (by norm_num)
    (dimensionOneRosserModelMinusTerm_continuousOn r)
    (fun s => dimensionOneRosserModelMinusTerm_eq_zero_of_lt r)
    (fun s => dimensionOneRosserModelMinusTerm_eq_zero_of_upper_le r)

end PrimesRestrictedDigits
