import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneConjugate
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Dimension-one Rosser model terms

This specializes Iwaniec's Section 7 model terms to `kappa = 1` and `beta = 2`; see
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 193--194.
-/

open Set MeasureTheory

namespace PrimesRestrictedDigits

private noncomputable def dimensionOneRosserModelTermPair :
    Nat -> (Real -> Real) × (Real -> Real)
  | 0 =>
      (fun s => if 1 ≤ s ∧ s ≤ 3 then 3 - s else 0,
        fun _ => 0)
  | r + 1 =>
      let previousPlus := (dimensionOneRosserModelTermPair r).1
      let currentMinus := fun s =>
        if 2 ≤ s then
          ∫ t in Ioi s, previousPlus (t - 1) / (t - 1)
        else 0
      let currentPlusTail := fun s =>
        ∫ t in Ioi s, currentMinus (t - 1) / (t - 1)
      (fun s =>
        if 1 ≤ s then currentPlusTail (max 3 s) else 0,
        currentMinus)

/-- The rank-`r` upper Section 7 model correction. -/
noncomputable def dimensionOneRosserModelPlusTerm
    (r : Nat) (s : Real) : Real :=
  (dimensionOneRosserModelTermPair r).1 s

/-- The rank-`r` lower Section 7 model correction. Rank zero is identically
zero. -/
noncomputable def dimensionOneRosserModelMinusTerm
    (r : Nat) (s : Real) : Real :=
  (dimensionOneRosserModelTermPair r).2 s

@[simp] theorem dimensionOneRosserModelPlusTerm_zero (s : Real) :
    dimensionOneRosserModelPlusTerm 0 s =
      if 1 ≤ s ∧ s ≤ 3 then 3 - s else 0 := by
  simp [dimensionOneRosserModelPlusTerm,
    dimensionOneRosserModelTermPair]

@[simp] theorem dimensionOneRosserModelMinusTerm_zero (s : Real) :
    dimensionOneRosserModelMinusTerm 0 s = 0 := by
  simp [dimensionOneRosserModelMinusTerm,
    dimensionOneRosserModelTermPair]

theorem dimensionOneRosserModelMinusTerm_succ_eq (r : Nat) (s : Real) :
    dimensionOneRosserModelMinusTerm (r + 1) s =
      if 2 ≤ s then
        ∫ t in Ioi s,
          dimensionOneRosserModelPlusTerm r (t - 1) / (t - 1)
      else 0 := by
  simp [dimensionOneRosserModelMinusTerm,
    dimensionOneRosserModelPlusTerm, dimensionOneRosserModelTermPair]

theorem dimensionOneRosserModelPlusTerm_succ_eq (r : Nat) (s : Real) :
    dimensionOneRosserModelPlusTerm (r + 1) s =
      if 1 ≤ s then
        ∫ t in Ioi (max 3 s),
          dimensionOneRosserModelMinusTerm (r + 1) (t - 1) / (t - 1)
      else 0 := by
  simp [dimensionOneRosserModelMinusTerm,
    dimensionOneRosserModelPlusTerm, dimensionOneRosserModelTermPair]

/-- The shifted quotient kernel in the dimension-one Section 7 recurrences. -/
noncomputable def shiftedRosserKernel
    (f : Real -> Real) (t : Real) : Real :=
  f (t - 1) / (t - 1)

private theorem continuousOn_shiftedRosserKernel {f : Real -> Real}
    {a : Real} (ha : 0 < a) (hf : ContinuousOn f (Ici a)) :
    ContinuousOn (shiftedRosserKernel f) (Ici (a + 1)) := by
  have hshift : ContinuousOn (fun t : Real => t - 1) (Ici (a + 1)) :=
    continuous_sub_right 1 |>.continuousOn
  have hmaps : MapsTo (fun t : Real => t - 1) (Ici (a + 1)) (Ici a) := by
    intro t ht
    simp only [mem_Ici] at ht ⊢
    linarith
  apply (hf.comp hshift hmaps).div hshift
  intro t ht
  simp only [mem_Ici] at ht
  linarith

private theorem shiftedRosserKernel_eq_zero_of_not_mem
    {f : Real -> Real} {a b t : Real}
    (hbelow : ∀ x, x < a -> f x = 0)
    (habove : ∀ x, b ≤ x -> f x = 0)
    (ht : t ∉ Icc (a + 1) (b + 1)) :
    shiftedRosserKernel f t = 0 := by
  rw [mem_Icc, not_and_or] at ht
  rcases ht with ht | ht
  · rw [shiftedRosserKernel, hbelow]
    · simp
    · linarith
  · rw [shiftedRosserKernel, habove]
    · simp
    · linarith

/-- A shifted Section 7 kernel is integrable when its source function is
continuous on its positive domain and vanishes outside a bounded interval. -/
theorem integrable_shiftedRosserKernel
    {f : Real -> Real} {a b : Real} (ha : 0 < a)
    (hf : ContinuousOn f (Ici a))
    (hbelow : ∀ x, x < a -> f x = 0)
    (habove : ∀ x, b ≤ x -> f x = 0) :
    Integrable (shiftedRosserKernel f) := by
  have hcont := continuousOn_shiftedRosserKernel ha hf
  have hcompact : IntegrableOn (shiftedRosserKernel f)
      (Icc (a + 1) (b + 1)) :=
    (hcont.mono Icc_subset_Ici_self).integrableOn_Icc
  exact hcompact.integrable_of_forall_notMem_eq_zero
    (fun t ht => shiftedRosserKernel_eq_zero_of_not_mem hbelow habove ht)

private structure DimensionOneRosserModelTermProperties (r : Nat) : Prop where
  plus_nonneg : ∀ s, 0 ≤ dimensionOneRosserModelPlusTerm r s
  minus_nonneg : ∀ s, 0 ≤ dimensionOneRosserModelMinusTerm r s
  plus_continuousOn :
    ContinuousOn (dimensionOneRosserModelPlusTerm r) (Ici 1)
  minus_continuousOn :
    ContinuousOn (dimensionOneRosserModelMinusTerm r) (Ici 2)
  plus_eq_zero_below :
    ∀ s, s < 1 -> dimensionOneRosserModelPlusTerm r s = 0
  minus_eq_zero_below :
    ∀ s, s < 2 -> dimensionOneRosserModelMinusTerm r s = 0
  plus_eq_zero_above :
    ∀ s, 3 + 2 * (r : Real) ≤ s ->
      dimensionOneRosserModelPlusTerm r s = 0
  minus_eq_zero_above :
    ∀ s, 2 + 2 * (r : Real) ≤ s ->
      dimensionOneRosserModelMinusTerm r s = 0

private theorem dimensionOneRosserModelTermProperties_zero :
    DimensionOneRosserModelTermProperties 0 := by
  constructor
  · intro s
    rw [dimensionOneRosserModelPlusTerm_zero]
    split_ifs with h
    · linarith [h.2]
    · exact le_rfl
  · intro s
    simp
  · have hcontinuous : Continuous (fun s : Real => max (3 - s) 0) :=
      (continuous_const.sub continuous_id).max continuous_const
    apply hcontinuous.continuousOn.congr
    intro s hs
    simp only [mem_Ici] at hs
    rw [dimensionOneRosserModelPlusTerm_zero]
    by_cases hs3 : s ≤ 3
    · rw [if_pos ⟨hs, hs3⟩]
      change 3 - s = max (3 - s) 0
      rw [max_eq_left (sub_nonneg.mpr hs3)]
    · have h3s : 3 ≤ s := le_of_not_ge hs3
      rw [if_neg (fun h => hs3 h.2)]
      change 0 = max (3 - s) 0
      rw [max_eq_right (sub_nonpos.mpr h3s)]
  · have heq : dimensionOneRosserModelMinusTerm 0 =
        (fun _ : Real => 0) := by
      funext s
      simp
    rw [heq]
    exact (continuous_const :
      Continuous (fun _ : Real => (0 : Real))).continuousOn
  · intro s hs
    rw [dimensionOneRosserModelPlusTerm_zero]
    simp [not_le.mpr hs]
  · intro s hs
    simp
  · intro s hs
    rw [dimensionOneRosserModelPlusTerm_zero]
    norm_num at hs
    split_ifs with h
    · linarith
    · rfl
  · intro s hs
    simp

private theorem integral_shiftedRosserKernel_nonneg
    {f : Real -> Real} (hf : ∀ x, 0 ≤ f x)
    {s : Real} (hs : 1 ≤ s) :
    0 ≤ ∫ t in Ioi s, shiftedRosserKernel f t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [mem_Ioi] at ht
  exact div_nonneg (hf (t - 1)) (by linarith)

private theorem integral_shiftedRosserKernel_eq_zero
    {f : Real -> Real} {b s : Real}
    (habove : ∀ x, b ≤ x -> f x = 0) (hbs : b + 1 ≤ s) :
    (∫ t in Ioi s, shiftedRosserKernel f t) = 0 := by
  calc
    (∫ t in Ioi s, shiftedRosserKernel f t) =
        ∫ _t in Ioi s, (0 : Real) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [mem_Ioi] at ht
      rw [shiftedRosserKernel, habove]
      · simp
      · linarith
    _ = 0 := by simp

private theorem dimensionOneRosserModelTermProperties_succ (r : Nat)
    (hr : DimensionOneRosserModelTermProperties r) :
    DimensionOneRosserModelTermProperties (r + 1) := by
  have hplusKernelIntegrable : Integrable
      (shiftedRosserKernel (dimensionOneRosserModelPlusTerm r)) :=
    integrable_shiftedRosserKernel (by norm_num) hr.plus_continuousOn
      hr.plus_eq_zero_below hr.plus_eq_zero_above
  have hminusNonneg : ∀ s,
      0 ≤ dimensionOneRosserModelMinusTerm (r + 1) s := by
    intro s
    rw [dimensionOneRosserModelMinusTerm_succ_eq]
    split_ifs with hs
    · simpa only [shiftedRosserKernel] using
        integral_shiftedRosserKernel_nonneg hr.plus_nonneg
          (show (1 : Real) ≤ s by linarith)
    · exact le_rfl
  have hminusBelow : ∀ s, s < 2 ->
      dimensionOneRosserModelMinusTerm (r + 1) s = 0 := by
    intro s hs
    rw [dimensionOneRosserModelMinusTerm_succ_eq]
    simp [not_le.mpr hs]
  have hminusAbove : ∀ s, 2 + 2 * ((r + 1 : Nat) : Real) ≤ s ->
      dimensionOneRosserModelMinusTerm (r + 1) s = 0 := by
    intro s hs
    have hs2 : (2 : Real) ≤ s := by
      push_cast at hs
      linarith [(Nat.cast_nonneg r : (0 : Real) ≤ (r : Real))]
    rw [dimensionOneRosserModelMinusTerm_succ_eq, if_pos hs2]
    simpa only [shiftedRosserKernel] using
      integral_shiftedRosserKernel_eq_zero hr.plus_eq_zero_above
        (show 3 + 2 * (r : Real) + 1 ≤ s by
          push_cast at hs
          linarith)
  have hminusContinuous : ContinuousOn
      (dimensionOneRosserModelMinusTerm (r + 1)) (Ici 2) := by
    have hprimitive : ContinuousOn
        (fun s => ∫ t in Ioi s,
          shiftedRosserKernel (dimensionOneRosserModelPlusTerm r) t)
        (Ici 2) :=
      hplusKernelIntegrable.integrableOn.continuousOn_Ici_primitive_Ioi
    apply hprimitive.congr
    intro s hs
    simp only [mem_Ici] at hs
    rw [dimensionOneRosserModelMinusTerm_succ_eq, if_pos hs]
    rfl
  have hminusKernelIntegrable : Integrable
      (shiftedRosserKernel
        (dimensionOneRosserModelMinusTerm (r + 1))) :=
    integrable_shiftedRosserKernel (by norm_num) hminusContinuous
      hminusBelow hminusAbove
  have hplusNonneg : ∀ s,
      0 ≤ dimensionOneRosserModelPlusTerm (r + 1) s := by
    intro s
    rw [dimensionOneRosserModelPlusTerm_succ_eq]
    split_ifs with hs
    · simpa only [shiftedRosserKernel] using
        integral_shiftedRosserKernel_nonneg hminusNonneg
          (show (1 : Real) ≤ max 3 s by linarith [le_max_left 3 s])
    · exact le_rfl
  have hplusBelow : ∀ s, s < 1 ->
      dimensionOneRosserModelPlusTerm (r + 1) s = 0 := by
    intro s hs
    rw [dimensionOneRosserModelPlusTerm_succ_eq]
    simp [not_le.mpr hs]
  have hplusAbove : ∀ s, 3 + 2 * ((r + 1 : Nat) : Real) ≤ s ->
      dimensionOneRosserModelPlusTerm (r + 1) s = 0 := by
    intro s hs
    have hs1 : (1 : Real) ≤ s := by
      push_cast at hs
      linarith [(Nat.cast_nonneg r : (0 : Real) ≤ (r : Real))]
    have hs3 : (3 : Real) ≤ s := by
      push_cast at hs
      linarith [(Nat.cast_nonneg r : (0 : Real) ≤ (r : Real))]
    rw [dimensionOneRosserModelPlusTerm_succ_eq, if_pos hs1,
      max_eq_right hs3]
    simpa only [shiftedRosserKernel] using
      integral_shiftedRosserKernel_eq_zero hminusAbove
        (show 2 + 2 * ((r + 1 : Nat) : Real) + 1 ≤ s by
          linarith)
  have hplusContinuous : ContinuousOn
      (dimensionOneRosserModelPlusTerm (r + 1)) (Ici 1) := by
    have hprimitive : ContinuousOn
        (fun s => ∫ t in Ioi s,
          shiftedRosserKernel
            (dimensionOneRosserModelMinusTerm (r + 1)) t) (Ici 3) :=
      hminusKernelIntegrable.integrableOn.continuousOn_Ici_primitive_Ioi
    have hmaxContinuous : ContinuousOn (fun s : Real => max 3 s) (Ici 1) :=
      (continuous_const.max continuous_id).continuousOn
    have hmaxMaps : MapsTo (fun s : Real => max 3 s) (Ici 1) (Ici 3) := by
      intro s hs
      exact le_max_left 3 s
    apply (hprimitive.comp hmaxContinuous hmaxMaps).congr
    intro s hs
    simp only [mem_Ici] at hs
    rw [dimensionOneRosserModelPlusTerm_succ_eq, if_pos hs]
    rfl
  exact {
    plus_nonneg := hplusNonneg
    minus_nonneg := hminusNonneg
    plus_continuousOn := hplusContinuous
    minus_continuousOn := hminusContinuous
    plus_eq_zero_below := hplusBelow
    minus_eq_zero_below := hminusBelow
    plus_eq_zero_above := hplusAbove
    minus_eq_zero_above := hminusAbove }

private theorem dimensionOneRosserModelTermProperties_all (r : Nat) :
    DimensionOneRosserModelTermProperties r := by
  induction r with
  | zero => exact dimensionOneRosserModelTermProperties_zero
  | succ r ih => exact dimensionOneRosserModelTermProperties_succ r ih

theorem dimensionOneRosserModelPlusTerm_nonneg (r : Nat) (s : Real) :
    0 ≤ dimensionOneRosserModelPlusTerm r s :=
  (dimensionOneRosserModelTermProperties_all r).plus_nonneg s

theorem dimensionOneRosserModelMinusTerm_nonneg (r : Nat) (s : Real) :
    0 ≤ dimensionOneRosserModelMinusTerm r s :=
  (dimensionOneRosserModelTermProperties_all r).minus_nonneg s

theorem dimensionOneRosserModelPlusTerm_continuousOn (r : Nat) :
    ContinuousOn (dimensionOneRosserModelPlusTerm r) (Ici 1) :=
  (dimensionOneRosserModelTermProperties_all r).plus_continuousOn

theorem dimensionOneRosserModelMinusTerm_continuousOn (r : Nat) :
    ContinuousOn (dimensionOneRosserModelMinusTerm r) (Ici 2) :=
  (dimensionOneRosserModelTermProperties_all r).minus_continuousOn

theorem dimensionOneRosserModelPlusTerm_eq_zero_of_lt
    (r : Nat) {s : Real} (hs : s < 1) :
    dimensionOneRosserModelPlusTerm r s = 0 :=
  (dimensionOneRosserModelTermProperties_all r).plus_eq_zero_below s hs

theorem dimensionOneRosserModelMinusTerm_eq_zero_of_lt
    (r : Nat) {s : Real} (hs : s < 2) :
    dimensionOneRosserModelMinusTerm r s = 0 :=
  (dimensionOneRosserModelTermProperties_all r).minus_eq_zero_below s hs

theorem dimensionOneRosserModelPlusTerm_eq_zero_of_upper_le
    (r : Nat) {s : Real} (hs : 3 + 2 * (r : Real) ≤ s) :
    dimensionOneRosserModelPlusTerm r s = 0 :=
  (dimensionOneRosserModelTermProperties_all r).plus_eq_zero_above s hs

theorem dimensionOneRosserModelMinusTerm_eq_zero_of_upper_le
    (r : Nat) {s : Real} (hs : 2 + 2 * (r : Real) ≤ s) :
    dimensionOneRosserModelMinusTerm r s = 0 :=
  (dimensionOneRosserModelTermProperties_all r).minus_eq_zero_above s hs

theorem dimensionOneRosserModelMinusTerm_succ_integral
    (r : Nat) {s : Real} (hs : 2 ≤ s) :
    dimensionOneRosserModelMinusTerm (r + 1) s =
      ∫ t in Ioi s,
        dimensionOneRosserModelPlusTerm r (t - 1) / (t - 1) := by
  rw [dimensionOneRosserModelMinusTerm_succ_eq, if_pos hs]

theorem dimensionOneRosserModelPlusTerm_succ_integral
    (r : Nat) {s : Real} (hs : 3 ≤ s) :
    dimensionOneRosserModelPlusTerm (r + 1) s =
      ∫ t in Ioi s,
        dimensionOneRosserModelMinusTerm (r + 1) (t - 1) / (t - 1) := by
  have hs1 : (1 : Real) ≤ s := by linarith
  rw [dimensionOneRosserModelPlusTerm_succ_eq, if_pos hs1,
    max_eq_right hs]

theorem dimensionOneRosserModelPlusTerm_succ_eq_at_three
    (r : Nat) {s : Real} (hs1 : 1 < s) (hs3 : s ≤ 3) :
    dimensionOneRosserModelPlusTerm (r + 1) s =
      dimensionOneRosserModelPlusTerm (r + 1) 3 := by
  have hs1' : (1 : Real) ≤ s := hs1.le
  rw [dimensionOneRosserModelPlusTerm_succ_eq,
    dimensionOneRosserModelPlusTerm_succ_eq, if_pos hs1',
    if_pos (by norm_num : (1 : Real) ≤ 3), max_eq_left hs3,
    max_self]

private theorem antitoneOn_integral_Ioi
    {f : Real -> Real} {a : Real} (hf : Integrable f)
    (hnonneg : ∀ t ∈ Ioi a, 0 ≤ f t) :
    AntitoneOn (fun s => ∫ t in Ioi s, f t) (Ici a) := by
  intro x hx y hy hxy
  apply setIntegral_mono_set hf.integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply hnonneg t
    change a ≤ x at hx
    change x < t at ht
    exact hx.trans_lt ht
  · exact (Ioi_subset_Ioi hxy).eventuallyLE

theorem dimensionOneRosserModelTerm_antitoneOn (r : Nat) :
    AntitoneOn (dimensionOneRosserModelPlusTerm r) (Ici 1) ∧
      AntitoneOn (dimensionOneRosserModelMinusTerm r) (Ici 2) := by
  cases r with
  | zero =>
      constructor
      · intro x hx y hy hxy
        simp only [mem_Ici] at hx hy
        change dimensionOneRosserModelPlusTerm 0 y ≤
          dimensionOneRosserModelPlusTerm 0 x
        rw [dimensionOneRosserModelPlusTerm_zero,
          dimensionOneRosserModelPlusTerm_zero]
        by_cases hy3 : y ≤ 3
        · have hx3 : x ≤ 3 := hxy.trans hy3
          rw [if_pos ⟨hy, hy3⟩, if_pos ⟨hx, hx3⟩]
          linarith
        · rw [if_neg (fun h => hy3 h.2)]
          by_cases hx3 : x ≤ 3
          · rw [if_pos ⟨hx, hx3⟩]
            linarith
          · rw [if_neg (fun h => hx3 h.2)]
      · intro x hx y hy hxy
        simp
  | succ r =>
      have hplusKernelIntegrable : Integrable
          (shiftedRosserKernel (dimensionOneRosserModelPlusTerm r)) :=
        integrable_shiftedRosserKernel (by norm_num)
          (dimensionOneRosserModelPlusTerm_continuousOn r)
          (fun s => dimensionOneRosserModelPlusTerm_eq_zero_of_lt r)
          (fun s => dimensionOneRosserModelPlusTerm_eq_zero_of_upper_le r)
      have hminusKernelIntegrable : Integrable
          (shiftedRosserKernel
            (dimensionOneRosserModelMinusTerm (r + 1))) :=
        integrable_shiftedRosserKernel (by norm_num)
          (dimensionOneRosserModelMinusTerm_continuousOn (r + 1))
          (fun s => dimensionOneRosserModelMinusTerm_eq_zero_of_lt (r + 1))
          (fun s => dimensionOneRosserModelMinusTerm_eq_zero_of_upper_le (r + 1))
      have hminusPrimitive : AntitoneOn
          (fun s => ∫ t in Ioi s,
            shiftedRosserKernel (dimensionOneRosserModelPlusTerm r) t)
          (Ici 2) :=
        antitoneOn_integral_Ioi hplusKernelIntegrable (by
          intro t ht
          exact div_nonneg
            (dimensionOneRosserModelPlusTerm_nonneg r (t - 1))
            (by simp only [mem_Ioi] at ht; linarith))
      have hplusPrimitive : AntitoneOn
          (fun s => ∫ t in Ioi s,
            shiftedRosserKernel
              (dimensionOneRosserModelMinusTerm (r + 1)) t)
          (Ici 3) :=
        antitoneOn_integral_Ioi hminusKernelIntegrable (by
          intro t ht
          exact div_nonneg
            (dimensionOneRosserModelMinusTerm_nonneg (r + 1) (t - 1))
            (by simp only [mem_Ioi] at ht; linarith))
      constructor
      · intro x hx y hy hxy
        simp only [mem_Ici] at hx hy
        rw [dimensionOneRosserModelPlusTerm_succ_eq,
          dimensionOneRosserModelPlusTerm_succ_eq,
          if_pos hx, if_pos hy]
        apply hplusPrimitive
        · exact le_max_left 3 x
        · exact le_max_left 3 y
        · exact max_le_max_left 3 hxy
      · intro x hx y hy hxy
        simp only [mem_Ici] at hx hy
        rw [dimensionOneRosserModelMinusTerm_succ_eq,
          dimensionOneRosserModelMinusTerm_succ_eq,
          if_pos hx, if_pos hy]
        exact hminusPrimitive hx hy hxy

end PrimesRestrictedDigits
