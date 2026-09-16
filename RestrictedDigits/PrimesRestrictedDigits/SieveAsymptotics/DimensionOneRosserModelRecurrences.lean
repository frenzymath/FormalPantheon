import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelPartialSums

/-!
# Finite recurrences for the dimension-one Rosser model

These are Iwaniec's specialized finite Section 7 recurrences (7.1)--(7.3); see
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 193--194.
-/

open Set MeasureTheory

namespace PrimesRestrictedDigits

theorem dimensionOneRosserModelMinusPartialSum_succ_integral
    (R : Nat) {s : Real} (hs : 2 ≤ s) :
    dimensionOneRosserModelMinusPartialSum (R + 1) s =
      ∫ t in Ioi s,
        dimensionOneRosserModelPlusPartialSum R (t - 1) / (t - 1) := by
  induction R with
  | zero =>
      rw [dimensionOneRosserModelMinusPartialSum_succ,
        dimensionOneRosserModelMinusPartialSum_zero, zero_add,
        dimensionOneRosserModelMinusTerm_succ_integral 0 hs]
      simp_rw [dimensionOneRosserModelPlusPartialSum_zero]
  | succ R ih =>
      rw [dimensionOneRosserModelMinusPartialSum_succ,
        dimensionOneRosserModelMinusTerm_succ_integral (R + 1) hs,
        ih]
      simp_rw [dimensionOneRosserModelPlusPartialSum_succ]
      have hpartial : IntegrableOn
          (fun t => dimensionOneRosserModelPlusPartialSum R (t - 1) /
            (t - 1)) (Ioi s) := by
        exact (integrable_shiftedRosserKernel_plusPartialSum R).integrableOn.congr_fun
          (fun t ht => rfl) measurableSet_Ioi
      have hterm : IntegrableOn
          (fun t => dimensionOneRosserModelPlusTerm (R + 1) (t - 1) /
            (t - 1)) (Ioi s) := by
        exact (integrable_shiftedRosserKernel_plusTerm (R + 1)).integrableOn.congr_fun
          (fun t ht => rfl) measurableSet_Ioi
      rw [← integral_add hpartial hterm]
      apply integral_congr_ae
      filter_upwards with t
      ring

theorem dimensionOneRosserModelPlusPartialSum_integral
    (R : Nat) {s : Real} (hs : 3 ≤ s) :
    dimensionOneRosserModelPlusPartialSum R s =
      ∫ t in Ioi s,
        dimensionOneRosserModelMinusPartialSum R (t - 1) / (t - 1) := by
  induction R with
  | zero =>
      rw [dimensionOneRosserModelPlusPartialSum_zero,
        dimensionOneRosserModelPlusTerm_eq_zero_of_upper_le 0 (by
          norm_num at hs ⊢
          exact hs)]
      simp_rw [dimensionOneRosserModelMinusPartialSum_zero]
      simp
  | succ R ih =>
      rw [dimensionOneRosserModelPlusPartialSum_succ, ih,
        dimensionOneRosserModelPlusTerm_succ_integral R hs]
      simp_rw [dimensionOneRosserModelMinusPartialSum_succ]
      have hpartial : IntegrableOn
          (fun t => dimensionOneRosserModelMinusPartialSum R (t - 1) /
            (t - 1)) (Ioi s) := by
        exact (integrable_shiftedRosserKernel_minusPartialSum R).integrableOn.congr_fun
          (fun t ht => rfl) measurableSet_Ioi
      have hterm : IntegrableOn
          (fun t => dimensionOneRosserModelMinusTerm (R + 1) (t - 1) /
            (t - 1)) (Ioi s) := by
        exact (integrable_shiftedRosserKernel_minusTerm (R + 1)).integrableOn.congr_fun
          (fun t ht => rfl) measurableSet_Ioi
      rw [← integral_add hpartial hterm]
      apply integral_congr_ae
      filter_upwards with t
      ring

theorem dimensionOneRosserModelPlusPartialSum_boundary
    (R : Nat) {s : Real} (hs1 : 1 < s) (hs3 : s ≤ 3) :
    dimensionOneRosserModelPlusPartialSum R s + s =
      3 + dimensionOneRosserModelPlusPartialSum R 3 := by
  induction R with
  | zero =>
      rw [dimensionOneRosserModelPlusPartialSum_zero,
        dimensionOneRosserModelPlusPartialSum_zero,
        dimensionOneRosserModelPlusTerm_zero,
        dimensionOneRosserModelPlusTerm_zero]
      rw [if_pos ⟨hs1.le, hs3⟩]
      norm_num
  | succ R ih =>
      calc
        dimensionOneRosserModelPlusPartialSum (R + 1) s + s =
            (dimensionOneRosserModelPlusPartialSum R s + s) +
              dimensionOneRosserModelPlusTerm (R + 1) s := by
          rw [dimensionOneRosserModelPlusPartialSum_succ]
          ring
        _ = (3 + dimensionOneRosserModelPlusPartialSum R 3) +
              dimensionOneRosserModelPlusTerm (R + 1) s := by rw [ih]
        _ = 3 + (dimensionOneRosserModelPlusPartialSum R 3 +
              dimensionOneRosserModelPlusTerm (R + 1) 3) := by
          rw [dimensionOneRosserModelPlusTerm_succ_eq_at_three R hs1 hs3]
          ring
        _ = 3 + dimensionOneRosserModelPlusPartialSum (R + 1) 3 := by
          rw [dimensionOneRosserModelPlusPartialSum_succ]

end PrimesRestrictedDigits
