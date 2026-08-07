module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import PeriodThree.Interval.Cycle

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by the period exclusion proof)

/-!
# Exact periods from the Li-Yorke order configuration

This file proves part T1 for the increasing orbit-order branch. `AllPeriods.lean`
transports the result to the reversed branch by reflection.
-/

@[expose] public section

open Set

namespace PeriodThree

/-- Under the increasing Li-Yorke orbit order, every positive natural number is
the least period of a point in the interval. This is [LY75, Theorem I, part T1,
pp. 987-988]. -/
theorem existsPointOfLeastPeriodOfIncreasingOrder
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (hJ : J.OrdConnected) (hF : ContinuousOn F J) (hFJ : MapsTo F J J) (haJ : a ∈ J)
    (horder : (F^[3]) a ≤ a ∧ a < F a ∧ F a < (F^[2]) a) :
    ∀ k : ℕ, 0 < k → ∃ x ∈ J, Function.minimalPeriod F x = k := by
  let b := F a
  let c := F b
  let d := F c
  have hb_def : F a = b := rfl
  have hc_def : F b = c := rfl
  have hd_def : F c = d := rfl
  have hiter2 : (F^[2]) a = c := by simp [b, c, Function.iterate_succ_apply']
  have hiter3 : (F^[3]) a = d := by simp [b, c, d, Function.iterate_succ_apply']
  have hda : d ≤ a := hiter3 ▸ horder.1
  have hab : a < b := hb_def ▸ horder.2.1
  have hbc : b < c := hb_def ▸ hiter2 ▸ horder.2.2
  have hbJ : b ∈ J := hb_def ▸ hFJ haJ
  have hcJ : c ∈ J := hc_def ▸ hFJ hbJ
  have hKJ : Icc a b ⊆ J := hJ.out haJ hbJ
  have hLJ : Icc b c ⊆ J := hJ.out hbJ hcJ
  have hLK : Icc b c ⊆ F '' Icc a b := by
    simpa [hb_def, hc_def] using
      intermediate_value_Icc hab.le (hF.mono hKJ)
  have hac_image : Icc a c ⊆ F '' Icc b c := by
    have hdc : Icc d c ⊆ F '' Icc b c := by
      simpa [hc_def, hd_def] using
        intermediate_value_Icc' hbc.le (hF.mono hLJ)
    exact (Icc_subset_Icc hda le_rfl).trans hdc
  have hKL : Icc a b ⊆ F '' Icc b c :=
    (Icc_subset_Icc le_rfl hbc.le).trans hac_image
  have hLL : Icc b c ⊆ F '' Icc b c :=
    (Icc_subset_Icc hab.le le_rfl).trans hac_image
  intro k hk
  rcases k with _ | k
  · omega
  rcases k with _ | n
  · obtain ⟨x, hxL, hxfix⟩ :=
      exists_mem_Icc_isFixedPt_of_surjOn (hF.mono hLJ) hbc.le hLL
    exact ⟨x, hLJ hxL, Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hxfix⟩
  · obtain ⟨p, hpL, hpPeriod, hpK, hpLBefore⟩ :=
      existsPeriodicPointOfRepeatedIntervalCover hF hFJ hLJ hLL hab.le hKL hLK n
    refine ⟨p, hLJ hpL, ?_⟩
    let j := Function.minimalPeriod F p
    have hjpos : 0 < j := hpPeriod.minimalPeriod_pos (by omega)
    have hjle : j ≤ n + 2 := hpPeriod.minimalPeriod_le (by omega)
    have hjperiod : Function.IsPeriodicPt F j p := Function.isPeriodicPt_minimalPeriod F p
    have hj_not_lt : ¬j < n + 2 := by
      intro hjlt
      have hjle_pred : j ≤ n + 1 := by omega
      have hsub_add : n + 1 - j + j = n + 1 := Nat.sub_add_cancel hjle_pred
      have horbit_eq : (F^[n + 1]) p = (F^[n + 1 - j]) p := by
        calc
          (F^[n + 1]) p = (F^[n + 1 - j + j]) p := by rw [hsub_add]
          _ = (F^[n + 1 - j]) ((F^[j]) p) :=
            Function.iterate_add_apply F (n + 1 - j) j p
          _ = (F^[n + 1 - j]) p := by rw [hjperiod.eq]
      have hright_index : n + 1 - j < n + 1 := by omega
      have hpRightL : (F^[n + 1 - j]) p ∈ Icc b c :=
        hpLBefore (n + 1 - j) hright_index
      have hpFinalB : (F^[n + 1]) p = b := by
        apply le_antisymm hpK.2
        rw [horbit_eq]
        exact hpRightL.1
      have hp_eq_c : p = c := by
        calc
          p = (F^[n + 2]) p := hpPeriod.eq.symm
          _ = F ((F^[n + 1]) p) := by
            rw [show n + 2 = (n + 1).succ by omega, Function.iterate_succ_apply']
          _ = F b := by rw [hpFinalB]
          _ = c := hc_def
      rcases n with _ | n
      · have hjone : j = 1 := by omega
        have hpFixed : F p = p := by
          simpa [hjone] using hjperiod.eq
        have hFpB : F p = b := by simpa using hpFinalB
        linarith
      · have hpOneL : (F^[1]) p ∈ Icc b c := hpLBefore 1 (by omega)
        have hFpD : F p = d := by rw [hp_eq_c, hd_def]
        have : b ≤ d := by
          rw [← hFpD]
          simpa using hpOneL.1
        linarith
    exact le_antisymm hjle (le_of_not_gt hj_not_lt)

end PeriodThree
