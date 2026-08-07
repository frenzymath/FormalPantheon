import BoundedGaps.Maynard.Growth
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Elementary logarithmic envelope limits

This module records the fixed-power logarithmic absorption used by the
concrete Maynard error envelopes. The source is Maynard2013v3, Proposition
`MainProp`, source lines 201--216; the little-o input is the pinned Mathlib
theorem `isLittleO_log_rpow_rpow_atTop`.
-/

namespace BoundedGaps.Maynard

open Filter

theorem tendsto_natCast_rpow_mul_log_rpow_div
    {a b : ℝ} (ha : a < 1) :
    Tendsto
      (fun N : ℕ =>
        Real.rpow (N : ℝ) a * Real.rpow (Real.log (N : ℝ)) b / (N : ℝ))
      atTop (nhds 0) := by
  have hlittle := isLittleO_log_rpow_rpow_atTop b (sub_pos.mpr ha)
  have hnat := hlittle.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := hnat.tendsto_div_nhds_zero
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  symm
  change (N : ℝ) ^ a * Real.log (N : ℝ) ^ b / (N : ℝ) =
    Real.log (N : ℝ) ^ b / (N : ℝ) ^ (1 - a)
  rw [div_eq_div_iff]
  · have hp : (N : ℝ) ^ a * (N : ℝ) ^ (1 - a) = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      rw [show a + (1 - a) = 1 by ring, Real.rpow_one]
    calc
      (N : ℝ) ^ a * Real.log (N : ℝ) ^ b * (N : ℝ) ^ (1 - a) =
          Real.log (N : ℝ) ^ b *
            ((N : ℝ) ^ a * (N : ℝ) ^ (1 - a)) := by ring
      _ = Real.log (N : ℝ) ^ b * (N : ℝ) := by rw [hp]
  · exact hNpos.ne'
  · exact (Real.rpow_pos_of_pos hNpos _).ne'

end BoundedGaps.Maynard
