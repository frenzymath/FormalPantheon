import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelComparison

/-!
# Inclusive upper endpoint for the finite Rosser model comparison

The strict comparison is closed at the upper-model endpoint `s = 1` by right continuity,
without changing its uniform witness.
-/

open Filter Set

namespace PrimesRestrictedDigits

/-- One comparison constant controls the upper model on its closed natural
domain and the lower model strictly on its original natural domain. -/
theorem exists_dimensionOneRosserModelPartialSums_le_delay :
    exists c : Real, 0 < c /\
      (forall (R : Nat) {s : Real}, 1 <= s ->
        dimensionOneRosserModelPlusPartialSum R s <=
          c * dimensionOneDelayScaledPlus s) /\
      (forall (R : Nat) {s : Real}, 2 <= s ->
        dimensionOneRosserModelMinusPartialSum R s <
          c * dimensionOneDelayScaledMinus s) := by
  rcases exists_dimensionOneRosserModelPartialSums_lt_delay with
    ⟨c, hc, hplus, hminus⟩
  refine ⟨c, hc, ?_, hminus⟩
  intro R s hs
  apply le_of_tendsto_of_tendsto
    (((dimensionOneRosserModelPlusPartialSum_continuousOn R).continuousWithinAt
      (mem_Ici.mpr hs)).mono fun u hu =>
        mem_Ici.mpr (hs.trans (mem_Ioi.mp hu).le))
    ((continuous_const.mul
      dimensionOneDelayScaledPlus_continuous).continuousWithinAt)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (hplus R (lt_of_le_of_lt hs (mem_Ioi.mp hu))).le

end PrimesRestrictedDigits
