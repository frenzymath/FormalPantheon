import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelEndpointComparison
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelLimits
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelPlusEndpoint

/-!
# Closed-domain raw model comparison

The finite model comparison has a common constant on the natural domains. Passing the finite
sums to their raw `tsum` limits preserves that constant. The upper comparison
also holds at the endpoint `s = 1`.
-/

namespace PrimesRestrictedDigits

theorem dimensionOneRosserModelPlusRaw_le_delay_of_partial
    {c : Real}
    (hplus : forall (R : Nat) {s : Real}, 1 <= s ->
      dimensionOneRosserModelPlusPartialSum R s <=
        c * dimensionOneDelayScaledPlus s)
    {s : Real} (hs : 1 <= s) :
    dimensionOneRosserModelPlusRaw s <=
      c * dimensionOneDelayScaledPlus s := by
  exact le_of_tendsto'
    (dimensionOneRosserModelPlusPartialSum_tendsto_raw_of_one_le hs)
    (fun R => hplus R (s := s) hs)

theorem dimensionOneRosserModelMinusRaw_le_delay_of_partial
    {c : Real}
    (hminus : forall (R : Nat) {s : Real}, 2 <= s ->
      dimensionOneRosserModelMinusPartialSum R s <
        c * dimensionOneDelayScaledMinus s)
    {s : Real} (hs : 2 <= s) :
    dimensionOneRosserModelMinusRaw s <=
      c * dimensionOneDelayScaledMinus s := by
  exact le_of_tendsto'
    (dimensionOneRosserModelMinusPartialSum_tendsto_raw hs)
    (fun R => (hminus R (s := s) hs).le)

theorem exists_dimensionOneRosserModelRaw_le_delay_closed :
    exists c : Real, 0 < c /\
      (forall {s : Real}, 1 <= s ->
        dimensionOneRosserModelPlusRaw s <=
          c * dimensionOneDelayScaledPlus s) /\
      (forall {s : Real}, 2 <= s ->
        dimensionOneRosserModelMinusRaw s <=
          c * dimensionOneDelayScaledMinus s) := by
  rcases exists_dimensionOneRosserModelPartialSums_le_delay with
    ⟨c, hc, hplus, hminus⟩
  refine ⟨c, hc, ?_, ?_⟩
  · intro s hs
    exact dimensionOneRosserModelPlusRaw_le_delay_of_partial hplus hs
  · intro s hs
    exact dimensionOneRosserModelMinusRaw_le_delay_of_partial hminus hs

end PrimesRestrictedDigits
