import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedPropagation

/-!
# Scaling the independent high-rank Rosser seed

This file scales the transformed seed while leaving the recurrence boundary unscaled. The
required correction is paid by nonnegativity of the reciprocal prime boundary and the
hypothesis `1 <= D`.
-/

namespace PrimesRestrictedDigits

/-- Every upper reciprocal-prime boundary partial sum is nonnegative. -/
theorem upperRosserFailurePartialSum_reciprocal_nonneg
    (P : Finset Nat) (level z : Real) (R : Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    0 <= upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
      level z R := by
  unfold upperRosserFailurePartialSum
  exact Finset.sum_nonneg fun r _ =>
    upperRosserFailureSumAtRank_reciprocal_nonneg P level z r hprime

/-- Every lower reciprocal-prime boundary partial sum is nonnegative. -/
theorem lowerRosserFailurePartialSum_reciprocal_nonneg
    (P : Finset Nat) (level z : Real) (R : Nat)
    (hprime : forall p, p ∈ P -> p.Prime) :
    0 <= lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
      level z R := by
  unfold lowerRosserFailurePartialSum
  exact Finset.sum_nonneg fun r _ =>
    lowerRosserFailureSumAtRank_reciprocal_nonneg P level z r hprime

private theorem failure_add_scaled_seed_lt
    {failure seed scale envelope D : Real}
    (hfailure : 0 <= failure) (hD : 1 <= D)
    (hbound : failure + seed < scale * (envelope / 2)) :
    failure + D * seed < scale * (D * envelope / 2) := by
  have hscale : failure + D * seed <= D * (failure + seed) := by
    calc
      failure + D * seed <= D * failure + D * seed := by
        simpa only [add_comm] using
          add_le_add_right (le_mul_of_one_le_left hfailure hD) (D * seed)
      _ = D * (failure + seed) := by ring
  exact hscale.trans_lt <| by
    calc
      D * (failure + seed) < D * (scale * (envelope / 2)) :=
        mul_lt_mul_of_pos_left hbound (zero_lt_one.trans_le hD)
      _ = scale * (D * envelope / 2) := by ring

/-- The upper boundary and a `D`-scaled transformed seed retain the same
half-envelope estimate, with `D` inserted into the target profile. -/
theorem dimensionOneRosserUpperSeed_add_scaledPrimeSum_lt_half
    (P : Finset Nat) (R : Nat) {D K level z s s0 : Real}
    (hD : 1 <= D) (hK : 0 <= K)
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hdom : 13824 * K <= s0 ^ 46)
    (hRatio : forall x : Real,
      level ^ (1 / s0) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        D * dimensionOneRosserSeedPrimeSum P level s0 z <
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (D * dimensionOneRosserSeedEnvelope s / 2) := by
  apply failure_add_scaled_seed_lt
  · exact upperRosserFailurePartialSum_reciprocal_nonneg P level
      (level ^ (1 / s0)) R hprime
  · exact hD
  · exact dimensionOneRosserUpperSeed_add_primeSum_lt_half P R hK hprime
      hlevel hz hs hsLarge hss0 hcutoff hcap hband hdom hRatio

/-- The lower boundary and a `D`-scaled transformed seed retain the same
half-envelope estimate, with `D` inserted into the target profile. -/
theorem dimensionOneRosserLowerSeed_add_scaledPrimeSum_lt_half
    (P : Finset Nat) (R : Nat) {D K level z s s0 : Real}
    (hD : 1 <= D) (hK : 0 <= K)
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s) (hss0 : s < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hdom : 13824 * K <= s0 ^ 46)
    (hRatio : forall x : Real,
      level ^ (1 / s0) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        D * dimensionOneRosserSeedPrimeSum P level s0 z <
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (D * dimensionOneRosserSeedEnvelope s / 2) := by
  apply failure_add_scaled_seed_lt
  · exact lowerRosserFailurePartialSum_reciprocal_nonneg P level
      (level ^ (1 / s0)) R hprime
  · exact hD
  · exact dimensionOneRosserLowerSeed_add_primeSum_lt_half P R hK hprime
      hlevel hz hs hsLarge hss0 hcutoff hcap hband hdom hRatio

end PrimesRestrictedDigits
