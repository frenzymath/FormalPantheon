import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedMoment

/-!
# Independent high-rank Rosser seed

This file combines the finite multiplicative moment with its explicit scalar and density
reserves. It replaces, but does not claim, Iwaniec's Eq. (8.13).
-/

namespace PrimesRestrictedDigits

private theorem rosserFailureSum_lt_seedEnvelope
    (P : Finset Nat) {failureSum level z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 1 <= s)
    (hband : Real.log level <= s ^ 51)
    (hmoment : failureSum <=
      Real.exp ((3 - s) * Real.log (dimensionOneRosserSeedTilt s) +
        dimensionOneRosserSeedTilt s *
          ∑ p ∈ P.filter (fun p : Nat => (p : Real) < z),
            (p : Real)⁻¹)) :
    failureSum <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s ^ 2 *
        dimensionOneRosserSeedEnvelope s := by
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hlogz : Real.log z <= s ^ 50 :=
    dimensionOneRosserSeed_log_cutoff_le_pow hz hsPos hs hband
  have hsum := sieveFactorsBelow_reciprocalSum_le_seedBound P hprime hz
    hsLarge hlogz
  have hmomentReserve := dimensionOneRosserSeedMomentExp_lt hsLarge hsum
  have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hInv := sieveDensityBelow_reciprocal_inv_le_exp_sum P z hprime
  have hdensity := dimensionOneRosserSeedExpNegTwo_lt_density_div_sq
    hsLarge hV hInv hsum
  calc
    failureSum <=
        Real.exp ((3 - s) * Real.log (dimensionOneRosserSeedTilt s) +
          dimensionOneRosserSeedTilt s *
            ∑ p ∈ P.filter (fun p : Nat => (p : Real) < z),
              (p : Real)⁻¹) := hmoment
    _ < Real.exp (-2 * s) * dimensionOneRosserSeedEnvelope s :=
      hmomentReserve
    _ < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s ^ 2 *
        dimensionOneRosserSeedEnvelope s :=
      mul_lt_mul_of_pos_right hdensity
        (dimensionOneRosserSeedEnvelope_pos s)

/-- The finite upper all-rank correction satisfies the independent
dimension-one seed bound. -/
theorem dimensionOneRosserUpperFailureSum_lt_seedEnvelope
    (P : Finset Nat) {level z0 s0 : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz0 : 2 <= z0)
    (hs0 : s0 = Real.log level / Real.log z0)
    (hs0Large : Real.exp 5000 + 1 <= s0)
    (hband : Real.log level <= s0 ^ 51) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z0 <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z0 / s0 ^ 2 *
        dimensionOneRosserSeedEnvelope s0 := by
  apply rosserFailureSum_lt_seedEnvelope P hprime hz0 hs0 hs0Large hband
  exact upperRosserFailureSum_le_seedMoment P hprime hlevel hz0 hs0 hs0Large

/-- The finite lower all-rank correction satisfies the independent
dimension-one seed bound. -/
theorem dimensionOneRosserLowerFailureSum_lt_seedEnvelope
    (P : Finset Nat) {level z0 s0 : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz0 : 2 <= z0)
    (hs0 : s0 = Real.log level / Real.log z0)
    (hs0Large : Real.exp 5000 + 1 <= s0)
    (hband : Real.log level <= s0 ^ 51) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z0 <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z0 / s0 ^ 2 *
        dimensionOneRosserSeedEnvelope s0 := by
  apply rosserFailureSum_lt_seedEnvelope P hprime hz0 hs0 hs0Large hband
  exact lowerRosserFailureSum_le_seedMoment P hprime hlevel hz0 hs0 hs0Large

/-- Every upper source truncation satisfies the same rank-uniform seed. -/
theorem dimensionOneRosserUpperFailurePartialSum_lt_seedEnvelope
    (P : Finset Nat) (R : Nat) {level z0 s0 : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz0 : 2 <= z0)
    (hs0 : s0 = Real.log level / Real.log z0)
    (hs0Large : Real.exp 5000 + 1 <= s0)
    (hband : Real.log level <= s0 ^ 51) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z0 R <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z0 / s0 ^ 2 *
        dimensionOneRosserSeedEnvelope s0 := by
  exact (upperRosserFailurePartialSum_le_failureSum P level z0 R hprime).trans_lt
    (dimensionOneRosserUpperFailureSum_lt_seedEnvelope P hprime hlevel hz0
      hs0 hs0Large hband)

/-- Every lower source truncation satisfies the same rank-uniform seed. -/
theorem dimensionOneRosserLowerFailurePartialSum_lt_seedEnvelope
    (P : Finset Nat) (R : Nat) {level z0 s0 : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz0 : 2 <= z0)
    (hs0 : s0 = Real.log level / Real.log z0)
    (hs0Large : Real.exp 5000 + 1 <= s0)
    (hband : Real.log level <= s0 ^ 51) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z0 R <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z0 / s0 ^ 2 *
        dimensionOneRosserSeedEnvelope s0 := by
  exact (lowerRosserFailurePartialSum_le_failureSum P level z0 R hprime).trans_lt
    (dimensionOneRosserLowerFailureSum_lt_seedEnvelope P hprime hlevel hz0
      hs0 hs0Large hband)

end PrimesRestrictedDigits
