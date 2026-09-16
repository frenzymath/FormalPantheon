import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserCompleteRapidDecay
import PrimesRestrictedDigits.SieveAsymptotics.RosserMainSum

/-!
# Reciprocal Rosser main-sum bounds

This is the exact finite main-sum composition. It deliberately keeps the strict factor cutoff
and stages the global reciprocal arithmetic function equality needed by the current opaque
failure-sum interfaces.
-/

namespace PrimesRestrictedDigits

/-- rapid correction estimate transferred to both selected main sums. -/
theorem exists_dimensionOneRosserReciprocalMainSums_lt_exp_neg :
    ∃ C : Real, 1 <= C ∧
      ∀ (sieve : BoundingSieve),
        (sieve.nu : Nat → Real) = (fun n : Nat => (n : Real)⁻¹) ->
        (∀ p, p ∈ sieve.prodPrimes.primeFactors -> ¬p ∣ 10) ->
        ∀ {level z s : Real},
          2 <= level -> 2 <= z ->
          (∀ p, p ∈ sieve.prodPrimes.primeFactors -> (p : Real) < z) ->
          s = Real.log level / Real.log z ->
          Real.exp 5000 + 1 <= s ->
          let V := sieveDensityBelow sieve.prodPrimes.primeFactors
            (fun p => (p : Real)⁻¹) z
          let eta := V / s * (C * Real.exp (-s))
          V - eta < sieve.mainSum (lowerRosserWeight level) ∧
            sieve.mainSum (upperRosserWeight level) < V + eta := by
  obtain ⟨C, hC, hRapid⟩ :=
    exists_dimensionOneRosserCompleteFailureSums_lt_exp_neg
  refine ⟨C, hC, ?_⟩
  intro sieve hnu hdecimal level z s hlevel hz hcutoff hs hsLarge
  let V : Real := sieveDensityBelow sieve.prodPrimes.primeFactors
    (fun p => (p : Real)⁻¹) z
  let eta : Real := V / s * (C * Real.exp (-s))
  have hprime : ∀ p, p ∈ sieve.prodPrimes.primeFactors -> p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hFailure := hRapid sieve.prodPrimes.primeFactors hprime hdecimal
    hlevel hz hs hsLarge
  have hUpperFailure :
      upperRosserFailureSum sieve.prodPrimes.primeFactors
          (fun p => (p : Real)⁻¹) level z < eta := by
    simpa [eta, V] using hFailure.1
  have hLowerFailure :
      lowerRosserFailureSum sieve.prodPrimes.primeFactors
          (fun p => (p : Real)⁻¹) level z < eta := by
    simpa [eta, V] using hFailure.2
  have hUpperIdentity :=
    boundingSieveMainSum_upperRosserWeight_eq_add_failureSum
      sieve level z hcutoff
  have hLowerIdentity :=
    boundingSieveMainSum_lowerRosserWeight_eq_sub_failureSum
      sieve level z hcutoff
  have hnuFun : (sieve.nu : Nat → Real) =
      (fun n : Nat => (n : Real)⁻¹) := hnu
  rw [hnuFun] at hUpperIdentity hLowerIdentity
  have hUpperIdentity' :
      sieve.mainSum (upperRosserWeight level) =
        V + upperRosserFailureSum sieve.prodPrimes.primeFactors
          (fun p => (p : Real)⁻¹) level z := by
    simpa [V] using hUpperIdentity
  have hLowerIdentity' :
      sieve.mainSum (lowerRosserWeight level) =
        V - lowerRosserFailureSum sieve.prodPrimes.primeFactors
          (fun p => (p : Real)⁻¹) level z := by
    simpa [V] using hLowerIdentity
  change V - eta < sieve.mainSum (lowerRosserWeight level) ∧
    sieve.mainSum (upperRosserWeight level) < V + eta
  constructor
  · calc
      V - eta < V -
          lowerRosserFailureSum sieve.prodPrimes.primeFactors
            (fun p => (p : Real)⁻¹) level z :=
        sub_lt_sub_left hLowerFailure V
      _ = sieve.mainSum (lowerRosserWeight level) :=
        hLowerIdentity'.symm
  · calc
      sieve.mainSum (upperRosserWeight level) =
          sieveDensityBelow sieve.prodPrimes.primeFactors
              (fun p => (p : Real)⁻¹) z +
            upperRosserFailureSum sieve.prodPrimes.primeFactors
              (fun p => (p : Real)⁻¹) level z := hUpperIdentity'
      _ < sieveDensityBelow sieve.prodPrimes.primeFactors
              (fun p => (p : Real)⁻¹) z +
            sieveDensityBelow sieve.prodPrimes.primeFactors
              (fun p => (p : Real)⁻¹) z / s *
                (C * Real.exp (-s)) :=
        by
          simpa [add_comm] using
            (add_lt_add_right hUpperFailure
              (sieveDensityBelow sieve.prodPrimes.primeFactors
                (fun p => (p : Real)⁻¹) z))

end PrimesRestrictedDigits
