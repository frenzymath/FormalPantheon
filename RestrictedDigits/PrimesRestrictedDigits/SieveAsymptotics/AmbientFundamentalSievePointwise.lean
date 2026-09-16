import PrimesRestrictedDigits.SieveAsymptotics.FundamentalSieveParameters
import PrimesRestrictedDigits.SieveAsymptotics.AmbientRosserWeakCutoffAdapter
import PrimesRestrictedDigits.SieveAsymptotics.AmbientRosserErrorBudget
import PrimesRestrictedDigits.SieveDecomposition.LowerBoundingSieve
import PrimesRestrictedDigits.SieveDecomposition.RosserWeights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pointwise corrected ambient fundamental-sieve estimate

This applies the paired reciprocal main sums to the concrete coprime ambient `BoundingSieve`
and inserts the absolute ambient progression-error budget.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_ambientFundamentalSieve_pointwise :
    ∃ C : Real, 1 <= C ∧
      ∀ (length : Nat) (outer_d : PNat) {X epsilon delta : Real},
        1 < X -> 0 < epsilon -> epsilon <= 1 / 64 ->
        2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1 ->
        0 < delta -> delta <= epsilon ^ (4 : Nat) ->
        5 <= X ^ delta ->
        let z := X ^ delta
        let s := epsilon / (2 * delta)
        |((strictSiftedCarrier
              (sieveDilation
                (maynardCoprimeAmbientCarrier
                  ((10 ^ length : Nat) : Real)) outer_d) z).card : Real) -
            ((maynardCoprimeAmbientCarrier
              ((10 ^ length : Nat) : Real)).card : Real) /
                (outer_d : Real) * decimalExcludedPrimeProduct z| <=
          (ambientBoundingSieve length outer_d z).totalMass *
              (decimalExcludedPrimeProduct z / s *
                (C * Real.exp (-s))) +
            ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
              |ambientSieveProgressionError length
                ((outer_d : Nat) * e)| := by
  obtain ⟨C, hC, hMain⟩ :=
    exists_dimensionOneRosserAmbientWeakCutoffMainSums
  refine ⟨C, hC, ?_⟩
  intro length outer_d X epsilon delta hX hepsilon hepsilonSmall
    hepsilonRosser hdelta hdeltaEpsilon hcutoff
  have hdata := fundamentalSieve_smallParameter_data hX hepsilon
    hepsilonSmall hepsilonRosser hdelta hdeltaEpsilon hcutoff
  dsimp at hdata
  rcases hdata with ⟨hlevel, hz, hcoordinate, hlarge, hfactor,
    _, _, _⟩
  let sieve := ambientBoundingSieve length outer_d (X ^ delta)
  let V : Real := decimalExcludedPrimeProduct (X ^ delta)
  let s : Real := epsilon / (2 * delta)
  have hmainPair :
      V - V / s * (C * Real.exp (-s)) <=
          sieve.mainSum (lowerRosserWeight (X ^ (epsilon / 2))) ∧
        sieve.mainSum (upperRosserWeight (X ^ (epsilon / 2))) <=
          V + V / s * (C * Real.exp (-s)) := by
    have h := hMain length outer_d
      (level := X ^ (epsilon / 2)) (z := X ^ delta) (s := s)
      hlevel hz (by simpa [s] using hcoordinate) hlarge
    simpa [sieve, V] using And.imp le_of_lt le_of_lt h
  have hmass : 0 <= sieve.totalMass := by
    rw [show sieve.totalMass =
        ((maynardCoprimeAmbientCarrier
          ((10 ^ length : Nat) : Real)).card : Real) /
          (outer_d : Real) by rfl]
    positivity
  have hpoint :=
    BoundingSieve.abs_siftedSum_sub_main_le_of_moebius_pair
      sieve (lowerRosserWeight (X ^ (epsilon / 2)))
      (upperRosserWeight (X ^ (epsilon / 2)))
      (lowerRosserWeight_isLowerMoebius _)
      (upperRosserWeight_isUpperMoebius _)
      hmass hmainPair.1 hmainPair.2
  have hupper := ambientBoundingSieve_errSum_upper_le_fundamental
    length outer_d (X := X) (epsilon := epsilon) (delta := delta)
      (by linarith : 1 < X ^ (epsilon / 2))
  have hlower := ambientBoundingSieve_errSum_lower_le_fundamental
    length outer_d (X := X) (epsilon := epsilon) (delta := delta)
      (by linarith : 1 < X ^ (epsilon / 2)) hfactor
  have hmax :
      max (sieve.errSum (lowerRosserWeight (X ^ (epsilon / 2))))
          (sieve.errSum (upperRosserWeight (X ^ (epsilon / 2)))) <=
        ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
          |ambientSieveProgressionError length
            ((outer_d : Nat) * e)| := by
    apply max_le
    · simpa [sieve] using hlower
    · simpa [sieve] using hupper
  have hsift := ambientBoundingSieve_siftedSum_eq_card
    length outer_d (z := X ^ delta) hcutoff
  have hrewritten :=
    hpoint.trans (add_le_add (le_refl
      (sieve.totalMass * (V / s * (C * Real.exp (-s))))) hmax)
  simpa [sieve, V, s, hsift, ambientBoundingSieve_totalMass] using hrewritten

end

end PrimesRestrictedDigits
