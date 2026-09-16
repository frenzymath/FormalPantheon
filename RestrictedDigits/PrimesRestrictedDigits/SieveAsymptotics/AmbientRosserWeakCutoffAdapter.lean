import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserWeakCutoffAdapter
import PrimesRestrictedDigits.SieveAsymptotics.DecimalAmbientBoundingSieve

/-!
# Weak-cutoff Rosser main sums for the ambient sieve

This specializes the reciprocal main-sum estimate to Maynard's coprime ambient
`BoundingSieve`, preserving the weak decimal product endpoint.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_dimensionOneRosserAmbientWeakCutoffMainSums :
    ∃ C : Real, 1 <= C ∧
      ∀ (length : Nat) (d : PNat),
        ∀ {level z s : Real},
          2 <= level -> 2 <= z ->
          s = Real.log level / Real.log z ->
          Real.exp 5000 + 2 <= s ->
          let sieve := ambientBoundingSieve length d z
          let V := decimalExcludedPrimeProduct z
          V - V / s * (C * Real.exp (-s)) <
              sieve.mainSum (lowerRosserWeight level) ∧
            sieve.mainSum (upperRosserWeight level) <
              V + V / s * (C * Real.exp (-s)) := by
  obtain ⟨C0, hC0, hmain⟩ :=
    exists_dimensionOneRosserReciprocalMainSums_lt_exp_neg
  refine ⟨2 * Real.exp 1 * C0, ?_, ?_⟩
  · have hExp : 1 <= Real.exp (1 : Real) := by
      have h := Real.add_one_le_exp (1 : Real)
      linarith
    calc
      (1 : Real) <= 2 * Real.exp 1 := by nlinarith
      _ = 2 * Real.exp 1 * 1 := by ring
      _ <= 2 * Real.exp 1 * C0 := by gcongr
  · intro length d level z s hlevel hz hs hsLarge
    let sieve := ambientBoundingSieve length d z
    let w := dimensionOneRosserWeakCutoff level s
    have hdata := dimensionOneRosserWeakCutoff_data hlevel hz hs hsLarge
    have hfactor :
        ∀ p, p ∈ sieve.prodPrimes.primeFactors -> (p : Real) < w := by
      intro p hp
      exact dimensionOneRosserWeakCutoff_factor_lt hlevel hz hs hsLarge hp
    have hdecimal :
        ∀ p, p ∈ sieve.prodPrimes.primeFactors -> ¬p ∣ 10 := by
      intro p hp
      exact (mem_decimalSievePrimeProductFactors_iff.mp hp).2.1
    have hnu :
        (sieve.nu : Nat -> Real) = fun n : Nat => (n : Real)⁻¹ := by
      rfl
    have hcoord : s - 1 = Real.log level / Real.log w := by
      simpa [w] using hdata.2.2.1.symm
    have hlarge : Real.exp 5000 + 1 <= s - 1 := hdata.2.2.2
    have hW := hmain sieve hnu hdecimal hlevel hdata.1 hfactor hcoord hlarge
    have hprime :
        ∀ p, p ∈ sieve.prodPrimes.primeFactors -> p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primeFactors hp
    have hVeq :
        sieveDensityBelow sieve.prodPrimes.primeFactors
            (fun p => (p : Real)⁻¹) w = decimalExcludedPrimeProduct z := by
      simpa [sieve, w] using
        sieveDensityBelow_decimalSievePrimeProduct_eq_decimalExcludedPrimeProduct
          (z := z) (w := w) hfactor
    have hV : 0 <= decimalExcludedPrimeProduct z := by
      rw [← hVeq]
      exact (sieveDensityBelow_reciprocal_pos
        sieve.prodPrimes.primeFactors w hprime).le
    have hsTwo : 2 <= s := by
      have hexp : 0 < Real.exp (5000 : Real) := Real.exp_pos _
      linarith
    have hTransfer := dimensionOneRosserWeakCutoff_error_transfer
      hV (by linarith : 0 <= C0) hsTwo
    dsimp at hW
    rw [hVeq] at hW
    constructor
    · calc
        decimalExcludedPrimeProduct z -
              decimalExcludedPrimeProduct z / s *
                ((2 * Real.exp 1 * C0) * Real.exp (-s)) <=
            decimalExcludedPrimeProduct z -
              decimalExcludedPrimeProduct z / (s - 1) *
                (C0 * Real.exp (-(s - 1))) := by
          exact sub_le_sub_left hTransfer _
        _ < sieve.mainSum (lowerRosserWeight level) := hW.1
    · calc
        sieve.mainSum (upperRosserWeight level) <
            decimalExcludedPrimeProduct z +
              decimalExcludedPrimeProduct z / (s - 1) *
                (C0 * Real.exp (-(s - 1))) := hW.2
        _ <= decimalExcludedPrimeProduct z +
              decimalExcludedPrimeProduct z / s *
                ((2 * Real.exp 1 * C0) * Real.exp (-s)) := by
          simpa [add_comm] using
            add_le_add_left hTransfer (decimalExcludedPrimeProduct z)

end

end PrimesRestrictedDigits
