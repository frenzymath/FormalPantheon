import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserReciprocalMainSums
import PrimesRestrictedDigits.SieveAsymptotics.DecimalSourceBoundingSieve
import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatio
import PrimesRestrictedDigits.BasicEstimates.PrimeProductBounds

/-!
# Weak source cutoff to strict Rosser cutoff

The source product uses `p <= z`, while the finite Rosser identities require `p < z`. We move
the analytic coordinate to `exp(log level / (s - 1))`, preserving the source product and
costing only a uniform factor in the exponential correction.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The strict analytic coordinate used for a weak source cutoff. -/
def dimensionOneRosserWeakCutoff (level s : Real) : Real :=
  Real.exp (Real.log level / (s - 1))

theorem dimensionOneRosserWeakCutoff_data
    {level z s : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 2 <= s) :
    2 <= dimensionOneRosserWeakCutoff level s ∧
      z < dimensionOneRosserWeakCutoff level s ∧
      Real.log level /
          Real.log (dimensionOneRosserWeakCutoff level s) = s - 1 ∧
      Real.exp 5000 + 1 <= s - 1 := by
  have hlevelOne : 1 < level := lt_of_lt_of_le (by norm_num) hlevel
  have hzOne : 1 < z := lt_of_lt_of_le (by norm_num) hz
  have hlogLevel : 0 < Real.log level := Real.log_pos hlevelOne
  have hlogZ : 0 < Real.log z := Real.log_pos hzOne
  have hsOne : 1 < s := by
    have hexp : 0 < Real.exp (5000 : Real) := Real.exp_pos _
    linarith
  have hsmOne : 0 < s - 1 := sub_pos.mpr hsOne
  have hsource : s * Real.log z = Real.log level :=
    (eq_div_iff hlogZ.ne').mp hs
  have hquot : Real.log z < Real.log level / (s - 1) := by
    calc
      Real.log z < (s * Real.log z) / (s - 1) := by
        apply (lt_div_iff₀ hsmOne).2
        nlinarith
      _ = Real.log level / (s - 1) := by rw [hsource]
  have hwz : z < dimensionOneRosserWeakCutoff level s := by
    have hexp := Real.exp_lt_exp.mpr hquot
    simpa [dimensionOneRosserWeakCutoff, Real.exp_log (by positivity : 0 < z)]
      using hexp
  have hwTwo : 2 <= dimensionOneRosserWeakCutoff level s :=
    hz.trans hwz.le
  have hlogW :
      Real.log (dimensionOneRosserWeakCutoff level s) =
        Real.log level / (s - 1) := by
    simp [dimensionOneRosserWeakCutoff]
  have hcoordinate :
      Real.log level /
          Real.log (dimensionOneRosserWeakCutoff level s) = s - 1 := by
    rw [hlogW, ← hsource]
    field_simp
  exact ⟨hwTwo, hwz, hcoordinate, by linarith⟩

theorem dimensionOneRosserWeakCutoff_factor_lt
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLarge : Real.exp 5000 + 2 <= s) {p : Nat}
    (hp : p ∈ (decimalSievePrimeProduct z).primeFactors) :
    (p : Real) < dimensionOneRosserWeakCutoff level s := by
  have hdata := dimensionOneRosserWeakCutoff_data hlevel hz hs hsLarge
  have hpz := (mem_decimalSievePrimeProductFactors_iff.mp hp).2.2
  exact hpz.trans_lt hdata.2.1

theorem sieveDensityBelow_decimalSievePrimeProduct_eq_decimalExcludedPrimeProduct
    {z w : Real}
    (hw : ∀ p, p ∈ (decimalSievePrimeProduct z).primeFactors ->
      (p : Real) < w) :
    sieveDensityBelow (decimalSievePrimeProduct z).primeFactors
        (fun p => (p : Real)⁻¹) w = decimalExcludedPrimeProduct z := by
  rw [sieveDensityBelow_eq_fullProduct _ _ hw,
    primeFactors_decimalSievePrimeProduct]
  rfl

theorem dimensionOneRosserWeakCutoff_error_transfer
    {V C s : Real} (hV : 0 <= V) (hC : 0 <= C) (hs : 2 <= s) :
    V / (s - 1) * (C * Real.exp (-(s - 1))) <=
      V / s * ((2 * Real.exp 1 * C) * Real.exp (-s)) := by
  have hsmOne : 0 < s - 1 := by linarith
  have hsPos : 0 < s := by linarith
  have hfrac : (1 : Real) / (s - 1) <= 2 / s := by
    rw [div_le_div_iff₀ hsmOne hsPos]
    nlinarith
  have hcommon : 0 <= V * C * Real.exp 1 * Real.exp (-s) := by
    positivity
  calc
    V / (s - 1) * (C * Real.exp (-(s - 1))) =
        (V * C * Real.exp 1 * Real.exp (-s)) * (1 / (s - 1)) := by
      rw [show (-(s - 1) : Real) = 1 + (-s) by ring, Real.exp_add]
      ring
    _ <= (V * C * Real.exp 1 * Real.exp (-s)) * (2 / s) := by
      exact mul_le_mul_of_nonneg_left hfrac hcommon
    _ = V / s * ((2 * Real.exp 1 * C) * Real.exp (-s)) := by ring

theorem exists_dimensionOneRosserWeakCutoffMainSums :
    ∃ C : Real, 1 <= C ∧
      ∀ (digit : Fin 10) (length : Nat) (d : PNat),
        ∀ {level z s : Real},
          2 <= level -> 2 <= z ->
          s = Real.log level / Real.log z ->
          Real.exp 5000 + 2 <= s ->
          let sieve := sourceBoundingSieve digit length d z
          let V := decimalExcludedPrimeProduct z
          V - V / s * (C * Real.exp (-s)) <
              sieve.mainSum (lowerRosserWeight level) ∧
            sieve.mainSum (upperRosserWeight level) <
              V + V / s * (C * Real.exp (-s)) := by
  obtain ⟨C₀, hC₀, hW64⟩ :=
    exists_dimensionOneRosserReciprocalMainSums_lt_exp_neg
  refine ⟨2 * Real.exp 1 * C₀, ?_, ?_⟩
  · have hExp : 1 <= Real.exp (1 : Real) := by
      have h := Real.add_one_le_exp (1 : Real)
      linarith
    calc
      (1 : Real) <= 2 * Real.exp 1 := by nlinarith
      _ = 2 * Real.exp 1 * 1 := by ring
      _ <= 2 * Real.exp 1 * C₀ := by
        gcongr
  · intro digit length d level z s hlevel hz hs hsLarge
    let sieve := sourceBoundingSieve digit length d z
    let w := dimensionOneRosserWeakCutoff level s
    have hdata := dimensionOneRosserWeakCutoff_data hlevel hz hs hsLarge
    have hfactor : ∀ p, p ∈ sieve.prodPrimes.primeFactors -> (p : Real) < w := by
      intro p hp
      exact dimensionOneRosserWeakCutoff_factor_lt hlevel hz hs hsLarge hp
    have hdecimal : ∀ p, p ∈ sieve.prodPrimes.primeFactors -> ¬p ∣ 10 := by
      intro p hp
      exact (mem_decimalSievePrimeProductFactors_iff.mp hp).2.1
    have hnu : (sieve.nu : Nat → Real) = (fun n : Nat => (n : Real)⁻¹) := by
      simpa [sieve] using sourceBoundingSieve_nu_eq_reciprocal digit length d z
    have hcoord : s - 1 = Real.log level / Real.log w := by
      simpa [w] using hdata.2.2.1.symm
    have hlarge : Real.exp 5000 + 1 <= s - 1 := hdata.2.2.2
    have hW := hW64 sieve hnu hdecimal hlevel hdata.1 hfactor hcoord hlarge
    have hprime : ∀ p, p ∈ sieve.prodPrimes.primeFactors -> p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primeFactors hp
    have hVeq :
        sieveDensityBelow sieve.prodPrimes.primeFactors
            (fun p => (p : Real)⁻¹) w = decimalExcludedPrimeProduct z := by
      simpa [sieve, w] using
        (sieveDensityBelow_decimalSievePrimeProduct_eq_decimalExcludedPrimeProduct
          (z := z) (w := w) hfactor)
    have hV : 0 <= decimalExcludedPrimeProduct z := by
      rw [← hVeq]
      exact (sieveDensityBelow_reciprocal_pos
        sieve.prodPrimes.primeFactors w hprime).le
    have hsTwo : 2 <= s := by
      have hexp : 0 < Real.exp (5000 : Real) := Real.exp_pos _
      linarith
    have hTransfer := dimensionOneRosserWeakCutoff_error_transfer
      hV (by linarith : 0 <= C₀) hsTwo
    dsimp at hW
    rw [hVeq] at hW
    constructor
    · calc
        decimalExcludedPrimeProduct z -
              decimalExcludedPrimeProduct z / s *
                ((2 * Real.exp 1 * C₀) * Real.exp (-s)) <=
            decimalExcludedPrimeProduct z -
              decimalExcludedPrimeProduct z / (s - 1) *
                (C₀ * Real.exp (-(s - 1))) := by
          exact sub_le_sub_left hTransfer _
        _ < sieve.mainSum (lowerRosserWeight level) := hW.1
    · calc
        sieve.mainSum (upperRosserWeight level) <
            decimalExcludedPrimeProduct z +
              decimalExcludedPrimeProduct z / (s - 1) *
                (C₀ * Real.exp (-(s - 1))) := hW.2
        _ <= decimalExcludedPrimeProduct z +
              decimalExcludedPrimeProduct z / s *
                ((2 * Real.exp 1 * C₀) * Real.exp (-s)) := by
          simpa [add_comm] using
            (add_le_add_left hTransfer (decimalExcludedPrimeProduct z))

end

end PrimesRestrictedDigits
