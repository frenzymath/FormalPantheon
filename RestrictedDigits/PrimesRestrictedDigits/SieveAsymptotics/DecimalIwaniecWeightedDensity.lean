import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatio
import PrimesRestrictedDigits.SieveAsymptotics.IwaniecWeightedDensityLogTail
import PrimesRestrictedDigits.SieveAsymptotics.IwaniecWeightedPartialSummation

/-!
# Iwaniec's weighted density estimate for decimal-admissible primes

This specializes Iwaniec's Lemma 21, Eq. (8.2), `IWANIEC-ROSSER-SIEVE-1980`, printed p. 198,
using the dimension hypothesis on p. 171; see its applications on pp. 199 and 201.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Iwaniec's weighted density estimate from an explicit dimension-one
density-ratio majorant on the same strict-upper interval. -/
theorem iwaniecWeightedDensitySum_le_of_ratio
    (P : Finset Nat) {K w z : Real} (B : Real -> Real)
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hw : 2 <= w) (hwz : w < z)
    (hRatio : ∀ u : Real, w <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u))
    (hBcont : ContinuousOn B (Icc w z))
    (hBmono : MonotoneOn B (Icc w z))
    (hB0 : ∀ x ∈ Icc w z, 0 <= B x) :
    (∑ p ∈ P.filter (fun p : Nat =>
        w <= (p : Real) ∧ (p : Real) < z),
      (p : Real)⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
        (Real.log (p : Real) / Real.log z) * B (p : Real)) <=
      (∫ x in w..z, B x / (x * Real.log x)) +
        2 * K * B z / Real.log w := by
  let V : Real -> Real :=
    sieveDensityBelow P (fun q => (q : Real)⁻¹)
  let a : Nat -> Real := fun k =>
    if k ∈ P then
      (k : Real)⁻¹ * (V (k : Real) / V z) *
        (Real.log (k : Real) / Real.log z)
    else 0
  have hcarrier :
      (naturalLeftClosedRightOpenInterval w z).filter (fun k => k ∈ P) =
        P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z) := by
    ext k
    simp only [Finset.mem_filter, mem_naturalLeftClosedRightOpenInterval]
    aesop
  have hsum :
      (∑ p ∈ P.filter (fun p : Nat =>
          w <= (p : Real) ∧ (p : Real) < z),
        (p : Real)⁻¹ * (V (p : Real) / V z) *
          (Real.log (p : Real) / Real.log z) * B (p : Real)) =
        ∑ k ∈ naturalLeftClosedRightOpenInterval w z,
          a k * B (k : Real) := by
    rw [← hcarrier]
    simp [a, Finset.filter_mem_eq_inter]
  have htail : ∀ i ∈ naturalLeftClosedRightOpenInterval w z,
      (∑ k ∈ naturalLeftClosedRightOpenInterval (i : Real) z, a k) <=
        (∫ x in (i : Real)..z, 1 / (x * Real.log x)) +
          2 * K / Real.log (i : Real) := by
    intro i hi
    have hiBounds := mem_naturalLeftClosedRightOpenInterval.mp hi
    have hcarrierTail :
        (naturalLeftClosedRightOpenInterval (i : Real) z).filter
            (fun k => k ∈ P) =
          P.filter (fun p : Nat =>
            (i : Real) <= (p : Real) ∧ (p : Real) < z) := by
      ext k
      simp only [Finset.mem_filter, mem_naturalLeftClosedRightOpenInterval]
      aesop
    have htailEq :
        (∑ k ∈ naturalLeftClosedRightOpenInterval (i : Real) z, a k) =
          ∑ p ∈ P.filter (fun p : Nat =>
              (i : Real) <= (p : Real) ∧ (p : Real) < z),
            (p : Real)⁻¹ * (V (p : Real) / V z) *
              (Real.log (p : Real) / Real.log z) := by
      rw [← hcarrierTail]
      simp [a, Finset.filter_mem_eq_inter]
    rw [htailEq]
    exact sum_reciprocal_mul_densityRatio_mul_logRatio_le_of_ratioMajorant
      P hK (hw.trans hiBounds.1) hiBounds.2 hprime
        (fun t hit htz => hRatio t (hiBounds.1.trans hit) htz)
  rw [hsum]
  exact weightedNaturalSum_le_integral_add_of_tail
    a B hK hw hwz hBcont hBmono hB0 htail

/-- One coefficient, chosen uniformly before the finite prime set, weight,
and cutoffs, gives Iwaniec's decimal weighted density estimate. -/
theorem exists_decimalIwaniecWeightedDensity_bound :
    ∃ K : Real, 2 <= K ∧
      ∀ (P : Finset Nat) (B : Real -> Real) (w z : Real),
        (∀ p ∈ P, p.Prime) -> (∀ p ∈ P, ¬p ∣ 10) ->
        2 <= w -> w < z ->
        ContinuousOn B (Icc w z) -> MonotoneOn B (Icc w z) ->
        (∀ x ∈ Icc w z, 0 <= B x) ->
        (∑ p ∈ P.filter (fun p : Nat =>
            w <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ *
            (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
            (Real.log (p : Real) / Real.log z) * B (p : Real)) <=
          (∫ x in w..z, B x / (x * Real.log x)) +
            2 * K * B z / Real.log w := by
  obtain ⟨K, hK, hRatio⟩ := exists_decimalSieveDensityRatio_bound
  refine ⟨K, hK, ?_⟩
  intro P B w z hprime hdecimal hw hwz hBcont hBmono hB0
  apply iwaniecWeightedDensitySum_le_of_ratio
    P B (by linarith [hK]) hprime hw hwz
  · intro u hwu huz
    exact (hRatio P u z hprime hdecimal (hw.trans hwu) huz).le
  · exact hBcont
  · exact hBmono
  · exact hB0

end PrimesRestrictedDigits
