import PrimesRestrictedDigits.MajorArcs.M3Contribution

/-!
# M3 contribution at logarithmic scale

This specializes the corrected finite M3 aggregation to the single natural
major-arc exponent used throughout the source-facing proof.
-/

namespace PrimesRestrictedDigits

/-- The source error `X / (log X)^(4D)` yields the normalized M3 saving
`1 / (log X)^D`, under an explicit uniform residue-error premise. -/
theorem norm_majorArcClassThreeContribution_sub_density_le_logScale
    (digit : Fin 10) {X K D : Nat} (hK : 0 < K)
    (hX : X = 10 ^ K) {B : Real}
    (hQ : 10 ≤ Real.log (X : Real) ^ D)
    (hQX : Real.log (X : Real) ^ D ≤ (X : Real))
    (hB : 0 ≤ B)
    (s : Finset Nat) (w : Nat → Complex)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n 10)
    (T : Complex)
    (hAP : ∀ q : Nat, 0 < q → q ∣ X →
      (q : Real) ≤ Real.log (X : Real) ^ D →
      ∀ r : Nat, Nat.Coprime r q →
        ‖majorArcResidueWeightSum s w q r -
          T / (Nat.totient q : Complex)‖ ≤
            B * (X : Real) / Real.log (X : Real) ^ (4 * D)) :
    ‖majorArcClassThreeContribution X
        (Real.log (X : Real) ^ D)
        (paddedRestrictedNumbers digit K) s w -
      (restrictedDigitDensity digit : Complex) *
        ((paddedRestrictedNumbers digit K).card : Complex) * T /
          (X : Complex)‖ ≤
      14 * B * ((paddedRestrictedNumbers digit K).card : Real) /
        Real.log (X : Real) ^ D := by
  apply norm_majorArcClassThreeContribution_sub_density_le_sourceScale
    (Q := Real.log (X : Real) ^ D) (B := B)
    digit hK hX hQ hQX hB s w hsupport T
  intro q hq hqdiv hqQ r hcoprime
  simpa only [pow_mul'] using hAP q hq hqdiv hqQ r hcoprime

end PrimesRestrictedDigits
