import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullShellRawSource

/-!
# Source shell with an explicit tail remainder

This specializes the complete raw shell to a source profile plus an arbitrary signed
remainder. The remainder is retained as an exact weighted finite sum; no tail estimate or sign
condition is introduced.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem dimensionOneRosserRawFirstRemainderSum_add
    (P : Finset Nat) {level s0 z : Real} (e₁ e₂ : Nat → Real) :
    dimensionOneRosserRawFirstRemainderSum P level s0 z
        (fun p : Nat => e₁ p + e₂ p) =
      dimensionOneRosserRawFirstRemainderSum P level s0 z e₁ +
        dimensionOneRosserRawFirstRemainderSum P level s0 z e₂ := by
  unfold dimensionOneRosserRawFirstRemainderSum
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/-- Lower complete-shell transport with a source profile and an explicit
weighted `tau` remainder. -/
theorem lowerRosserFailureSum_le_cutoff_add_rawSourceShell_with_tail
    (P : Finset Nat) (D : Real) (tau : Nat → Real) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hInner : ∀ p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) -> (p : Real) < z ->
      upperRosserFailureSum P (fun q => (q : Real)⁻¹)
          (level / p) p <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelPlusRaw
              (buchstabArgument level (p : Real)) +
            (D * dimensionOneRosserSourcePlusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)) + tau p))) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z +
        dimensionOneRosserRawFirstRemainderSum P level s0 z tau := by
  have hraw := lowerRosserFailureSum_le_cutoff_add_rawFirstShell P
    (fun p : Nat => D * dimensionOneRosserSourcePlusProfile
      (Real.log (level / (p : Real)))
      (buchstabArgument level (p : Real)) + tau p) hprime hlevel hz hs hsLower
      hss0 hcutoff hInner
  calc
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
          dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
          dimensionOneRosserRawFirstRemainderSum P level s0 z
            (fun p : Nat => D * dimensionOneRosserSourcePlusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)) + tau p) := hraw
    _ = lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
        (D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z +
          dimensionOneRosserRawFirstRemainderSum P level s0 z tau) := by
      rw [dimensionOneRosserRawFirstRemainderSum_add,
        dimensionOneRosserRawFirstRemainderSum_sourcePlus_eq
          P hlevel hz hs hsLower hcutoff]
    _ = _ := by ring

/-- Upper weak-cube complete-shell transport with a source profile and an
explicit weighted `tau` remainder. -/
theorem upperRosserFailureSum_le_cutoff_add_rawSourceShell_with_tail_of_cube_le
    (P : Finset Nat) (D : Real) (tau : Nat → Real) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hcube : z ^ 3 <= level)
    (hInner : ∀ p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) -> (p : Real) < z ->
      lowerRosserFailureSum P (fun q => (q : Real)⁻¹)
          (level / p) p <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusRaw
              (buchstabArgument level (p : Real)) +
            (D * dimensionOneRosserSourceMinusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)) + tau p))) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      upperRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        (upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level z 0 -
          upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) 0) +
        dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z +
        dimensionOneRosserRawFirstRemainderSum P level s0 z tau := by
  have hraw := upperRosserFailureSum_le_cutoff_add_rawFirstShell_of_cube_le P
    (fun p : Nat => D * dimensionOneRosserSourceMinusProfile
      (Real.log (level / (p : Real)))
      (buchstabArgument level (p : Real)) + tau p) hprime hlevel hz hs hsLower
      hss0 hcutoff hcube hInner
  calc
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        upperRosserFailureSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) +
          (upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
              level z 0 -
            upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
              level (level ^ (1 / s0)) 0) +
          dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
          dimensionOneRosserRawFirstRemainderSum P level s0 z
            (fun p : Nat => D * dimensionOneRosserSourceMinusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)) + tau p) := hraw
    _ = upperRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        (upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level z 0 -
          upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) 0) +
        dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
        (D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z +
          dimensionOneRosserRawFirstRemainderSum P level s0 z tau) := by
      rw [dimensionOneRosserRawFirstRemainderSum_add,
        dimensionOneRosserRawFirstRemainderSum_sourceMinus_eq
          P hlevel hz hs (by linarith) hcutoff]
    _ = _ := by ring

end PrimesRestrictedDigits
