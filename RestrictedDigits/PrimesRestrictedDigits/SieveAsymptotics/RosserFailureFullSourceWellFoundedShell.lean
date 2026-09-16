import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureUpperCubeRankZero

/-!
# Tail-free full source shells for well-founded recursion

The strict outer cutoff makes every complete inner failure sum use a shorter filtered prime
carrier. Consequently, a later simultaneous well-founded induction can supply the complete
opposite-sign inner target directly and set the explicit rank-tail remainder to zero. The
retained source cutoff is not recursive here. The recurrence source is
`IWANIEC-ROSSER-SIEVE-1980`, Eqs. (4.4)--(4.6), pp. 180--181, with the source shell in Eqs.
(8.8)--(8.11), pp. 198--200.
-/

namespace PrimesRestrictedDigits

/-- A member strictly below the outer cutoff witnesses strict growth of the
sorted filtered carrier.  No primality assumption is needed. -/
theorem sieveFactorsBelow_length_lt_of_mem_of_lt
    (P : Finset Nat) {p : Nat} {z : Real}
    (hpP : p ∈ P) (hpz : (p : Real) < z) :
    (sieveFactorsBelow P (p : Real)).length <
      (sieveFactorsBelow P z).length := by
  have hsubset :
      P.filter (fun q : Nat => (q : Real) < (p : Real)) ⊆
        P.filter (fun q : Nat => (q : Real) < z) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨
      (Finset.mem_filter.mp hq).1,
      (Finset.mem_filter.mp hq).2.trans hpz⟩
  have hpOuter : p ∈ P.filter (fun q : Nat => (q : Real) < z) :=
    Finset.mem_filter.mpr ⟨hpP, hpz⟩
  have hpNotInner :
      p ∉ P.filter (fun q : Nat => (q : Real) < (p : Real)) := by
    simp
  have hstrict :
      P.filter (fun q : Nat => (q : Real) < (p : Real)) ⊂
        P.filter (fun q : Nat => (q : Real) < z) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
      intro heq
      apply hpNotInner
      rw [heq]
      exact hpOuter⟩
  have hcard := Finset.card_lt_card hstrict
  simpa only [sieveFactorsBelow, Finset.length_sort] using hcard

/-- Lower complete source shell with the explicit remainder specialized
to zero.  The complete upper inner target is suitable for a strictly smaller
carrier induction hypothesis. -/
theorem lowerRosserFailureSum_le_cutoff_add_rawSourceShell_tailFree
    (P : Finset Nat) (D : Real) {level z s s0 : Real}
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
            D * dimensionOneRosserSourcePlusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)))) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      lowerRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z := by
  have htail :=
    lowerRosserFailureSum_le_cutoff_add_rawSourceShell_with_tail
      P D (fun _ => 0) hprime hlevel hz hs hsLower hss0 hcutoff (by
        intro p hpP hpCutoff hpz
        simpa using hInner p hpP hpCutoff hpz)
  simpa [dimensionOneRosserRawFirstRemainderSum] using htail

/--
Upper weak-cube complete source shell with both the explicit remainder and exact rank-zero
difference removed. The complete lower inner target is suitable for a strictly smaller carrier
induction hypothesis.
-/
theorem upperRosserFailureSum_le_cutoff_add_rawSourceShell_of_cube_le_rankZeroFree_tailFree
    (P : Finset Nat) (D : Real) {level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hcube : z ^ (3 : Nat) <= level)
    (hInner : ∀ p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) -> (p : Real) < z ->
      lowerRosserFailureSum P (fun q => (q : Real)⁻¹)
          (level / p) p <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusRaw
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserSourceMinusProfile
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)))) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      upperRosserFailureSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) +
        dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z := by
  have htail :=
    upperRosserFailureSum_le_cutoff_add_rawSourceShell_with_tail_of_cube_le_rankZeroFree
      P D (fun _ => 0) hprime hlevel hz hs hsLower hss0 hcutoff hcube (by
        intro p hpP hpCutoff hpz
        simpa using hInner p hpP hpCutoff hpz)
  simpa [dimensionOneRosserRawFirstRemainderSum] using htail

end PrimesRestrictedDigits
