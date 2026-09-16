import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowTerminalOccurrence

/-!
# Complete-modulus bounds for Section 6 terminal occurrences

The four terminal families have different cutoff envelopes. In particular, the repeated-low
family uses its pre-repeat low classification, while the repeated-high family necessarily
retains two prime-scale factors.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact family-by-family complete-modulus envelope for one terminal
occurrence. -/
theorem SectionSixLowTerminalOccurrence.state_modulus_le_envelope
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {root : SectionSixLowActiveNode X delta theta R y band ell}
    (term : SectionSixLowTerminalOccurrence root) :
    (term.state.1 : Real) ≤ match term with
      | .base _ => R
      | .strictHigh _ => R * X ^ theta
      | .repeatedLow _ => R * X ^ theta
      | .repeatedHigh _ => R * (X ^ theta) ^ (2 : Nat) := by
  cases term with
  | base occurrence =>
      exact occurrence.parent.target.modulus_le
  | strictHigh occurrence =>
      have hq : (occurrence.q : Real) ≤ X ^ theta :=
        (mem_sievePrimeInterval.mp
          (mem_sectionSixStateHighPrimeInterval.mp occurrence.primeMem).1).2.2.trans
            occurrence.parent.target.upper_le_range
      have hR : 0 ≤ R :=
        (Nat.cast_nonneg occurrence.parent.target.state.1).trans
          occurrence.parent.target.modulus_le
      change
        ((occurrence.parent.target.state.1 * occurrence.q : Nat) : Real) ≤
          R * X ^ theta
      simpa only [Nat.cast_mul] using
        mul_le_mul occurrence.parent.target.modulus_le hq
          (Nat.cast_nonneg occurrence.q) hR
  | repeatedLow occurrence =>
      have hpre :=
        (mem_sectionSixStateLowPrimeInterval.mp occurrence.primeMem).2
      have hq : (occurrence.q : Real) ≤ X ^ theta :=
        (mem_sievePrimeInterval.mp
          (mem_sectionSixStateLowPrimeInterval.mp occurrence.primeMem).1).2.2.trans
            occurrence.parent.target.upper_le_range
      have hR : 0 ≤ R :=
        (Nat.cast_nonneg occurrence.parent.target.state.1).trans
          occurrence.parent.target.modulus_le
      change
        ((occurrence.parent.target.state.1 * occurrence.q *
          occurrence.q : Nat) : Real) ≤ R * X ^ theta
      simpa only [Nat.cast_mul] using
        mul_le_mul hpre hq (Nat.cast_nonneg occurrence.q) hR
  | repeatedHigh occurrence =>
      have hq : (occurrence.q : Real) ≤ X ^ theta :=
        (mem_sievePrimeInterval.mp
          (mem_sectionSixStateHighPrimeInterval.mp occurrence.primeMem).1).2.2.trans
            occurrence.parent.target.upper_le_range
      have hR : 0 ≤ R :=
        (Nat.cast_nonneg occurrence.parent.target.state.1).trans
          occurrence.parent.target.modulus_le
      have hqNonneg : 0 ≤ (occurrence.q : Real) := Nat.cast_nonneg _
      have hthetaNonneg : 0 ≤ X ^ theta := hqNonneg.trans hq
      have hfirst :
          (occurrence.parent.target.state.1 : Real) * occurrence.q ≤
            R * X ^ theta :=
        mul_le_mul occurrence.parent.target.modulus_le hq hqNonneg hR
      have hsecond :
          ((occurrence.parent.target.state.1 : Real) * occurrence.q) *
              occurrence.q ≤
            (R * X ^ theta) * X ^ theta :=
        mul_le_mul hfirst hq hqNonneg (mul_nonneg hR hthetaNonneg)
      change
        ((occurrence.parent.target.state.1 * occurrence.q *
          occurrence.q : Nat) : Real) ≤ R * (X ^ theta) ^ (2 : Nat)
      simpa only [Nat.cast_mul, pow_two, mul_assoc] using hsecond

private theorem sectionSix_decimalScale_one_lt
    {length : Nat} (hlength : 1 ≤ length) :
    (1 : Real) < ((10 ^ length : Nat) : Real) := by
  exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
    (by norm_num : 1 < (10 : Nat))

private theorem sectionSix_low_terminal_exponent_le_one
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    sectionSixThetaOne epsilon + sectionSixThetaGap epsilon +
        sectionSixThetaGap epsilon ≤ 1 := by
  rw [sectionSixThetaGap_eq]
  simp only [sectionSixThetaOne]
  linarith

private theorem sectionSix_high_terminal_exponent_le_one
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    1 - sectionSixThetaTwo epsilon + sectionSixThetaGap epsilon +
        sectionSixThetaGap epsilon ≤ 1 := by
  rw [sectionSixThetaGap_eq]
  simp only [sectionSixThetaTwo]
  linarith

/--
On the Proposition 6.1 parameter range, every complete modulus emitted from a strict low- or
high-band source root is at most the decimal scale `10^length`.
-/
theorem SectionSixLowTerminalOccurrence.source_state_modulus_le
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    {length ell : Nat} (hlength : 1 ≤ length)
    {region : Set (Fin ell → Real)}
    (band : SectionSixStateBand)
    (p : Fin ell → Nat)
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (delta : Real)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hband : sectionSixSourceBandMembership band
      ((10 ^ length : Nat) : Real)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real))
    (hcutoff_le_X :
      sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ≤
        ((10 ^ length : Nat) : Real))
    (term : SectionSixLowTerminalOccurrence
      (sectionSixSourceBandRoot hlength band p hp delta hdeltaGap
        hband hcutoff_le_X)) :
    (term.state.1 : Real) ≤ ((10 ^ length : Nat) : Real) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := sectionSix_decimalScale_one_lt hlength
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hXOne : 1 ≤ X := hX.le
  have hparameters := sectionSix_parameter_bounds hepsilon hepsilonSmall
  have hthetaOneLe : sectionSixThetaOne epsilon ≤ 1 :=
    hparameters.2.2.1.le
  have hthetaTwoLe : sectionSixThetaTwo epsilon ≤ 1 := by
    simp only [sectionSixThetaTwo]
    linarith
  have hthetaTwoNonneg : 0 ≤ sectionSixThetaTwo epsilon := by
    simp only [sectionSixThetaTwo]
    linarith
  have hlowExponent := sectionSix_low_terminal_exponent_le_one hepsilon
  have hhighExponent := sectionSix_high_terminal_exponent_le_one hepsilon
  have hbound := term.state_modulus_le_envelope
  cases band with
  | low =>
      cases term with
      | base occurrence =>
          exact hbound.trans <| by
            simpa only [sectionSixStateBandCutoff, X, Real.rpow_one] using
              Real.rpow_le_rpow_of_exponent_le hXOne hthetaOneLe
      | strictHigh occurrence =>
          refine hbound.trans ?_
          calc
            X ^ sectionSixThetaOne epsilon * X ^ sectionSixThetaGap epsilon =
                X ^ (sectionSixThetaOne epsilon +
                  sectionSixThetaGap epsilon) :=
              (Real.rpow_add hXPos _ _).symm
            _ ≤ X ^ (1 : Real) :=
              Real.rpow_le_rpow_of_exponent_le hXOne (by linarith)
            _ = X := Real.rpow_one X
      | repeatedLow occurrence =>
          refine hbound.trans ?_
          calc
            X ^ sectionSixThetaOne epsilon * X ^ sectionSixThetaGap epsilon =
                X ^ (sectionSixThetaOne epsilon +
                  sectionSixThetaGap epsilon) :=
              (Real.rpow_add hXPos _ _).symm
            _ ≤ X ^ (1 : Real) :=
              Real.rpow_le_rpow_of_exponent_le hXOne (by linarith)
            _ = X := Real.rpow_one X
      | repeatedHigh occurrence =>
          refine hbound.trans ?_
          rw [pow_two]
          calc
            X ^ sectionSixThetaOne epsilon *
                  (X ^ sectionSixThetaGap epsilon *
                    X ^ sectionSixThetaGap epsilon) =
                (X ^ sectionSixThetaOne epsilon *
                    X ^ sectionSixThetaGap epsilon) *
                  X ^ sectionSixThetaGap epsilon := by ring
            _ = X ^ (sectionSixThetaOne epsilon +
                    sectionSixThetaGap epsilon) *
                  X ^ sectionSixThetaGap epsilon := by
              rw [Real.rpow_add hXPos]
            _ = X ^ (sectionSixThetaOne epsilon +
                  sectionSixThetaGap epsilon +
                    sectionSixThetaGap epsilon) :=
              (Real.rpow_add hXPos _ _).symm
            _ ≤ X ^ (1 : Real) :=
              Real.rpow_le_rpow_of_exponent_le hXOne hlowExponent
            _ = X := Real.rpow_one X
  | high =>
      cases term with
      | base occurrence =>
          exact hbound.trans <| by
            change X ^ (1 - sectionSixThetaTwo epsilon) ≤ X
            have hexponent : 1 - sectionSixThetaTwo epsilon ≤ (1 : Real) := by
              linarith
            have hpower :
                X ^ (1 - sectionSixThetaTwo epsilon) ≤ X ^ (1 : Real) :=
              Real.rpow_le_rpow_of_exponent_le hXOne hexponent
            simpa only [Real.rpow_one] using hpower
      | strictHigh occurrence =>
          refine hbound.trans ?_
          calc
            X ^ (1 - sectionSixThetaTwo epsilon) *
                  X ^ sectionSixThetaGap epsilon =
                X ^ (1 - sectionSixThetaTwo epsilon +
                  sectionSixThetaGap epsilon) :=
              (Real.rpow_add hXPos _ _).symm
            _ ≤ X ^ (1 : Real) :=
              Real.rpow_le_rpow_of_exponent_le hXOne (by linarith)
            _ = X := Real.rpow_one X
      | repeatedLow occurrence =>
          refine hbound.trans ?_
          calc
            X ^ (1 - sectionSixThetaTwo epsilon) *
                  X ^ sectionSixThetaGap epsilon =
                X ^ (1 - sectionSixThetaTwo epsilon +
                  sectionSixThetaGap epsilon) :=
              (Real.rpow_add hXPos _ _).symm
            _ ≤ X ^ (1 : Real) :=
              Real.rpow_le_rpow_of_exponent_le hXOne (by linarith)
            _ = X := Real.rpow_one X
      | repeatedHigh occurrence =>
          refine hbound.trans ?_
          rw [pow_two]
          calc
            X ^ (1 - sectionSixThetaTwo epsilon) *
                  (X ^ sectionSixThetaGap epsilon *
                    X ^ sectionSixThetaGap epsilon) =
                (X ^ (1 - sectionSixThetaTwo epsilon) *
                    X ^ sectionSixThetaGap epsilon) *
                  X ^ sectionSixThetaGap epsilon := by ring
            _ = X ^ (1 - sectionSixThetaTwo epsilon +
                    sectionSixThetaGap epsilon) *
                  X ^ sectionSixThetaGap epsilon := by
              rw [Real.rpow_add hXPos]
            _ = X ^ (1 - sectionSixThetaTwo epsilon +
                  sectionSixThetaGap epsilon +
                    sectionSixThetaGap epsilon) :=
              (Real.rpow_add hXPos _ _).symm
            _ ≤ X ^ (1 : Real) :=
              Real.rpow_le_rpow_of_exponent_le hXOne hhighExponent
            _ = X := Real.rpow_one X

end

end PrimesRestrictedDigits
