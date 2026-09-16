import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTail

/-!
# Proposition 6.2 stable-pattern target-tail charge

The fixed canonical stable-pattern multiplicity is absorbed into the weak small-product
carrier tail. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, Eq. (9.4), p. 165, and
Proposition 7.2 statement, p. 148, and proof, pp. 163--168.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The full canonical stable-pattern multiple of the requested and weighted
ambient target tails has the same eventual log-log-width bound. -/
theorem exists_propositionSixTwoStablePatternTargetTailCharge_upper
    (epsilon : Real) (ell : Nat) :
    let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
    ∃ CtargetTail : Real, 0 < CtargetTail ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          let XNat : Nat := 10 ^ length
          let X : Real := (XNat : Real)
          let rho : Real := majorArcM2LogLogDelta XNat
          let A : Finset Nat := paddedRestrictedNumbers digit length
          let B : Finset Nat := maynardAmbientCarrier X
          let lambda : Real :=
            (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
          let near : Finset Nat := typeIINearXCarrier XNat rho
          (Fintype.card (PropositionSixTwoStablePattern ell M) : Real) *
              (((A \ near).card : Real) +
                lambda * ((B \ near).card : Real)) <=
            CtargetTail * rho * (A.card : Real) / Real.log X := by
  dsimp only
  let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let Kreal : Real :=
    (Fintype.card (PropositionSixTwoStablePattern ell M) : Real)
  obtain ⟨Ctail, hCtail, length0, hlength0, htail⟩ :=
    exists_typeIIWeakSmallProductTail_upper
  let CtargetTail : Real := (Kreal + 1) * Ctail
  have hKreal : 0 <= Kreal := by
    dsimp only [Kreal]
    exact Nat.cast_nonneg _
  have hCtargetTail : 0 < CtargetTail := by
    dsimp only [CtargetTail]
    exact mul_pos (by linarith) hCtail
  refine ⟨CtargetTail, hCtargetTail, length0, hlength0, ?_⟩
  intro length hlength digit
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let near : Finset Nat := typeIINearXCarrier XNat rho
  let tailCharge : Real :=
    ((A \ near).card : Real) + lambda * ((B \ near).card : Real)
  have htailAt := htail length hlength digit
  have htailBound : tailCharge <=
      Ctail * rho * (A.card : Real) / Real.log X := by
    simpa only [tailCharge, lambda, near, B, A, rho, X, XNat,
      mul_div_assoc] using htailAt
  have hXPos : 0 < X := by
    dsimp only [X, XNat]
    positivity
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact mul_nonneg (restrictedDigitDensity_nonneg digit)
      (div_nonneg (Nat.cast_nonneg A.card) hXPos.le)
  have htailCharge : 0 <= tailCharge := by
    dsimp only [tailCharge]
    exact add_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hlambda (Nat.cast_nonneg _))
  have htailRight :
      0 <= Ctail * rho * (A.card : Real) / Real.log X :=
    htailCharge.trans htailBound
  change Kreal * tailCharge <=
    CtargetTail * rho * (A.card : Real) / Real.log X
  calc
    Kreal * tailCharge <=
        Kreal * (Ctail * rho * (A.card : Real) / Real.log X) :=
      mul_le_mul_of_nonneg_left htailBound hKreal
    _ <= (Kreal + 1) *
        (Ctail * rho * (A.card : Real) / Real.log X) :=
      mul_le_mul_of_nonneg_right (by linarith) htailRight
    _ = CtargetTail * rho * (A.card : Real) / Real.log X := by
      dsimp only [CtargetTail]
      ring

end

end PrimesRestrictedDigits
