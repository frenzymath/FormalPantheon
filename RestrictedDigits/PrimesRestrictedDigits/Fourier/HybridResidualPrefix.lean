import PrimesRestrictedDigits.Fourier.HybridResidualSource
import PrimesRestrictedDigits.Fourier.HybridResidueCRT
import PrimesRestrictedDigits.Fourier.TransformPrefix

/-!
# Residual Squared Prefix and Source Reindex

This file formalizes the prefix replacement and exact reduced-residue reindex immediately
preceding equation (10.16) in Maynard's Lemma 10.7. See `MAYNARD-PRD-PUBLISHED`, pp. 184--185.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem normalizedPaddedDigitFourierMagnitudeSqAt_le_prefix
    (digit : Fin 10) {r v : Nat} (hrv : r <= v) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeSqAt digit v theta <=
      normalizedPaddedDigitFourierMagnitudeSqAt digit r theta := by
  rw [normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq,
    normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq]
  have hprefix := normalizedPaddedDigitFourierMagnitudeAt_le_prefix
    digit hrv theta
  have hv := normalizedPaddedDigitFourierMagnitudeAt_nonneg digit v theta
  have hr := normalizedPaddedDigitFourierMagnitudeAt_nonneg digit r theta
  nlinarith

theorem closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeSqAt_le_prefix
    (digit : Fin 10) {r v : Nat} {delta : Real}
    (hrv : r <= v) (hdelta : 0 <= delta) (theta : Real) :
    closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeSqAt digit v) delta theta <=
      closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeSqAt digit r) delta theta := by
  exact closedWindowMaximum_mono
    (normalizedPaddedDigitFourierMagnitudeSqAt_continuous digit v)
    (normalizedPaddedDigitFourierMagnitudeSqAt_continuous digit r)
    (normalizedPaddedDigitFourierMagnitudeSqAt_le_prefix digit hrv)
    hdelta theta

/-- Natural denominators in the literal source band `q ~ Q`, coprime to ten. -/
def hybridResidualSourceDenominators (Q : Nat) : Finset Nat :=
  (Finset.Icc 1 Q).filter fun q => Q < 10 * q && q.Coprime 10

theorem mem_hybridResidualSourceDenominators_iff {Q q : Nat} :
    q ∈ hybridResidualSourceDenominators Q <->
      1 <= q ∧ q <= Q ∧ Q < 10 * q ∧ q.Coprime 10 := by
  simp [hybridResidualSourceDenominators, and_assoc]

/-- The source residual sum as an outer denominator sum and an inner sum over
canonical reduced residues. -/
noncomputable def hybridResidualReducedSourceSum
    (digit : Fin 10) (length M Q : Nat) (delta : Real) : Real :=
  ∑ q ∈ hybridResidualSourceDenominators Q,
    ∑ a : ReducedResidue (M * q),
      closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeSqAt digit length) delta
        ((a.val.val : Real) / ((M * q : Nat) : Real))

theorem hybridResidualReducedSourceSum_eq_fractionSourceCarrier
    (digit : Fin 10) (length M Q : Nat) (delta : Real) :
    hybridResidualReducedSourceSum digit length M Q delta =
      ∑ x ∈ hybridResidualFractionSourceCarrier M Q,
        closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeSqAt digit length) delta
          (hybridResidualFractionValue M x) := by
  classical
  rw [hybridResidualReducedSourceSum, Finset.sum_sigma']
  apply Finset.sum_bij
    (fun x _ => (x.1, x.2.val.val))
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hq, _⟩
    have hqData := mem_hybridResidualSourceDenominators_iff.mp hq
    apply mem_hybridResidualFractionSourceCarrier_iff.mpr
    exact ⟨hqData.1, hqData.2.1, hqData.2.2.1, hqData.2.2.2,
      x.2.val.isLt, x.2.property⟩
  · rintro ⟨qx, ax⟩ hx ⟨qy, ay⟩ hy hxy
    have hq : qx = qy := congrArg Prod.fst hxy
    subst qy
    have hax : ax = ay := by
      apply Subtype.ext
      apply Fin.ext
      exact congrArg Prod.snd hxy
    exact Sigma.ext rfl (heq_of_eq hax)
  · intro y hy
    have hyData := mem_hybridResidualFractionSourceCarrier_iff.mp hy
    let a : ReducedResidue (M * y.1) :=
      ⟨⟨y.2, hyData.2.2.2.2.1⟩, hyData.2.2.2.2.2⟩
    refine ⟨⟨y.1, a⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      exact ⟨mem_hybridResidualSourceDenominators_iff.mpr
        ⟨hyData.1, hyData.2.1, hyData.2.2.1, hyData.2.2.2.1⟩,
        Finset.mem_univ a⟩
    · rfl
  · intro x hx
    rfl

theorem hybridResidualReducedSourceSum_le_prefix
    (digit : Fin 10) {r v M Q : Nat} {delta : Real}
    (hrv : r <= v) (hdelta : 0 <= delta) :
    hybridResidualReducedSourceSum digit v M Q delta <=
      hybridResidualReducedSourceSum digit r M Q delta := by
  unfold hybridResidualReducedSourceSum
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro a ha
  exact closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeSqAt_le_prefix
    digit hrv hdelta _

end

end PrimesRestrictedDigits
