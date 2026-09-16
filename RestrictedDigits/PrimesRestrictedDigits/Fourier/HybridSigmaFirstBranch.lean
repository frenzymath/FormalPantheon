import PrimesRestrictedDigits.Fourier.HybridSourcePhases
import PrimesRestrictedDigits.Fourier.HybridSigmaFactorization
import PrimesRestrictedDigits.Fourier.HybridSigmaGrid
import PrimesRestrictedDigits.Fourier.ContinuousTransformSquaredVariation

/-!
# First specialized Sigma-product branch

This is the explicit repaired `Sigma_2 * Sigma_3` majorant underlying published Lemma 10.7,
pp. 182--183.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem decimalHybridFirstSigmaBranch_le
    (digit : Fin 10) {q d k v u : Nat}
    (hq : 0 < q) (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) {delta : Real} (hdelta : 0 ≤ delta) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    (∑ a : ReducedResidue q,
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / (d₃ : Real) + gamma) *
              normalizedPaddedDigitFourierMagnitudeSqAt digit v
                (((10 ^ k : Nat) : Real) *
                    hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  ((10 ^ k : Nat) : Real) * gamma))
          delta 0) ≤
      (largeSieveSamplingConstant * (1 + delta * (d₃ : Real)) *
        ((d₃ : Real) ^ largeSieveAlpha +
          (d₃ : Real) *
            (((10 ^ k : Nat) : Real) ^ (-largeSieveSigma)))) *
        ∑ c : ReducedResidue (q * (d₁ * d₂)),
          closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeSqAt digit v)
            (((10 ^ k : Nat) : Real) * delta)
            ((c.val.val : Real) / (q * (d₁ * d₂) : Nat)) := by
  dsimp only
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  change (∑ a : ReducedResidue q,
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / (d₃ : Real) + gamma) *
              normalizedPaddedDigitFourierMagnitudeSqAt digit v
                (((10 ^ k : Nat) : Real) *
                    hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  ((10 ^ k : Nat) : Real) * gamma))
          delta 0) ≤
      (largeSieveSamplingConstant * (1 + delta * (d₃ : Real)) *
        ((d₃ : Real) ^ largeSieveAlpha +
          (d₃ : Real) *
            (((10 ^ k : Nat) : Real) ^ (-largeSieveSigma)))) *
        ∑ c : ReducedResidue (q * (d₁ * d₂)),
          closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeSqAt digit v)
            (((10 ^ k : Nat) : Real) * delta)
            ((c.val.val : Real) / (q * (d₁ * d₂) : Nat))
  let F := normalizedPaddedDigitFourierMagnitudeAt digit k
  let G := normalizedPaddedDigitFourierMagnitudeSqAt digit v
  let C := largeSieveSamplingConstant * (1 + delta * (d₃ : Real)) *
    ((d₃ : Real) ^ largeSieveAlpha +
      (d₃ : Real) * (((10 ^ k : Nat) : Real) ^ (-largeSieveSigma)))
  have hd₁ : 0 < d₁ := hybridDenominatorFirstFactor_pos hd
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hD0 : (0 : Real) ≤ (10 ^ k : Nat) := by positivity
  have hFcont : Continuous F :=
    normalizedPaddedDigitFourierMagnitudeAt_continuous digit k
  have hGcont : Continuous G :=
    normalizedPaddedDigitFourierMagnitudeSqAt_continuous digit v
  have hF0 : ∀ z, 0 ≤ F z := fun z => by
    dsimp [F]
    exact normalizedPaddedDigitFourierMagnitudeAt_nonneg _ _ _
  have hG0 : ∀ z, 0 ≤ G z := fun z => by
    dsimp [G]
    rw [normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq]
    positivity
  have hrelax (a : ReducedResidue q) :
      (∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma => F
              (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                (b.2.val : Real) / d₃ + gamma) *
            G (((10 ^ k : Nat) : Real) *
                hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
              ((10 ^ k : Nat) : Real) * gamma)) delta 0) ≤
      ∑ b ∈ hybridPairReducedCarrier d₁ d₂ ×ˢ
          (Finset.univ : Finset (Fin d₃)),
        closedWindowMaximum
          (fun gamma => F
              (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                (b.2.val : Real) / d₃ + gamma) *
            G (((10 ^ k : Nat) : Real) *
                hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
              ((10 ^ k : Nat) : Real) * gamma)) delta 0 := by
    apply sum_hybridFullReducedCarrier_le_sum_pairProduct
    intro b
    apply closedWindowMaximum_nonneg
    · exact (hFcont.comp <| (continuous_const.add continuous_const).add continuous_id).mul
        (hGcont.comp <| (continuous_const.mul continuous_const).add
          (continuous_const.mul continuous_id))
    · intro z
      exact mul_nonneg (hF0 _) (hG0 _)
    · exact hdelta
  calc
    _ ≤ ∑ a : ReducedResidue q,
        ∑ b ∈ hybridPairReducedCarrier d₁ d₂ ×ˢ
            (Finset.univ : Finset (Fin d₃)),
          closedWindowMaximum
            (fun gamma => F
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / d₃ + gamma) *
              G (((10 ^ k : Nat) : Real) *
                  hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                ((10 ^ k : Nat) : Real) * gamma)) delta 0 := by
      exact Finset.sum_le_sum fun a _ => hrelax a
    _ ≤ ∑ a : ReducedResidue q,
        ∑ b ∈ hybridPairReducedCarrier d₁ d₂ ×ˢ
            (Finset.univ : Finset (Fin d₃)),
          closedWindowMaximum F delta
              (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                (b.2.val : Real) / d₃) *
            closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
              (((10 ^ k : Nat) : Real) *
                hybridSourceBetaTwo q d₁ d₂ d₃ a b.1) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact closedWindowMaximum_coupled_mul_le_mul hFcont hGcont hF0 hG0
        hdelta hD0 _ _
    _ ≤ C * ∑ a : ReducedResidue q,
        ∑ b ∈ hybridPairReducedCarrier d₁ d₂,
          closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
            (((10 ^ k : Nat) : Real) *
              hybridSourceBetaTwo q d₁ d₂ d₃ a b) := by
      calc
        _ ≤ ∑ a : ReducedResidue q, C *
            ∑ b ∈ hybridPairReducedCarrier d₁ d₂,
              closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
                (((10 ^ k : Nat) : Real) *
                  hybridSourceBetaTwo q d₁ d₂ d₃ a b) := by
          apply Finset.sum_le_sum
          intro a ha
          apply sum_product_mul_le_mul_sum_of_fiber_bound
            (s := hybridPairReducedCarrier d₁ d₂)
            (t := (Finset.univ : Finset (Fin d₃)))
            (A := fun b b₃ => closedWindowMaximum F delta
              (hybridSourceBetaTwo q d₁ d₂ d₃ a b +
                (b₃.val : Real) / d₃))
            (B := fun b => closedWindowMaximum G
              (((10 ^ k : Nat) : Real) * delta)
              (((10 ^ k : Nat) : Real) *
                hybridSourceBetaTwo q d₁ d₂ d₃ a b)) C
          · intro b hb
            exact closedWindowMaximum_nonneg hGcont hG0
              (mul_nonneg hD0 hdelta)
              (((10 ^ k : Nat) : Real) *
                hybridSourceBetaTwo q d₁ d₂ d₃ a b)
          · intro b hb
            have hgrid := completeFinGrid_largeSieveSampling
              digit k d₃ hd₃ hdelta
              (hybridSourceBetaTwo q d₁ d₂ d₃ a b)
            simpa [F, C, add_comm] using hgrid
        _ = _ := by rw [Finset.mul_sum]
    _ = C * ∑ c : ReducedResidue (q * (d₁ * d₂)),
          closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
            ((c.val.val : Real) / (q * (d₁ * d₂) : Nat)) := by
      congr 1
      rw [show (∑ a : ReducedResidue q,
          ∑ b ∈ hybridPairReducedCarrier d₁ d₂,
            closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
              (((10 ^ k : Nat) : Real) *
                hybridSourceBetaTwo q d₁ d₂ d₃ a b)) =
          ∑ a : ReducedResidue q,
            ∑ b : HybridMixedRadixReducedPair d₁ d₂,
              closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
                (((10 ^ k : Nat) : Real) *
                  hybridSourceBetaTwo q d₁ d₂ d₃ a b.val) by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_subtype
          (p := fun b : Fin d₁ × Fin d₂ =>
            (lowHighFinEquiv d₁ d₂ b).val.Coprime (d₁ * d₂))
          (hybridPairReducedCarrier d₁ d₂)
          (by simp [hybridPairReducedCarrier]) _]
      calc
        (∑ a : ReducedResidue q,
            ∑ b : HybridMixedRadixReducedPair d₁ d₂,
              closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
                (((10 ^ k : Nat) : Real) *
                  hybridSourceBetaTwo q d₁ d₂ d₃ a b.val)) =
            ∑ a : ReducedResidue q,
              ∑ b : HybridMixedRadixReducedPair d₁ d₂,
                closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
                  (((decimalHybridFirstTwoSourceResidueEquiv
                    hq hd hdvd hq10 (a, b)).val.val : Real) /
                    (q * (d₁ * d₂) : Nat)) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply closedWindowMaximum_eq_of_unitAddCircle_eq
            (normalizedPaddedDigitFourierMagnitudeSqAt_periodic digit v)
          exact (decimalHybridFirstTwoSourceResidue_betaTwo_unitAddCircle_eq
            hq hd hdvd hq10 a b).symm
        _ = ∑ x : ReducedResidue q ×
              HybridMixedRadixReducedPair d₁ d₂,
            closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
              (((decimalHybridFirstTwoSourceResidueEquiv
                hq hd hdvd hq10 x).val.val : Real) /
                (q * (d₁ * d₂) : Nat)) := by
          rw [Fintype.sum_prod_type]
        _ = ∑ c : ReducedResidue (q * (d₁ * d₂)),
              closedWindowMaximum G (((10 ^ k : Nat) : Real) * delta)
                ((c.val.val : Real) / (q * (d₁ * d₂) : Nat)) := by
          exact Fintype.sum_equiv
            (decimalHybridFirstTwoSourceResidueEquiv hq hd hdvd hq10)
            _ _ (fun x => rfl)
    _ = _ := by rfl

end

end PrimesRestrictedDigits
