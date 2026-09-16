import PrimesRestrictedDigits.Fourier.HybridSourcePhases
import PrimesRestrictedDigits.Fourier.HybridSigmaFactorization
import PrimesRestrictedDigits.Fourier.HybridSigmaGrid
import PrimesRestrictedDigits.Fourier.ContinuousTransformSquaredVariation

/-!
# Second specialized Sigma-product branch

This is the explicit repaired `Sigma_4 * Sigma_5` majorant underlying published Lemma 10.7,
pp. 182--183.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem decimalHybridSecondSigmaBranch_le
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
                (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                    a b.1.1 +
                  (((10 ^ k * 10 ^ v : Nat) : Real) * gamma)))
          delta 0) ≤
      (largeSieveSamplingConstant *
        (1 + delta * ((d₂ * d₃ : Nat) : Real)) *
        (((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha +
          ((d₂ * d₃ : Nat) : Real) *
            (((10 ^ k : Nat) : Real) ^ (-largeSieveSigma)))) *
        ∑ c : ReducedResidue (q * d₁),
          closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeSqAt digit v)
            (((10 ^ k * 10 ^ v : Nat) : Real) * delta)
            ((c.val.val : Real) / (q * d₁ : Nat)) := by
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
                (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                    a b.1.1 +
                  (((10 ^ k * 10 ^ v : Nat) : Real) * gamma)))
          delta 0) ≤
      (largeSieveSamplingConstant *
        (1 + delta * ((d₂ * d₃ : Nat) : Real)) *
        (((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha +
          ((d₂ * d₃ : Nat) : Real) *
            (((10 ^ k : Nat) : Real) ^ (-largeSieveSigma)))) *
        ∑ c : ReducedResidue (q * d₁),
          closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeSqAt digit v)
            (((10 ^ k * 10 ^ v : Nat) : Real) * delta)
            ((c.val.val : Real) / (q * d₁ : Nat))
  let F := normalizedPaddedDigitFourierMagnitudeAt digit k
  let G := normalizedPaddedDigitFourierMagnitudeSqAt digit v
  let S : Nat := 10 ^ k * 10 ^ v
  let C := largeSieveSamplingConstant *
    (1 + delta * ((d₂ * d₃ : Nat) : Real)) *
    (((d₂ * d₃ : Nat) : Real) ^ largeSieveAlpha +
      ((d₂ * d₃ : Nat) : Real) *
        (((10 ^ k : Nat) : Real) ^ (-largeSieveSigma)))
  have hd₁ : 0 < d₁ := hybridDenominatorFirstFactor_pos hd
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hd₂₃ : 0 < d₂ * d₃ := Nat.mul_pos hd₂ hd₃
  have hS0 : (0 : Real) ≤ S := by positivity
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
            G (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                a b.1.1 + (S : Real) * gamma)) delta 0) ≤
      ∑ b ∈ (reducedResidueCarrier d₁ ×ˢ
          (Finset.univ : Finset (Fin d₂))) ×ˢ
          (Finset.univ : Finset (Fin d₃)),
        closedWindowMaximum
          (fun gamma => F
              (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                (b.2.val : Real) / d₃ + gamma) *
            G (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                a b.1.1 + (S : Real) * gamma)) delta 0 := by
    apply sum_hybridFullReducedCarrier_le_sum_firstProduct
    intro b
    apply closedWindowMaximum_nonneg
    · exact (hFcont.comp <| (continuous_const.add continuous_const).add continuous_id).mul
        (hGcont.comp <| continuous_const.add (continuous_const.mul continuous_id))
    · intro z
      exact mul_nonneg (hF0 _) (hG0 _)
    · exact hdelta
  have hgrid (a : ReducedResidue q) (b₁ : Fin d₁) :
      (∑ b₂ : Fin d₂, ∑ b₃ : Fin d₃,
        closedWindowMaximum F delta
          (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
            (b₃.val : Real) / d₃)) ≤ C := by
    calc
      _ = ∑ x : Fin d₂ × Fin d₃,
          closedWindowMaximum F delta
            (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, x.1) +
              (x.2.val : Real) / d₃) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : Fin d₂ × Fin d₃,
          closedWindowMaximum F delta
            (((a.val.val : Real) / q +
                (b₁.val : Real) / (d₁ * d₂ * d₃ : Nat)) +
              ((lowHighFinEquiv d₂ d₃ x).val : Real) / (d₂ * d₃)) := by
        apply Finset.sum_congr rfl
        intro x hx
        simpa only [Nat.cast_mul] using congrArg
          (closedWindowMaximum F delta)
          (hybridSourceBetaTwo_add_third_eq_grid hd₁ hd₂ hd₃
            a b₁ x.1 x.2)
      _ = ∑ y : Fin (d₂ * d₃),
          closedWindowMaximum F delta
            (((a.val.val : Real) / q +
                (b₁.val : Real) / (d₁ * d₂ * d₃ : Nat)) +
              (y.val : Real) / (d₂ * d₃)) := by
        simpa only [Nat.cast_mul] using sum_lowHighFinEquiv d₂ d₃
          (fun y => closedWindowMaximum F delta
            (((a.val.val : Real) / q +
                (b₁.val : Real) / (d₁ * d₂ * d₃ : Nat)) +
              (y.val : Real) / (d₂ * d₃ : Nat)))
      _ ≤ C := by
        have hsamp := completeFinGrid_largeSieveSampling digit k
          (d₂ * d₃) hd₂₃ hdelta
          ((a.val.val : Real) / q +
            (b₁.val : Real) / (d₁ * d₂ * d₃ : Nat))
        simpa [F, C, add_comm] using hsamp
  have hfactor (a : ReducedResidue q) :
      (∑ b ∈ (reducedResidueCarrier d₁ ×ˢ
          (Finset.univ : Finset (Fin d₂))) ×ˢ
          (Finset.univ : Finset (Fin d₃)),
        closedWindowMaximum F delta
            (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
              (b.2.val : Real) / d₃) *
          closedWindowMaximum G ((S : Real) * delta)
            (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
              a b.1.1)) ≤
      C * ∑ b₁ ∈ reducedResidueCarrier d₁,
        closedWindowMaximum G ((S : Real) * delta)
          (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁) := by
    rw [Finset.sum_product, Finset.sum_product]
    calc
      _ = ∑ b₁ ∈ reducedResidueCarrier d₁,
          (∑ b₂ : Fin d₂, ∑ b₃ : Fin d₃,
            closedWindowMaximum F delta
              (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
                (b₃.val : Real) / d₃)) *
            closedWindowMaximum G ((S : Real) * delta)
              (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁) := by
        apply Finset.sum_congr rfl
        intro b₁ hb₁
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b₂ hb₂
        rw [Finset.sum_mul]
      _ ≤ ∑ b₁ ∈ reducedResidueCarrier d₁,
          C * closedWindowMaximum G ((S : Real) * delta)
            (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁) := by
        apply Finset.sum_le_sum
        intro b₁ hb₁
        exact mul_le_mul_of_nonneg_right (hgrid a b₁)
          (closedWindowMaximum_nonneg hGcont hG0
            (mul_nonneg hS0 hdelta) _)
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ ∑ a : ReducedResidue q,
        ∑ b ∈ (reducedResidueCarrier d₁ ×ˢ
            (Finset.univ : Finset (Fin d₂))) ×ˢ
            (Finset.univ : Finset (Fin d₃)),
          closedWindowMaximum
            (fun gamma => F
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / d₃ + gamma) *
              G (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                  a b.1.1 + (S : Real) * gamma)) delta 0 := by
      exact Finset.sum_le_sum fun a _ => hrelax a
    _ ≤ ∑ a : ReducedResidue q,
        ∑ b ∈ (reducedResidueCarrier d₁ ×ˢ
            (Finset.univ : Finset (Fin d₂))) ×ˢ
            (Finset.univ : Finset (Fin d₃)),
          closedWindowMaximum F delta
              (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                (b.2.val : Real) / d₃) *
            closedWindowMaximum G ((S : Real) * delta)
              (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                a b.1.1) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact closedWindowMaximum_coupled_mul_le_mul hFcont hGcont hF0 hG0
        hdelta hS0 _ _
    _ ≤ C * ∑ a : ReducedResidue q,
        ∑ b₁ ∈ reducedResidueCarrier d₁,
          closedWindowMaximum G ((S : Real) * delta)
            (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁) := by
      calc
        _ ≤ ∑ a : ReducedResidue q, C *
            ∑ b₁ ∈ reducedResidueCarrier d₁,
              closedWindowMaximum G ((S : Real) * delta)
                (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                  a b₁) := by
          exact Finset.sum_le_sum fun a _ => hfactor a
        _ = _ := by rw [Finset.mul_sum]
    _ = C * ∑ c : ReducedResidue (q * d₁),
          closedWindowMaximum G ((S : Real) * delta)
            ((c.val.val : Real) / (q * d₁ : Nat)) := by
      congr 1
      rw [show (∑ a : ReducedResidue q,
          ∑ b₁ ∈ reducedResidueCarrier d₁,
            closedWindowMaximum G ((S : Real) * delta)
              (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁)) =
          ∑ a : ReducedResidue q, ∑ b₁ : ReducedResidue d₁,
            closedWindowMaximum G ((S : Real) * delta)
              (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁.val) by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_subtype (p := fun b₁ : Fin d₁ => b₁.val.Coprime d₁)
          (reducedResidueCarrier d₁)
          (by simp [reducedResidueCarrier]) _]
      calc
        (∑ a : ReducedResidue q, ∑ b₁ : ReducedResidue d₁,
            closedWindowMaximum G ((S : Real) * delta)
              (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁.val)) =
          ∑ a : ReducedResidue q, ∑ b₁ : ReducedResidue d₁,
            closedWindowMaximum G ((S : Real) * delta)
              (((decimalHybridFirstReducedResidueEquiv
                hq hd hdvd hq10 (a, b₁)).val.val : Real) / (q * d₁ : Nat)) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b₁ hb₁
          apply closedWindowMaximum_eq_of_unitAddCircle_eq
            (normalizedPaddedDigitFourierMagnitudeSqAt_periodic digit v)
          exact (decimalHybridFirstResidue_betaThree_unitAddCircle_eq
            hq hd hdvd hq10 a b₁).symm
        _ = ∑ x : ReducedResidue q × ReducedResidue d₁,
            closedWindowMaximum G ((S : Real) * delta)
              (((decimalHybridFirstReducedResidueEquiv
                hq hd hdvd hq10 x).val.val : Real) / (q * d₁ : Nat)) := by
          rw [Fintype.sum_prod_type]
        _ = ∑ c : ReducedResidue (q * d₁),
            closedWindowMaximum G ((S : Real) * delta)
              ((c.val.val : Real) / (q * d₁ : Nat)) := by
          exact Fintype.sum_equiv
            (decimalHybridFirstReducedResidueEquiv hq hd hdvd hq10)
            _ _ (fun x => rfl)
    _ = _ := by rfl

end

end PrimesRestrictedDigits
