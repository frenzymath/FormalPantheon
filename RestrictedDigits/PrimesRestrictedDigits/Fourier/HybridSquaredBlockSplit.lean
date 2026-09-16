import PrimesRestrictedDigits.Fourier.HybridSigmaFirstBranch
import PrimesRestrictedDigits.Fourier.HybridSigmaSecondBranch
import PrimesRestrictedDigits.Fourier.TransformBlockFactorization

/-!
# Squared transform block split for the alternative hybrid bound

This formalizes the exact `F_(V^2)` split immediately before the two specialized Sigma
branches in published Lemma 10.7, pp. 181--183.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- A period-one real function agrees at inputs representing the same point
of the unit additive circle. -/
theorem periodic_eq_of_unitAddCircle_eq
    {f : Real → Real} (hf : Function.Periodic f 1) {x y : Real}
    (hxy : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    f x = f y := by
  simpa only [Function.Periodic.lift_coe] using congrArg hf.lift hxy

/-- A compact closed-window maximum is subadditive. -/
theorem closedWindowMaximum_add_le_add
    {f g : Real → Real} (hf : Continuous f) (hg : Continuous g)
    {delta : Real} (hdelta : 0 ≤ delta) (x : Real) :
    closedWindowMaximum (fun z => f z + g z) delta x ≤
      closedWindowMaximum f delta x + closedWindowMaximum g delta x := by
  obtain ⟨eta, heta, hmax⟩ :=
    exists_closedWindowMaximum_eq (hf.add hg) hdelta x
  change closedWindowMaximum (f + g) delta x ≤
    closedWindowMaximum f delta x + closedWindowMaximum g delta x
  rw [hmax]
  exact add_le_add (le_closedWindowMaximum hf hdelta x heta)
    (le_closedWindowMaximum hg hdelta x heta)

/-- Exact factorization of a length-`2*v` transform magnitude into two
length-`v` blocks. -/
theorem normalizedPaddedDigitFourierMagnitudeAt_twoBlock
    (digit : Fin 10) (v : Nat) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) theta =
      normalizedPaddedDigitFourierMagnitudeAt digit v theta *
        normalizedPaddedDigitFourierMagnitudeAt digit v
          (((10 ^ v : Nat) : Real) * theta) := by
  have hfactor := normalizedPaddedDigitFourierMagnitudeAt_threeBlock
    digit (2 * v) v v 0 (by omega) theta
  simpa [normalizedPaddedDigitFourierMagnitudeAt_zero] using hfactor

/-- The length-`2*v` magnitude is bounded by the sum of the two squared block
magnitudes, with coefficient one. -/
theorem normalizedPaddedDigitFourierMagnitudeAt_twoBlock_le_sq_add
    (digit : Fin 10) (v : Nat) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) theta ≤
      normalizedPaddedDigitFourierMagnitudeSqAt digit v theta +
        normalizedPaddedDigitFourierMagnitudeSqAt digit v
          (((10 ^ v : Nat) : Real) * theta) := by
  rw [normalizedPaddedDigitFourierMagnitudeAt_twoBlock,
    normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq,
    normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq]
  have hx0 := normalizedPaddedDigitFourierMagnitudeAt_nonneg digit v theta
  have hy0 := normalizedPaddedDigitFourierMagnitudeAt_nonneg digit v
    (((10 ^ v : Nat) : Real) * theta)
  nlinarith [two_mul_le_add_sq
    (normalizedPaddedDigitFourierMagnitudeAt digit v theta)
    (normalizedPaddedDigitFourierMagnitudeAt digit v
      (((10 ^ v : Nat) : Real) * theta))]

/--
Pointwise source split from the raw squared-block phase into the two branch integrands.
-/
theorem decimalHybridSquaredBlockSplit_le
    (digit : Fin 10) {q d k v : Nat} (hd : 0 < d)
    (a : ReducedResidue q)
    (b₁ : Fin (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)))
    (b₂ : Fin (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)))
    (b₃ : Fin (hybridDenominatorThirdFactor d (10 ^ k)))
    (gamma : Real) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    normalizedPaddedDigitFourierMagnitudeAt digit k
        (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
          (b₃.val : Real) / d₃ + gamma) *
      normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
        (((10 ^ k : Nat) : Real) *
          (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
            (b₃.val : Real) / d₃ + gamma)) ≤
    normalizedPaddedDigitFourierMagnitudeAt digit k
        (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
          (b₃.val : Real) / d₃ + gamma) *
      normalizedPaddedDigitFourierMagnitudeSqAt digit v
        (((10 ^ k : Nat) : Real) *
            hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
          ((10 ^ k : Nat) : Real) * gamma) +
    normalizedPaddedDigitFourierMagnitudeAt digit k
        (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
          (b₃.val : Real) / d₃ + gamma) *
      normalizedPaddedDigitFourierMagnitudeSqAt digit v
        (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁ +
          (((10 ^ k * 10 ^ v : Nat) : Real) * gamma)) := by
  dsimp only
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  let beta := hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂)
  let thetaRaw := ((10 ^ k : Nat) : Real) *
    (beta + (b₃.val : Real) / d₃ + gamma)
  let thetaOne := ((10 ^ k : Nat) : Real) * beta +
    ((10 ^ k : Nat) : Real) * gamma
  let thetaTwo := decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁ +
    (((10 ^ k * 10 ^ v : Nat) : Real) * gamma)
  change normalizedPaddedDigitFourierMagnitudeAt digit k
      (beta + (b₃.val : Real) / d₃ + gamma) *
      normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) thetaRaw ≤
    normalizedPaddedDigitFourierMagnitudeAt digit k
        (beta + (b₃.val : Real) / d₃ + gamma) *
        normalizedPaddedDigitFourierMagnitudeSqAt digit v thetaOne +
      normalizedPaddedDigitFourierMagnitudeAt digit k
        (beta + (b₃.val : Real) / d₃ + gamma) *
        normalizedPaddedDigitFourierMagnitudeSqAt digit v thetaTwo
  have hdrop := hybridSourceBetaTwo_add_third_scale_unitAddCircle_eq
    (hybridDenominatorThirdFactor_pos hd)
    (hybridDenominatorThirdFactor_dvd_scale d (10 ^ k))
    a (b₁, b₂) b₃
  have hrawCircle : (thetaRaw : UnitAddCircle) = (thetaOne : UnitAddCircle) := by
    have htranslated := congrArg
      (fun z : UnitAddCircle =>
        z + ((((10 ^ k : Nat) : Real) * gamma : Real) : UnitAddCircle)) hdrop
    dsimp only [thetaRaw, thetaOne, beta]
    rw [show ((10 ^ k : Nat) : Real) *
        (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
          (b₃.val : Real) / d₃ + gamma) =
        ((10 ^ k : Nat) : Real) *
          (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
            (b₃.val : Real) / d₃) +
          ((10 ^ k : Nat) : Real) * gamma by ring]
    simpa only [AddCircle.coe_add] using htranslated
  have hraw :
      normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) thetaRaw =
        normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) thetaOne :=
    periodic_eq_of_unitAddCircle_eq
      (normalizedPaddedDigitFourierMagnitudeAt_periodic digit (2 * v)) hrawCircle
  have henlarged :=
    decimalHybridSourceBetaTwo_enlargedScale_unitAddCircle_eq hd a b₁ b₂
  have hscale :
      ((10 ^ v : Nat) : Real) * thetaOne =
        (((10 ^ k * 10 ^ v : Nat) : Real) * beta) +
          (((10 ^ k * 10 ^ v : Nat) : Real) * gamma) := by
    dsimp only [thetaOne]
    push_cast
    ring
  have hsecondCircle :
      ((((10 ^ v : Nat) : Real) * thetaOne : Real) : UnitAddCircle) =
        (thetaTwo : UnitAddCircle) := by
    have htranslated := congrArg
      (fun z : UnitAddCircle =>
        z + ((((10 ^ k * 10 ^ v : Nat) : Real) * gamma : Real) :
          UnitAddCircle)) henlarged
    rw [hscale]
    dsimp only [thetaTwo, beta]
    simpa only [AddCircle.coe_add] using htranslated
  have hsecond :
      normalizedPaddedDigitFourierMagnitudeSqAt digit v
          (((10 ^ v : Nat) : Real) * thetaOne) =
        normalizedPaddedDigitFourierMagnitudeSqAt digit v thetaTwo :=
    periodic_eq_of_unitAddCircle_eq
      (normalizedPaddedDigitFourierMagnitudeSqAt_periodic digit v) hsecondCircle
  have hsplit :=
    normalizedPaddedDigitFourierMagnitudeAt_twoBlock_le_sq_add digit v thetaOne
  have hsquared :
      normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) thetaRaw ≤
        normalizedPaddedDigitFourierMagnitudeSqAt digit v thetaOne +
          normalizedPaddedDigitFourierMagnitudeSqAt digit v thetaTwo := by
    rw [hraw]
    exact hsplit.trans_eq (congrArg
      (fun z => normalizedPaddedDigitFourierMagnitudeSqAt digit v thetaOne + z)
      hsecond)
  calc
    _ ≤ normalizedPaddedDigitFourierMagnitudeAt digit k
          (beta + (b₃.val : Real) / d₃ + gamma) *
        (normalizedPaddedDigitFourierMagnitudeSqAt digit v thetaOne +
          normalizedPaddedDigitFourierMagnitudeSqAt digit v thetaTwo) :=
      mul_le_mul_of_nonneg_left hsquared
        (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit k _)
    _ = _ := by ring

/-- Compact-window form of the source squared-block split. -/
theorem decimalHybridSquaredBlockWindow_le
    (digit : Fin 10) {q d k v : Nat} (hd : 0 < d)
    (a : ReducedResidue q)
    (b₁ : Fin (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)))
    (b₂ : Fin (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)))
    (b₃ : Fin (hybridDenominatorThirdFactor d (10 ^ k)))
    {delta : Real} (hdelta : 0 ≤ delta) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    closedWindowMaximum
        (fun gamma =>
          normalizedPaddedDigitFourierMagnitudeAt digit k
              (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
                (b₃.val : Real) / d₃ + gamma) *
            normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
              (((10 ^ k : Nat) : Real) *
                (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
                  (b₃.val : Real) / d₃ + gamma)))
        delta 0 ≤
      closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
                  (b₃.val : Real) / d₃ + gamma) *
              normalizedPaddedDigitFourierMagnitudeSqAt digit v
                (((10 ^ k : Nat) : Real) *
                    hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
                  ((10 ^ k : Nat) : Real) * gamma))
          delta 0 +
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
                  (b₃.val : Real) / d₃ + gamma) *
              normalizedPaddedDigitFourierMagnitudeSqAt digit v
                (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁ +
                  (((10 ^ k * 10 ^ v : Nat) : Real) * gamma)))
          delta 0 := by
  dsimp only
  let H := fun gamma =>
    normalizedPaddedDigitFourierMagnitudeAt digit k
        (hybridSourceBetaTwo q
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorThirdFactor d (10 ^ k)) a (b₁, b₂) +
          (b₃.val : Real) / hybridDenominatorThirdFactor d (10 ^ k) + gamma) *
      normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
        (((10 ^ k : Nat) : Real) *
          (hybridSourceBetaTwo q
              (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
              (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
              (hybridDenominatorThirdFactor d (10 ^ k)) a (b₁, b₂) +
            (b₃.val : Real) / hybridDenominatorThirdFactor d (10 ^ k) + gamma))
  let A := fun gamma =>
    normalizedPaddedDigitFourierMagnitudeAt digit k
        (hybridSourceBetaTwo q
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorThirdFactor d (10 ^ k)) a (b₁, b₂) +
          (b₃.val : Real) / hybridDenominatorThirdFactor d (10 ^ k) + gamma) *
      normalizedPaddedDigitFourierMagnitudeSqAt digit v
        (((10 ^ k : Nat) : Real) *
            hybridSourceBetaTwo q
              (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
              (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
              (hybridDenominatorThirdFactor d (10 ^ k)) a (b₁, b₂) +
          ((10 ^ k : Nat) : Real) * gamma)
  let B := fun gamma =>
    normalizedPaddedDigitFourierMagnitudeAt digit k
        (hybridSourceBetaTwo q
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorThirdFactor d (10 ^ k)) a (b₁, b₂) +
          (b₃.val : Real) / hybridDenominatorThirdFactor d (10 ^ k) + gamma) *
      normalizedPaddedDigitFourierMagnitudeSqAt digit v
        (decimalHybridSourceBetaThree q
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorThirdFactor d (10 ^ k)) k v a b₁ +
          (((10 ^ k * 10 ^ v : Nat) : Real) * gamma))
  have hF := normalizedPaddedDigitFourierMagnitudeAt_continuous digit k
  have hF₂ := normalizedPaddedDigitFourierMagnitudeAt_continuous digit (2 * v)
  have hG := normalizedPaddedDigitFourierMagnitudeSqAt_continuous digit v
  have hH : Continuous H := by
    exact (hF.comp <| (continuous_const.add continuous_const).add continuous_id).mul
      (hF₂.comp <| continuous_const.mul
        ((continuous_const.add continuous_const).add continuous_id))
  have hA : Continuous A := by
    exact (hF.comp <| (continuous_const.add continuous_const).add continuous_id).mul
      (hG.comp <| (continuous_const.mul continuous_const).add
        (continuous_const.mul continuous_id))
  have hB : Continuous B := by
    exact (hF.comp <| (continuous_const.add continuous_const).add continuous_id).mul
      (hG.comp <| continuous_const.add (continuous_const.mul continuous_id))
  have hpoint : ∀ gamma, H gamma ≤ A gamma + B gamma := fun gamma =>
    decimalHybridSquaredBlockSplit_le digit hd a b₁ b₂ b₃ gamma
  change closedWindowMaximum H delta 0 ≤
    closedWindowMaximum A delta 0 + closedWindowMaximum B delta 0
  calc
    _ ≤ closedWindowMaximum (fun z => A z + B z) delta 0 :=
      closedWindowMaximum_mono hH (hA.add hB) hpoint hdelta 0
    _ ≤ _ := closedWindowMaximum_add_le_add hA hB hdelta 0

/--
The unsplit full-carrier sum is bounded by the sum of the two exact branch inputs.
-/
theorem sum_decimalHybridSquaredBlock_le_add_branches
    (digit : Fin 10) {q d k v : Nat} (hd : 0 < d)
    {delta : Real} (hdelta : 0 ≤ delta) :
    let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
    let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
    let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
    (∑ a : ReducedResidue q,
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / d₃ + gamma) *
              normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                (((10 ^ k : Nat) : Real) *
                  (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                    (b.2.val : Real) / d₃ + gamma)))
          delta 0) ≤
      (∑ a : ReducedResidue q,
        ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
          closedWindowMaximum
            (fun gamma =>
              normalizedPaddedDigitFourierMagnitudeAt digit k
                  (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                    (b.2.val : Real) / d₃ + gamma) *
                normalizedPaddedDigitFourierMagnitudeSqAt digit v
                  (((10 ^ k : Nat) : Real) *
                      hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                    ((10 ^ k : Nat) : Real) * gamma))
            delta 0) +
        (∑ a : ReducedResidue q,
          ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃,
            closedWindowMaximum
              (fun gamma =>
                normalizedPaddedDigitFourierMagnitudeAt digit k
                    (hybridSourceBetaTwo q d₁ d₂ d₃ a b.1 +
                      (b.2.val : Real) / d₃ + gamma) *
                  normalizedPaddedDigitFourierMagnitudeSqAt digit v
                    (decimalHybridSourceBetaThree q d₁ d₂ d₃ k v
                        a b.1.1 +
                      (((10 ^ k * 10 ^ v : Nat) : Real) * gamma)))
              delta 0) := by
  dsimp only
  calc
    _ ≤ ∑ a : ReducedResidue q,
        ∑ b ∈ hybridFullReducedCarrier
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorThirdFactor d (10 ^ k)),
          (closedWindowMaximum
            (fun gamma =>
              normalizedPaddedDigitFourierMagnitudeAt digit k
                  (hybridSourceBetaTwo q
                      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
                      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
                      (hybridDenominatorThirdFactor d (10 ^ k)) a b.1 +
                    (b.2.val : Real) / hybridDenominatorThirdFactor d (10 ^ k) + gamma) *
                normalizedPaddedDigitFourierMagnitudeSqAt digit v
                  (((10 ^ k : Nat) : Real) *
                      hybridSourceBetaTwo q
                        (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
                        (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
                        (hybridDenominatorThirdFactor d (10 ^ k)) a b.1 +
                    ((10 ^ k : Nat) : Real) * gamma)) delta 0 +
          closedWindowMaximum
            (fun gamma =>
              normalizedPaddedDigitFourierMagnitudeAt digit k
                  (hybridSourceBetaTwo q
                      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
                      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
                      (hybridDenominatorThirdFactor d (10 ^ k)) a b.1 +
                    (b.2.val : Real) / hybridDenominatorThirdFactor d (10 ^ k) + gamma) *
                normalizedPaddedDigitFourierMagnitudeSqAt digit v
                  (decimalHybridSourceBetaThree q
                      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
                      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
                      (hybridDenominatorThirdFactor d (10 ^ k)) k v a b.1.1 +
                    (((10 ^ k * 10 ^ v : Nat) : Real) * gamma))) delta 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact decimalHybridSquaredBlockWindow_le digit hd a b.1.1 b.1.2 b.2 hdelta
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

end

end PrimesRestrictedDigits
