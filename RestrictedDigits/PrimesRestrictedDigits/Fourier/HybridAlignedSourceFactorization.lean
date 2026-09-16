import PrimesRestrictedDigits.Fourier.HybridAlignedSourceReindex
import PrimesRestrictedDigits.Fourier.HybridSigmaOne
import PrimesRestrictedDigits.Fourier.HybridSquaredBlockSourceSum
import PrimesRestrictedDigits.Fourier.HybridSquaredBlockSplit
import PrimesRestrictedDigits.Fourier.TransformBlockFactorization
import PrimesRestrictedDigits.Fourier.TransformPrefix

/-!
# Aligned-source factorization and Sigma-one extraction

This file formalizes the coefficient-one factorization between equations (10.11) and (10.12)
of `MAYNARD-PRD-PUBLISHED`, pp. 181--183. The canonical aligned carrier is retained while
periodicity transports the two leading blocks to the source phase.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

private theorem unitAddCircle_nat_mul_eq (n : Nat) {x y : Real}
    (hxy : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    (((n : Real) * x : Real) : UnitAddCircle) =
      (((n : Real) * y : Real) : UnitAddCircle) := by
  have h := congrArg (fun z : UnitAddCircle => n • z) hxy
  simpa only [← AddCircle.coe_nsmul, nsmul_eq_mul] using h

private theorem finFraction_mem_Icc {n : Nat} (hn : 0 < n) (a : Fin n) :
    ((a.val : Real) / (n : Real)) ∈ Set.Icc (0 : Real) 1 := by
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (by positivity) hnReal.le
  · apply (div_le_iff₀ hnReal).2
    norm_num

private theorem alignedGridSum_le_sigmaOne_mul_squaredBlock
    (digit : Fin 10) {length k e v E : Nat} {x y : Real}
    (hblocks : k + 2 * v + e ≤ length)
    (hxy : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    alignedGridSum digit length (E : Real) x ≤
      decimalHybridSigmaOneAt digit length k e v E x *
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k (y + gamma) *
              normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                (((10 ^ k : Nat) : Real) * (y + gamma)))
          ((E : Real) / ((10 ^ length : Nat) : Real)) 0 := by
  classical
  let Y : Real := ((10 ^ length : Nat) : Real)
  let D : Real := ((10 ^ k : Nat) : Real)
  let S : Real := (((10 ^ k) * (10 ^ v) ^ 2 : Nat) : Real)
  let delta : Real := (E : Real) / Y
  let G : Real → Real := fun gamma =>
    normalizedPaddedDigitFourierMagnitudeAt digit k (y + gamma) *
      normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
        (D * (y + gamma))
  let M : Real := closedWindowMaximum G delta 0
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hdelta : 0 ≤ delta := div_nonneg (by positivity) hY.le
  have hG : Continuous G := by
    exact
      (normalizedPaddedDigitFourierMagnitudeAt_continuous digit k).comp
          (continuous_const.add continuous_id) |>.mul <|
        (normalizedPaddedDigitFourierMagnitudeAt_continuous digit (2 * v)).comp
          (continuous_const.mul (continuous_const.add continuous_id))
  change (∑ b ∈ alignedGridWindow length (E : Real) x,
      normalizedPaddedDigitFourierMagnitudeAt digit length
        ((b : Real) / Y)) ≤
    (∑ b ∈ alignedGridWindow length (E : Real) x,
      normalizedPaddedDigitFourierMagnitudeAt digit e
        (S * ((b : Real) / Y))) * M
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b hb
  let theta : Real := (b : Real) / Y
  let gamma : Real := theta - x
  have hwindow := (mem_alignedGridWindow_iff.mp hb).2.2
  have hgamma : gamma ∈ Set.Icc (-delta) delta := by
    have habs : |gamma| ≤ delta := by
      simpa only [gamma, theta, Y, delta] using hwindow
    exact (abs_le.mp habs)
  have htheta : theta = x + gamma := by dsimp [gamma]; ring
  have hphase : (theta : UnitAddCircle) = ((y + gamma : Real) : UnitAddCircle) := by
    calc
      (theta : UnitAddCircle) = ((x + gamma : Real) : UnitAddCircle) := by
        exact congrArg (fun z : Real => (z : UnitAddCircle)) htheta
      _ = ((y + gamma : Real) : UnitAddCircle) := by
        have hadd := congrArg
          (fun z : UnitAddCircle => z + (gamma : UnitAddCircle)) hxy
        simpa only [AddCircle.coe_add] using hadd
  have hfirst :
      normalizedPaddedDigitFourierMagnitudeAt digit k theta =
        normalizedPaddedDigitFourierMagnitudeAt digit k (y + gamma) :=
    periodic_eq_of_unitAddCircle_eq
      (normalizedPaddedDigitFourierMagnitudeAt_periodic digit k) hphase
  have hmiddlePhase :
      ((D * theta : Real) : UnitAddCircle) =
        ((D * (y + gamma) : Real) : UnitAddCircle) := by
    simpa only [D] using unitAddCircle_nat_mul_eq (10 ^ k) hphase
  have hmiddle :
      normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) (D * theta) =
        normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
          (D * (y + gamma)) :=
    periodic_eq_of_unitAddCircle_eq
      (normalizedPaddedDigitFourierMagnitudeAt_periodic digit (2 * v))
      hmiddlePhase
  have hmaximum : G gamma ≤ M := by
    have hle := le_closedWindowMaximum hG hdelta 0 hgamma
    simpa only [zero_add, M] using hle
  have hfactor := normalizedPaddedDigitFourierMagnitudeAt_threeBlock
    digit (k + 2 * v + e) k (2 * v) e rfl theta
  have hblock :
      normalizedPaddedDigitFourierMagnitudeAt digit length theta ≤
        normalizedPaddedDigitFourierMagnitudeAt digit k theta *
          normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) (D * theta) *
            normalizedPaddedDigitFourierMagnitudeAt digit e (S * theta) := by
    calc
      _ ≤ normalizedPaddedDigitFourierMagnitudeAt digit (k + 2 * v + e)
          theta :=
        normalizedPaddedDigitFourierMagnitudeAt_le_prefix digit hblocks theta
      _ = _ := by
        simpa only [D, S, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          pow_add, pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using hfactor
  calc
    normalizedPaddedDigitFourierMagnitudeAt digit length theta ≤
        normalizedPaddedDigitFourierMagnitudeAt digit k theta *
          normalizedPaddedDigitFourierMagnitudeAt digit (2 * v) (D * theta) *
            normalizedPaddedDigitFourierMagnitudeAt digit e (S * theta) := hblock
    _ = normalizedPaddedDigitFourierMagnitudeAt digit e (S * theta) *
        G gamma := by rw [hfirst, hmiddle]; ring
    _ ≤ normalizedPaddedDigitFourierMagnitudeAt digit e (S * theta) * M :=
      mul_le_mul_of_nonneg_left hmaximum
        (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit e _)

private theorem sum_hybridMixedRadixReducedTriple_eq_fullCarrier
    {M : Type*} [AddCommMonoid M] (d₁ d₂ d₃ : Nat)
    (f : ((Fin d₁ × Fin d₂) × Fin d₃) → M) :
    (∑ b : HybridMixedRadixReducedTriple d₁ d₂ d₃, f b.val) =
      ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃, f b := by
  exact (Finset.sum_subtype (hybridFullReducedCarrier d₁ d₂ d₃)
    (fun b => by simp [hybridFullReducedCarrier]) f).symm

/-- Extract a uniform `Sigma1` bound from the exact ZC-reindexed aligned
source sum, retaining the unsplit squared-block source factor. -/
theorem decimalHybridAlignedSourceBandSum_le_mul_squaredBlockSourceBandSum
    (digit : Fin 10) {length q₁ d k e v u Q₂ E : Nat}
    (hblocks : k + 2 * v + e ≤ length)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq₁10 : q₁.Coprime 10) {K : Real}
    (hSigma : ∀ x ∈ Set.Icc (0 : Real) 1,
      decimalHybridSigmaOneAt digit length k e v E x ≤ K) :
    decimalHybridAlignedSourceBandSum digit length q₁ d Q₂ E ≤
      K * decimalHybridSquaredBlockSourceBandSum digit q₁ d k v Q₂
        ((E : Real) / ((10 ^ length : Nat) : Real)) := by
  classical
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  let delta : Real := (E : Real) / ((10 ^ length : Nat) : Real)
  rw [decimalHybridAlignedSourceBandSum_eq_reindexed
    digit length q₁ d k v u Q₂ E hq₁ hd hdvd hq₁10]
  calc
    (∑ q₂ : {q₂ // q₂ ∈ hybridResidualSourceDenominators Q₂},
        ∑ a : ReducedResidue (q₁ * q₂.val),
          ∑ b : HybridMixedRadixReducedTriple d₁ d₂ d₃,
            alignedGridSum digit length (E : Real)
              (((decimalHybridFullSourceResidueEquiv
                (q := q₁ * q₂.val) (d := d) (k := k) (v := v) (u := u)
                (Nat.mul_pos hq₁
                  ((mem_hybridResidualSourceDenominators_iff.mp q₂.property).1))
                hd hdvd
                (hq₁10.mul_left
                  ((mem_hybridResidualSourceDenominators_iff.mp
                    q₂.property).2.2.2))
                (a, b)).val.val : Real) /
                ((((q₁ * q₂.val) * d : Nat) : Real)))) ≤
      ∑ q₂ : {q₂ // q₂ ∈ hybridResidualSourceDenominators Q₂},
        ∑ a : ReducedResidue (q₁ * q₂.val),
          ∑ b : HybridMixedRadixReducedTriple d₁ d₂ d₃,
            K * closedWindowMaximum
              (fun gamma =>
                normalizedPaddedDigitFourierMagnitudeAt digit k
                    (hybridSourceBetaTwo (q₁ * q₂.val) d₁ d₂ d₃ a b.val.1 +
                      (b.val.2.val : Real) / d₃ + gamma) *
                  normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                    (((10 ^ k : Nat) : Real) *
                      (hybridSourceBetaTwo (q₁ * q₂.val) d₁ d₂ d₃ a b.val.1 +
                        (b.val.2.val : Real) / d₃ + gamma)))
              delta 0 := by
        apply Finset.sum_le_sum
        intro q₂ hq₂
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        let q := q₁ * q₂.val
        have hq : 0 < q := Nat.mul_pos hq₁
          ((mem_hybridResidualSourceDenominators_iff.mp q₂.property).1)
        have hq10 : q.Coprime 10 := hq₁10.mul_left
          ((mem_hybridResidualSourceDenominators_iff.mp q₂.property).2.2.2)
        let c := decimalHybridFullSourceResidueEquiv
          (q := q) (d := d) (k := k) (v := v) (u := u)
          hq hd hdvd hq10 (a, b)
        let x : Real := (c.val.val : Real) / (((q * d : Nat) : Real))
        let y : Real := hybridSourceBetaTwo q d₁ d₂ d₃ a b.val.1 +
          (b.val.2.val : Real) / d₃
        have hx : x ∈ Set.Icc (0 : Real) 1 :=
          finFraction_mem_Icc (Nat.mul_pos hq hd) c.val
        have hcircle : (x : UnitAddCircle) = (y : UnitAddCircle) := by
          simpa only [q, x, y, d₁, d₂, d₃] using
            decimalHybridFullSourceResidue_unitAddCircle_eq
              hq hd hdvd hq10 a b
        have hpoint := alignedGridSum_le_sigmaOne_mul_squaredBlock
          digit (E := E) hblocks hcircle
        have hG : Continuous (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k (y + gamma) *
              normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                (((10 ^ k : Nat) : Real) * (y + gamma))) := by
          exact
            (normalizedPaddedDigitFourierMagnitudeAt_continuous digit k).comp
                (continuous_const.add continuous_id) |>.mul <|
              (normalizedPaddedDigitFourierMagnitudeAt_continuous digit (2 * v)).comp
                (continuous_const.mul (continuous_const.add continuous_id))
        have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
        have hmaximum : 0 ≤ closedWindowMaximum
            (fun gamma =>
              normalizedPaddedDigitFourierMagnitudeAt digit k (y + gamma) *
                normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                  (((10 ^ k : Nat) : Real) * (y + gamma))) delta 0 :=
          closedWindowMaximum_nonneg hG
            (fun gamma => mul_nonneg
              (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit k _)
              (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit (2 * v) _))
            hdelta 0
        have hfinal := hpoint.trans <|
          mul_le_mul_of_nonneg_right (hSigma x hx) hmaximum
        simpa only [q, x, y, c, d₁, d₂, d₃, delta] using hfinal
    _ = K * (∑ q₂ : {q₂ // q₂ ∈ hybridResidualSourceDenominators Q₂},
        ∑ a : ReducedResidue (q₁ * q₂.val),
          ∑ b : HybridMixedRadixReducedTriple d₁ d₂ d₃,
            closedWindowMaximum
              (fun gamma =>
                normalizedPaddedDigitFourierMagnitudeAt digit k
                    (hybridSourceBetaTwo (q₁ * q₂.val) d₁ d₂ d₃ a b.val.1 +
                      (b.val.2.val : Real) / d₃ + gamma) *
                  normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                    (((10 ^ k : Nat) : Real) *
                      (hybridSourceBetaTwo (q₁ * q₂.val) d₁ d₂ d₃ a b.val.1 +
                        (b.val.2.val : Real) / d₃ + gamma)))
              delta 0) := by
        simp_rw [Finset.mul_sum]
    _ = K * decimalHybridSquaredBlockSourceBandSum digit q₁ d k v Q₂
        delta := by
      congr 1
      unfold decimalHybridSquaredBlockSourceBandSum
      dsimp only
      rw [Finset.sum_subtype (hybridResidualSourceDenominators Q₂)
        (fun _ => Iff.rfl)]
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      apply Finset.sum_congr rfl
      intro a ha
      let f : ((Fin d₁ × Fin d₂) × Fin d₃) → Real := fun b =>
        closedWindowMaximum
          (fun gamma =>
            normalizedPaddedDigitFourierMagnitudeAt digit k
                (hybridSourceBetaTwo (q₁ * q₂.val) d₁ d₂ d₃ a b.1 +
                  (b.2.val : Real) / d₃ + gamma) *
              normalizedPaddedDigitFourierMagnitudeAt digit (2 * v)
                (((10 ^ k : Nat) : Real) *
                  (hybridSourceBetaTwo (q₁ * q₂.val) d₁ d₂ d₃ a b.1 +
                    (b.2.val : Real) / d₃ + gamma)))
          delta 0
      change (∑ b : HybridMixedRadixReducedTriple d₁ d₂ d₃, f b.val) =
        ∑ b ∈ hybridFullReducedCarrier d₁ d₂ d₃, f b
      exact sum_hybridMixedRadixReducedTriple_eq_fullCarrier d₁ d₂ d₃ f

/--
Insert the canonical auxiliary blocks and the uniform source-power bound into the
coefficient-one aligned-source factorization.
-/
theorem
    decimalHybridAlignedSourceBandSum_le_source_power_mul_squaredBlockSourceBandSum
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q₁ d u Q₂ : Nat}
    (hscale : dLength + eLength ≤ length + loss)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq₁10 : q₁.Coprime 10) :
    let dAux := decimalHybridAuxiliaryDLength length dLength
    let eAux := decimalHybridAuxiliaryELength length dLength eLength
    let v := decimalHybridSquareScaleLength length dAux eAux
    let C : Real := ((10 ^ loss : Nat) : Real)
    let E : Real := ((10 ^ eLength : Nat) : Real)
    decimalHybridAlignedSourceBandSum digit length q₁ d Q₂ (10 ^ eLength) ≤
      (20 * largeSieveSamplingConstant * (2 * C + 1) *
          E ^ largeSieveAlpha) *
        decimalHybridSquaredBlockSourceBandSum digit q₁ d dAux v Q₂
          (E / ((10 ^ length : Nat) : Real)) := by
  let dAux := decimalHybridAuxiliaryDLength length dLength
  let eAux := decimalHybridAuxiliaryELength length dLength eLength
  let v := decimalHybridSquareScaleLength length dAux eAux
  let C : Real := ((10 ^ loss : Nat) : Real)
  let E : Real := ((10 ^ eLength : Nat) : Real)
  have haux := decimalHybridAuxiliaryLengths_spec hscale
  change dAux ≤ dLength ∧ dLength ≤ dAux + loss ∧
    eAux ≤ eLength ∧ eLength ≤ eAux + loss ∧
      dAux + eAux ≤ length at haux
  have hblocks := (decimalHybridSquareScaleLength_spec haux.2.2.2.2).1
  change dAux + 2 * v + eAux ≤ length at hblocks
  apply decimalHybridAlignedSourceBandSum_le_mul_squaredBlockSourceBandSum
    digit hblocks hq₁ hd hdvd hq₁10
  intro x hx
  exact decimalHybridSigmaOneAt_le_source_power loss digit hscale x hx

end

end PrimesRestrictedDigits
