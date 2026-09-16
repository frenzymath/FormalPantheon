import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceJointLedger
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserRawFirstWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFullSourceBase
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelRawClosedComparison

/-!
# Rank-free raw full-source ledger

This is the retained-cutoff analogue of the joint ledger. The W4 normalized boundary is
saturated at the local filtered-carrier length, while the first and model terms use their raw
(infinite-rank) forms. The ledger stops at the retained cutoff and makes no outer-cube claim.
-/

namespace PrimesRestrictedDigits

theorem dimensionOneRosserPlusRawFullSourceLedger :
    exists S : Real, Real.exp 5000 + 1 <= S /\
      forall (P : Finset Nat) {c D K level z s s0 : Real},
        0 < c -> 1 <= D ->
          2 * (1 + K) + 2304 * c * K <= D ->
          (forall {t : Real}, 1 <= t ->
            dimensionOneRosserModelPlusRaw t <=
              c * dimensionOneDelayScaledPlus t) ->
          (forall {t : Real}, 2 <= t ->
            dimensionOneRosserModelMinusRaw t <=
              c * dimensionOneDelayScaledMinus t) ->
          0 <= K ->
          (forall p, p ∈ P -> p.Prime) ->
          2 <= level -> 2 <= z ->
          s = Real.log level / Real.log z -> 3 <= s -> s < s0 ->
          2 <= level ^ (1 / s0) -> S <= s0 ->
          s0 ^ 50 = Real.log level * (Real.log (Real.log level)) ^ 3 ->
          Real.exp 1 <= Real.log level ->
          124800 + 14400 * Real.log (Real.log (Real.log level)) <=
            Real.log (Real.log level) ->
          dimensionOneRosserSecondLevelThreshold <= Real.log level ->
          6 * (1 + 2304 * K) <=
            (Real.log level) ^ (1 / 24 : Real) ->
          (forall u : Real,
            level ^ (1 / s0) <= u -> u < z ->
            sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
                sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
              (Real.log z / Real.log u) * (1 + K / Real.log u)) ->
          upperRosserFailureSum P (fun p => (p : Real)⁻¹) level
                (level ^ (1 / s0)) +
              dimensionOneRosserPlusRawFirstPrimeSum P level s0 z +
              D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
            sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
              (dimensionOneRosserModelPlusRaw s -
                  dimensionOneRosserModelPlusRaw s0 +
                D * (1 - 1 / (2 * s0)) *
                  dimensionOneRosserSourcePlusProfile (Real.log level) s) := by
  obtain ⟨S, hS, hboundaryAll⟩ :=
    exists_dimensionOneRosserFailurePartialSums_sourceNormalized_transport
  refine ⟨S, hS, ?_⟩
  intro P c D K level z s s0 hc hD hDdom hmodelPlus hmodelMinus hK
    hprime hlevel hz hs hsLower hss0 hcutoff hsTail hsource hLExp hgate
    hgrowth hsmall hRatio
  let R : Nat := (sieveFactorsBelow P (level ^ (1 / s0))).length
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hs0One : 1 <= s0 := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hLOne : 1 <= Real.log level :=
    (Real.one_le_exp (by norm_num : (0 : Real) <= 1)).trans hLExp
  have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_pos hV hsPos
  have hdecay : 0 <= (Real.log level) ^ (-1 / 3 : Real) :=
    (Real.rpow_pos_of_pos hL _).le
  have hprofile : 0 <= dimensionOneRosserPlusArtificialAux
      (Real.log level) 0 s :=
    (dimensionOneRosserPlusArtificialAux_pos hL hsPos).le
  have hs0L := dimensionOneRosserSourceCutoff_s0_le_log hs0One hsource
    hLExp hgate
  have hprofileEndpoint :=
    dimensionOneRosserPlusArtificialAux_sourceEndpoint_le_two hsLower hss0
      hsource hLExp hgate hgrowth
  have hboundaryProfile := dimensionOneRosserSourceBoundaryProfile_le hK hL
    hs0Pos hs0L hprofileEndpoint hprofile
  have hboundary := (hboundaryAll P R hprime hlevel hz hs
    (by linarith : 2 <= s) hss0 hcutoff hsTail hLExp hsource hRatio).1
  rw [upperRosserFailurePartialSum_eq_full_of_rankCount_le
    P (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) R (by
      dsimp [R]
      omega)] at hboundary
  have hboundary' :
      upperRosserFailureSum P (fun p => (p : Real)⁻¹) level
            (level ^ (1 / s0)) <
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
          (Real.log level) ^ (-1 / 3 : Real) *
          (((2 * (1 + K) / s0) *
              (Real.log level) ^ (-1 / 24 : Real)) *
            dimensionOneRosserPlusArtificialAux
              (Real.log level) 0 s) := by
    have hraw :
        upperRosserFailureSum P (fun p => (p : Real)⁻¹) level
              (level ^ (1 / s0)) <
          (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
            (Real.log level) ^ (-1 / 3 : Real) *
            ((((1 + K * s0 / Real.log level) / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserPlusArtificialAux
                (Real.log level) 0 s0) := hboundary
    exact hraw.trans_le
      (mul_le_mul_of_nonneg_left hboundaryProfile
        (mul_nonneg hscale.le hdecay))
  have hfirstRaw := dimensionOneRosserPlusRawFirstPrimeSum_le_of_ratio
    P hK hprime hlevel hz hs hsLower hss0 hcutoff hRatio
  have hmodelShift := hmodelMinus (by linarith : 2 <= s - 1)
  have hfirstEndpoint :=
    dimensionOneRosserSourceFirstModelEndpoint_le_profile
      (c := c) (K := K) (L := Real.log level) (s := s) (s0 := s0)
      (model := dimensionOneRosserModelMinusRaw (s - 1))
      (shifted := dimensionOneDelayScaledMinus (s - 1))
      (current := dimensionOneDelayScaledPlus s)
      (A := dimensionOneRosserArtificialFactor (Real.log level) 0 s)
      hc.le hK (by linarith : 2 <= s) hss0 hsource hLExp hgate hmodelShift
      (dimensionOneDelayScaledMinus_shift_le_plus (by linarith))
      (dimensionOneDelayScaledPlus_pos (by linarith)).le
      (one_le_dimensionOneRosserArtificialFactor_zero
        ((Real.exp_pos 1).trans_le hLExp) (by linarith))
  have hfirstEndpoint' :
      (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
          dimensionOneRosserModelMinusRaw (s - 1) <=
        (Real.log level) ^ (-1 / 3 : Real) *
          (((2304 * c * K / s0) *
              (Real.log level) ^ (-1 / 24 : Real)) *
            dimensionOneRosserPlusArtificialAux
              (Real.log level) 0 s) := by
    calc
      _ <= (2304 * c * K / s0) *
          (Real.log level) ^ (-1 / 24 : Real) *
          (dimensionOneRosserArtificialFactor (Real.log level) 0 s *
            dimensionOneDelayScaledPlus s *
              (Real.log level) ^ (-1 / 3 : Real)) := hfirstEndpoint
      _ = _ := by
        unfold dimensionOneRosserPlusArtificialAux
        ring
  have hfirstInside :
      dimensionOneRosserModelPlusRaw s - dimensionOneRosserModelPlusRaw s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelMinusRaw (s - 1) <=
        dimensionOneRosserModelPlusRaw s - dimensionOneRosserModelPlusRaw s0 +
          (Real.log level) ^ (-1 / 3 : Real) *
            (((2304 * c * K / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserPlusArtificialAux
                (Real.log level) 0 s) := by linarith
  have hfirst : dimensionOneRosserPlusRawFirstPrimeSum P level s0 z <=
      (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
        (dimensionOneRosserModelPlusRaw s -
            dimensionOneRosserModelPlusRaw s0 +
          (Real.log level) ^ (-1 / 3 : Real) *
            (((2304 * c * K / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserPlusArtificialAux
                (Real.log level) 0 s)) :=
    hfirstRaw.trans (mul_le_mul_of_nonneg_left hfirstInside hscale.le)
  have hArtificial :
      (1 + s ^ 50 / Real.log level) ^ s =
        dimensionOneRosserArtificialFactor (Real.log level) 0 s := by
    symm
    rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
    unfold dimensionOneRosserArtificialBase
    norm_num
  have hraw := dimensionOneRosserPlusSecondRawPrimeSum_le_relaxed_of_two_le
    P hprime hlevel hz hs (by linarith : 2 <= s) hcutoff
  have hrelaxed :=
    dimensionOneRosserSourcePlusSecondRelaxedPrimeSum_lt_fixedSplice
      P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp hgate
        hgrowth hRatio
  have hsecondEndpoint := dimensionOneRosserPlusSecondEndpoint_le_sourceCutoff
    hK hLExp (by linarith : 2 <= s) hss0 hsource hgate
  rw [hArtificial] at hrelaxed hsecondEndpoint
  have hrelaxed' :
      dimensionOneRosserPlusSecondRelaxedPrimeSum P level s0 z <
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
          (Real.log level) ^ (-1 / 3 : Real) *
          ((1 - 1 / s0) ^ (2 / 3 : Real) *
              dimensionOneRosserPlusArtificialAux (Real.log level) 0 s +
            (2 * K * s0 / Real.log level) *
              dimensionOneRosserPlusSecondKernel (Real.log level) s) := by
    simpa only [dimensionOneRosserPlusArtificialAux, mul_assoc] using hrelaxed
  have hsecondEndpoint' :
      (2 * K * s0 / Real.log level) *
          dimensionOneRosserPlusSecondKernel (Real.log level) s <=
        ((2304 * K / s0) *
            (Real.log level) ^ (-1 / 24 : Real)) *
          dimensionOneRosserPlusArtificialAux (Real.log level) 0 s := by
    simpa only [dimensionOneRosserPlusArtificialAux, mul_assoc] using
      hsecondEndpoint
  have hsecond := dimensionOneRosserSourceSecondProfile_lt hscale.le hdecay
    hraw hrelaxed' hsecondEndpoint'
  have hbudget := dimensionOneRosserSourceJointScalarBudget hc.le hD hK
    hLOne hs0One hDdom hsmall
  have hledger := dimensionOneRosserSourceJointLedger_of_estimates hscale
    hdecay hprofile (zero_le_one.trans hD) hboundary' hfirst hsecond hbudget
  simpa only [dimensionOneRosserSourcePlusProfile, mul_assoc] using hledger

theorem dimensionOneRosserMinusRawFullSourceLedger :
    exists S : Real, Real.exp 5000 + 1 <= S /\
      forall (P : Finset Nat) {c D K level z s s0 : Real},
        0 < c -> 1 <= D ->
          2 * (1 + K) + 2304 * c * K <= D ->
          (forall {t : Real}, 1 <= t ->
            dimensionOneRosserModelPlusRaw t <=
              c * dimensionOneDelayScaledPlus t) ->
          (forall {t : Real}, 2 <= t ->
            dimensionOneRosserModelMinusRaw t <=
              c * dimensionOneDelayScaledMinus t) ->
          0 <= K ->
          (forall p, p ∈ P -> p.Prime) ->
          2 <= level -> 2 <= z ->
          s = Real.log level / Real.log z -> 2 <= s -> s < s0 ->
          2 <= level ^ (1 / s0) -> S <= s0 ->
          s0 ^ 50 = Real.log level * (Real.log (Real.log level)) ^ 3 ->
          Real.exp 1 <= Real.log level ->
          124800 + 14400 * Real.log (Real.log (Real.log level)) <=
            Real.log (Real.log level) ->
          dimensionOneRosserSecondLevelThreshold <= Real.log level ->
          6 * (1 + 2304 * K) <=
            (Real.log level) ^ (1 / 24 : Real) ->
          (forall u : Real,
            level ^ (1 / s0) <= u -> u < z ->
            sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
                sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
              (Real.log z / Real.log u) * (1 + K / Real.log u)) ->
          lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level
                (level ^ (1 / s0)) +
              dimensionOneRosserMinusRawFirstPrimeSum P level s0 z +
              D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
            sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
              (dimensionOneRosserModelMinusRaw s -
                  dimensionOneRosserModelMinusRaw s0 +
                D * (1 - 1 / (2 * s0)) *
                  dimensionOneRosserSourceMinusProfile (Real.log level) s) := by
  obtain ⟨S, hS, hboundaryAll⟩ :=
    exists_dimensionOneRosserFailurePartialSums_sourceNormalized_transport
  refine ⟨S, hS, ?_⟩
  intro P c D K level z s s0 hc hD hDdom hmodelPlus hmodelMinus hK
    hprime hlevel hz hs hsLower hss0 hcutoff hsTail hsource hLExp hgate
    hgrowth hsmall hRatio
  let R : Nat := (sieveFactorsBelow P (level ^ (1 / s0))).length
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hs0One : 1 <= s0 := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hLOne : 1 <= Real.log level :=
    (Real.one_le_exp (by norm_num : (0 : Real) <= 1)).trans hLExp
  have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hscale : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_pos hV hsPos
  have hdecay : 0 <= (Real.log level) ^ (-1 / 3 : Real) :=
    (Real.rpow_pos_of_pos hL _).le
  have hprofile : 0 <= dimensionOneRosserMinusArtificialAux
      (Real.log level) 0 s :=
    (dimensionOneRosserMinusArtificialAux_pos hL hsPos).le
  have hs0L := dimensionOneRosserSourceCutoff_s0_le_log hs0One hsource
    hLExp hgate
  have hprofileEndpoint :=
    dimensionOneRosserMinusArtificialAux_sourceEndpoint_le_two hsLower hss0
      hsource hLExp hgate hgrowth
  have hboundaryProfile := dimensionOneRosserSourceBoundaryProfile_le hK hL
    hs0Pos hs0L hprofileEndpoint hprofile
  have hboundary := (hboundaryAll P R hprime hlevel hz hs hsLower hss0
    hcutoff hsTail hLExp hsource hRatio).2
  rw [lowerRosserFailurePartialSum_eq_full_of_rankCount_le
    P (fun p => (p : Real)⁻¹) level (level ^ (1 / s0)) R (by
      dsimp [R]
      omega)] at hboundary
  have hboundary' :
      lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level
            (level ^ (1 / s0)) <
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
          (Real.log level) ^ (-1 / 3 : Real) *
          (((2 * (1 + K) / s0) *
              (Real.log level) ^ (-1 / 24 : Real)) *
            dimensionOneRosserMinusArtificialAux
              (Real.log level) 0 s) := by
    have hraw :
        lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level
              (level ^ (1 / s0)) <
          (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
            (Real.log level) ^ (-1 / 3 : Real) *
            ((((1 + K * s0 / Real.log level) / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserMinusArtificialAux
                (Real.log level) 0 s0) := hboundary
    exact hraw.trans_le
      (mul_le_mul_of_nonneg_left hboundaryProfile
        (mul_nonneg hscale.le hdecay))
  have hfirstRaw := dimensionOneRosserMinusRawFirstPrimeSum_le_of_ratio
    P hK hprime hlevel hz hs hsLower hss0 hcutoff hRatio
  have hmodelShift := hmodelPlus (by linarith : 1 <= s - 1)
  have hfirstEndpoint :=
    dimensionOneRosserSourceFirstModelEndpoint_le_profile
      (c := c) (K := K) (L := Real.log level) (s := s) (s0 := s0)
      (model := dimensionOneRosserModelPlusRaw (s - 1))
      (shifted := dimensionOneDelayScaledPlus (s - 1))
      (current := dimensionOneDelayScaledMinus s)
      (A := dimensionOneRosserArtificialFactor (Real.log level) 0 s)
      hc.le hK hsLower hss0 hsource hLExp hgate hmodelShift
      (dimensionOneDelayScaledPlus_shift_le_minus hsLower)
      (dimensionOneDelayScaledMinus_pos (by linarith)).le
      (one_le_dimensionOneRosserArtificialFactor_zero
        ((Real.exp_pos 1).trans_le hLExp) (by linarith))
  have hfirstEndpoint' :
      (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
          dimensionOneRosserModelPlusRaw (s - 1) <=
        (Real.log level) ^ (-1 / 3 : Real) *
          (((2304 * c * K / s0) *
              (Real.log level) ^ (-1 / 24 : Real)) *
            dimensionOneRosserMinusArtificialAux
              (Real.log level) 0 s) := by
    calc
      _ <= (2304 * c * K / s0) *
          (Real.log level) ^ (-1 / 24 : Real) *
          (dimensionOneRosserArtificialFactor (Real.log level) 0 s *
            dimensionOneDelayScaledMinus s *
              (Real.log level) ^ (-1 / 3 : Real)) := hfirstEndpoint
      _ = _ := by
        unfold dimensionOneRosserMinusArtificialAux
        ring
  have hfirstInside :
      dimensionOneRosserModelMinusRaw s - dimensionOneRosserModelMinusRaw s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelPlusRaw (s - 1) <=
        dimensionOneRosserModelMinusRaw s - dimensionOneRosserModelMinusRaw s0 +
          (Real.log level) ^ (-1 / 3 : Real) *
            (((2304 * c * K / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserMinusArtificialAux
                (Real.log level) 0 s) := by linarith
  have hfirst : dimensionOneRosserMinusRawFirstPrimeSum P level s0 z <=
      (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
        (dimensionOneRosserModelMinusRaw s -
            dimensionOneRosserModelMinusRaw s0 +
          (Real.log level) ^ (-1 / 3 : Real) *
            (((2304 * c * K / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserMinusArtificialAux
                (Real.log level) 0 s)) :=
    hfirstRaw.trans (mul_le_mul_of_nonneg_left hfirstInside hscale.le)
  have hArtificial :
      (1 + s ^ 50 / Real.log level) ^ s =
        dimensionOneRosserArtificialFactor (Real.log level) 0 s := by
    symm
    rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
    unfold dimensionOneRosserArtificialBase
    norm_num
  have hraw := dimensionOneRosserMinusSecondRawPrimeSum_le_relaxed_of_two_le
    P hprime hlevel hz hs hsLower hcutoff
  have hrelaxed :=
    dimensionOneRosserSourceMinusSecondRelaxedPrimeSum_lt_fixedSplice
      P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp hgate
        hgrowth hRatio
  have hsecondEndpoint := dimensionOneRosserMinusSecondEndpoint_le_sourceCutoff
    hK hLExp hsLower hss0 hsource hgate
  rw [hArtificial] at hrelaxed hsecondEndpoint
  have hrelaxed' :
      dimensionOneRosserMinusSecondRelaxedPrimeSum P level s0 z <
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
          (Real.log level) ^ (-1 / 3 : Real) *
          ((1 - 1 / s0) ^ (2 / 3 : Real) *
              dimensionOneRosserMinusArtificialAux (Real.log level) 0 s +
            (2 * K * s0 / Real.log level) *
              dimensionOneRosserMinusSecondKernel (Real.log level) s) := by
    simpa only [dimensionOneRosserMinusArtificialAux, mul_assoc] using hrelaxed
  have hsecondEndpoint' :
      (2 * K * s0 / Real.log level) *
          dimensionOneRosserMinusSecondKernel (Real.log level) s <=
        ((2304 * K / s0) *
            (Real.log level) ^ (-1 / 24 : Real)) *
          dimensionOneRosserMinusArtificialAux (Real.log level) 0 s := by
    simpa only [dimensionOneRosserMinusArtificialAux, mul_assoc] using
      hsecondEndpoint
  have hsecond := dimensionOneRosserSourceSecondProfile_lt hscale.le hdecay
    hraw hrelaxed' hsecondEndpoint'
  have hbudget := dimensionOneRosserSourceJointScalarBudget hc.le hD hK
    hLOne hs0One hDdom hsmall
  have hledger := dimensionOneRosserSourceJointLedger_of_estimates hscale
    hdecay hprofile (zero_le_one.trans hD) hboundary' hfirst hsecond hbudget
  simpa only [dimensionOneRosserSourceMinusProfile, mul_assoc] using hledger

end PrimesRestrictedDigits
