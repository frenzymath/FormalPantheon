import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceJointLedgerCore
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceCutoffLedger
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceProfileEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceFirstEndpointProfile
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceFixedSpliceWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceProfileShell

/-!
# Source joint endpoint ledger

This composes the transported boundary, first weighted sum, and strict pre-absorption second
sum under the explicit D-scaled reserve of Eq. (8.14). The seed-free profile shell and the
later induction use these sign-specific ledgers.
-/

namespace PrimesRestrictedDigits

theorem dimensionOneRosserPlusSourceJointLedger :
    exists S : Real, Real.exp 5000 + 1 <= S /\
      forall (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real},
        0 < c -> 1 <= D ->
          2 * (1 + K) + 2304 * c * K <= D ->
          (forall (r : Nat) {t : Real}, 1 <= t ->
            dimensionOneRosserModelPlusPartialSum r t <=
              c * dimensionOneDelayScaledPlus t) ->
          (forall (r : Nat) {t : Real}, 2 <= t ->
            dimensionOneRosserModelMinusPartialSum r t <
              c * dimensionOneDelayScaledMinus t) ->
          0 < R -> 0 <= K ->
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
          upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
                (level ^ (1 / s0)) R +
              dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
              D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
            sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
              (dimensionOneRosserModelPlusPartialSum R s -
                  dimensionOneRosserModelPlusPartialSum R s0 +
                D * (1 - 1 / (2 * s0)) *
                  dimensionOneRosserSourcePlusProfile (Real.log level) s) := by
  obtain ⟨S, hS, hboundaryAll⟩ :=
    exists_dimensionOneRosserFailurePartialSums_sourceNormalized_transport
  refine ⟨S, hS, ?_⟩
  intro P R c D K level z s s0 hc hD hDdom _hmodelPlus hmodelMinus hR hK
    hprime hlevel hz hs hsLower hss0 hcutoff hsTail hsource hLExp hgate
    hgrowth hsmall hRatio
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
  have hboundaryRaw := (hboundaryAll P R hprime hlevel hz hs
    (by linarith : 2 <= s) hss0 hcutoff hsTail hLExp hsource hRatio).1
  have hboundary :
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
            (level ^ (1 / s0)) R <
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
          (Real.log level) ^ (-1 / 3 : Real) *
          (((2 * (1 + K) / s0) *
              (Real.log level) ^ (-1 / 24 : Real)) *
            dimensionOneRosserPlusArtificialAux
              (Real.log level) 0 s) := by
    have hboundaryRaw' :
        upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
              (level ^ (1 / s0)) R <
          (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
            (Real.log level) ^ (-1 / 3 : Real) *
            ((((1 + K * s0 / Real.log level) / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserPlusArtificialAux
                (Real.log level) 0 s0) := by
      simpa only [dimensionOneRosserPlusArtificialAux, mul_assoc] using
        hboundaryRaw
    exact hboundaryRaw'.trans_le
      (mul_le_mul_of_nonneg_left hboundaryProfile
        (mul_nonneg hscale.le hdecay))
  have hfirstRaw := dimensionOneRosserPlusFirstPrimeSum_le_of_ratio
    P R hR hK hprime hlevel hz hs hsLower hss0 hcutoff hRatio
  have hmodelShift := (hmodelMinus R (by linarith : 2 <= s - 1)).le
  have hfirstEndpoint :=
    dimensionOneRosserPlusFirstModelEndpoint_le_source_profile R hc.le hK
      hsLower hss0 hsource hLExp hgate hmodelShift
  have hfirstEndpoint' :
      (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
          dimensionOneRosserModelMinusPartialSum R (s - 1) <=
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
      dimensionOneRosserModelPlusPartialSum R s -
            dimensionOneRosserModelPlusPartialSum R s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelMinusPartialSum R (s - 1) <=
        dimensionOneRosserModelPlusPartialSum R s -
            dimensionOneRosserModelPlusPartialSum R s0 +
          (Real.log level) ^ (-1 / 3 : Real) *
            (((2304 * c * K / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserPlusArtificialAux
                (Real.log level) 0 s) := by linarith
  have hfirst : dimensionOneRosserPlusFirstPrimeSum P level s0 z R <=
      (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
        (dimensionOneRosserModelPlusPartialSum R s -
            dimensionOneRosserModelPlusPartialSum R s0 +
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
    hdecay hprofile (zero_le_one.trans hD) hboundary hfirst hsecond hbudget
  simpa only [dimensionOneRosserSourcePlusProfile, mul_assoc] using hledger

theorem dimensionOneRosserMinusSourceJointLedger :
    exists S : Real, Real.exp 5000 + 1 <= S /\
      forall (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real},
        0 < c -> 1 <= D ->
          2 * (1 + K) + 2304 * c * K <= D ->
          (forall (r : Nat) {t : Real}, 1 <= t ->
            dimensionOneRosserModelPlusPartialSum r t <=
              c * dimensionOneDelayScaledPlus t) ->
          (forall (r : Nat) {t : Real}, 2 <= t ->
            dimensionOneRosserModelMinusPartialSum r t <
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
          lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
                (level ^ (1 / s0)) (R + 1) +
              dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
              D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
            sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
              (dimensionOneRosserModelMinusPartialSum (R + 1) s -
                  dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
                D * (1 - 1 / (2 * s0)) *
                  dimensionOneRosserSourceMinusProfile (Real.log level) s) := by
  obtain ⟨S, hS, hboundaryAll⟩ :=
    exists_dimensionOneRosserFailurePartialSums_sourceNormalized_transport
  refine ⟨S, hS, ?_⟩
  intro P R c D K level z s s0 hc hD hDdom hmodelPlus _hmodelMinus hK
    hprime hlevel hz hs hsLower hss0 hcutoff hsTail hsource hLExp hgate
    hgrowth hsmall hRatio
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
  have hboundaryRaw := (hboundaryAll P (R + 1) hprime hlevel hz hs hsLower
    hss0 hcutoff hsTail hLExp hsource hRatio).2
  have hboundary :
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
            (level ^ (1 / s0)) (R + 1) <
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
          (Real.log level) ^ (-1 / 3 : Real) *
          (((2 * (1 + K) / s0) *
              (Real.log level) ^ (-1 / 24 : Real)) *
            dimensionOneRosserMinusArtificialAux
              (Real.log level) 0 s) := by
    have hboundaryRaw' :
        lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
              (level ^ (1 / s0)) (R + 1) <
          (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
            (Real.log level) ^ (-1 / 3 : Real) *
            ((((1 + K * s0 / Real.log level) / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserMinusArtificialAux
                (Real.log level) 0 s0) := by
      simpa only [dimensionOneRosserMinusArtificialAux, mul_assoc] using
        hboundaryRaw
    exact hboundaryRaw'.trans_le
      (mul_le_mul_of_nonneg_left hboundaryProfile
        (mul_nonneg hscale.le hdecay))
  have hfirstRaw := dimensionOneRosserMinusFirstPrimeSum_le_of_ratio
    P R hK hprime hlevel hz hs hsLower hss0 hcutoff hRatio
  have hmodelShift := hmodelPlus R (by linarith : 1 <= s - 1)
  have hfirstEndpoint :=
    dimensionOneRosserMinusFirstModelEndpoint_le_source_profile R hc.le hK
      hsLower hss0 hsource hLExp hgate hmodelShift
  have hfirstEndpoint' :
      (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
          dimensionOneRosserModelPlusPartialSum R (s - 1) <=
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
      dimensionOneRosserModelMinusPartialSum (R + 1) s -
            dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelPlusPartialSum R (s - 1) <=
        dimensionOneRosserModelMinusPartialSum (R + 1) s -
            dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
          (Real.log level) ^ (-1 / 3 : Real) *
            (((2304 * c * K / s0) *
                (Real.log level) ^ (-1 / 24 : Real)) *
              dimensionOneRosserMinusArtificialAux
                (Real.log level) 0 s) := by linarith
  have hfirst : dimensionOneRosserMinusFirstPrimeSum P level s0 z R <=
      (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
        (dimensionOneRosserModelMinusPartialSum (R + 1) s -
            dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
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
    hdecay hprofile (zero_le_one.trans hD) hboundary hfirst hsecond hbudget
  simpa only [dimensionOneRosserSourceMinusProfile, mul_assoc] using hledger

end PrimesRestrictedDigits
