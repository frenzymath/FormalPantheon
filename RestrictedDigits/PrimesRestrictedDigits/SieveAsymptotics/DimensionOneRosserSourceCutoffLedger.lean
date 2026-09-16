import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceNormalizedHighSeed
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceFixedSpliceAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFirstWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondRawPrimeSum

/-!
# Source-cutoff boundary transport and the three-term ledger

This module exposes the recurrence-facing part of Iwaniec's Section 8 assembly. It
deliberately stops before the seed-prime sum and before the joint endpoint reserve of Eq.
(8.14).
-/

namespace PrimesRestrictedDigits

private theorem sourceNormalizedBoundary_transport
    (P : Finset Nat) {K level z s s0 failure profile : Real}
    (hfailure : failure <
      sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (level ^ (1 / s0)) / s0 ^ 2 *
        (profile * (Real.log level) ^ (-3 / 8 : Real)))
    (hprofile : 0 <= profile)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0)
    (hRatio : ∀ u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) *
          (1 + K / Real.log u)) :
    failure <
      (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (Real.log level) ^ (-1 / 3 : Real)) *
        (((1 + K * s0 / Real.log level) / s0) *
          (Real.log level) ^ (-1 / 24 : Real) * profile) := by
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hlevelPos : 0 < level := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hzLog : 0 < Real.log z := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun q => (q : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hwz : level ^ (1 / s0) < z :=
    dimensionOneRosserFirstCutoff_lt hlevel hz hs hss0 hsLower
  have hratioW := hRatio (level ^ (1 / s0)) le_rfl hwz
  have hlogw : Real.log (level ^ (1 / s0)) =
      Real.log level / s0 := log_rpow_one_div hlevelPos
  have hlogz : Real.log z = Real.log level / s := by
    rw [hs]
    field_simp [hL.ne', hzLog.ne']
  have hratioExact :
      Real.log z / Real.log (level ^ (1 / s0)) *
          (1 + K / Real.log (level ^ (1 / s0))) =
        s0 / s * (1 + K * s0 / Real.log level) := by
    rw [hlogw, hlogz]
    field_simp [hL.ne', hsPos.ne', hs0Pos.ne']
  rw [hratioExact] at hratioW
  have hVbound : sieveDensityBelow P (fun q => (q : Real)⁻¹)
        (level ^ (1 / s0)) <=
      sieveDensityBelow P (fun q => (q : Real)⁻¹) z *
        (s0 / s * (1 + K * s0 / Real.log level)) := by
    have hratioMul := mul_le_mul_of_nonneg_left hratioW hV.le
    calc
      _ = sieveDensityBelow P (fun q => (q : Real)⁻¹) z *
          (sieveDensityBelow P (fun q => (q : Real)⁻¹)
            (level ^ (1 / s0)) /
            sieveDensityBelow P (fun q => (q : Real)⁻¹) z) := by
        field_simp [hV.ne']
      _ <= _ := hratioMul
  have hpower :
      (Real.log level) ^ (-3 / 8 : Real) =
        (Real.log level) ^ (-1 / 3 : Real) *
          (Real.log level) ^ (-1 / 24 : Real) := by
    rw [<- Real.rpow_add hL]
    congr 1
    ring
  have hmult : 0 <=
      (profile * (Real.log level) ^ (-3 / 8 : Real)) / s0 ^ 2 := by
    positivity
  have htransport := mul_le_mul_of_nonneg_right hVbound hmult
  apply hfailure.trans_le
  calc
    sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (level ^ (1 / s0)) / s0 ^ 2 *
        (profile * (Real.log level) ^ (-3 / 8 : Real)) =
      sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (level ^ (1 / s0)) *
        ((profile * (Real.log level) ^ (-3 / 8 : Real)) / s0 ^ 2) := by
      ring
    _ <= (sieveDensityBelow P (fun q => (q : Real)⁻¹) z *
          (s0 / s * (1 + K * s0 / Real.log level))) *
        ((profile * (Real.log level) ^ (-3 / 8 : Real)) / s0 ^ 2) :=
      htransport
    _ = _ := by
      rw [hpower]
      field_simp [hL.ne', hsPos.ne', hs0Pos.ne']

/- Transport the W4 boundary to the outer density used by the recurrence. -/
theorem exists_dimensionOneRosserFailurePartialSums_sourceNormalized_transport :
    ∃ S : Real, Real.exp 5000 + 1 <= S ∧
      ∀ (P : Finset Nat) (R : Nat) {K level z s s0 : Real},
        (∀ p ∈ P, p.Prime) ->
          2 <= level -> 2 <= z ->
            s = Real.log level / Real.log z -> 2 <= s -> s < s0 ->
              2 <= level ^ (1 / s0) -> S <= s0 ->
                Real.exp 1 <= Real.log level ->
                  s0 ^ 50 = Real.log level *
                    (Real.log (Real.log level)) ^ 3 ->
                    (∀ u : Real,
                      level ^ (1 / s0) <= u -> u < z ->
                      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
                          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
                        (Real.log z / Real.log u) *
                          (1 + K / Real.log u)) ->
                      upperRosserFailurePartialSum P
                          (fun p => (p : Real)⁻¹) level
                          (level ^ (1 / s0)) R <
                        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
                            (Real.log level) ^ (-1 / 3 : Real)) *
                          (((1 + K * s0 / Real.log level) / s0) *
                            (Real.log level) ^ (-1 / 24 : Real) *
                            (dimensionOneRosserArtificialFactor
                                (Real.log level) 0 s0 *
                              dimensionOneDelayScaledPlus s0)) ∧
                      lowerRosserFailurePartialSum P
                          (fun p => (p : Real)⁻¹) level
                          (level ^ (1 / s0)) R <
                        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
                            (Real.log level) ^ (-1 / 3 : Real)) *
                          (((1 + K * s0 / Real.log level) / s0) *
                            (Real.log level) ^ (-1 / 24 : Real) *
                            (dimensionOneRosserArtificialFactor
                                (Real.log level) 0 s0 *
                              dimensionOneDelayScaledMinus s0)) := by
  obtain ⟨S, hS, hseed⟩ :=
    exists_dimensionOneRosserFailurePartialSums_sourceNormalized
  refine ⟨S, hS, ?_⟩
  intro P R K level z s s0 hprime hlevel hz hs hsLower hss0 hcutoff
    hsTail hLExp hsource hRatio
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hlevelPos : 0 < level := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogw : Real.log (level ^ (1 / s0)) =
      Real.log level / s0 := log_rpow_one_div hlevelPos
  have hs0Cutoff :
      s0 = Real.log level / Real.log (level ^ (1 / s0)) := by
    rw [hlogw]
    field_simp [hL.ne', hs0Pos.ne']
  have hbounds := hseed P R hprime hlevel hcutoff hs0Cutoff hsTail hLExp
    hsource
  constructor
  · apply sourceNormalizedBoundary_transport P hbounds.1
    · exact mul_nonneg (Real.exp_pos _).le
        (dimensionOneDelayScaledPlus_pos hs0Pos).le
    · exact hprime
    · exact hlevel
    · exact hz
    · exact hs
    · exact hsLower
    · exact hss0
    · exact hRatio
  · apply sourceNormalizedBoundary_transport P hbounds.2
    · exact mul_nonneg (Real.exp_pos _).le
        (dimensionOneDelayScaledMinus_pos hs0Pos).le
    · exact hprime
    · exact hlevel
    · exact hz
    · exact hs
    · exact hsLower
    · exact hss0
    · exact hRatio

/- Direct recurrence-facing wrappers for relaxed estimates. -/
theorem dimensionOneRosserSourcePlusSecondRawPrimeSum_lt_absorbed
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsource : s0 ^ 50 = Real.log level *
      (Real.log (Real.log level)) ^ 3)
    (hLExp : Real.exp 1 <= Real.log level)
    (hgate : 124800 + 14400 * Real.log (Real.log (Real.log level)) <=
      Real.log (Real.log level))
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= (Real.log level) ^ (1 / 24 : Real))
    (hRatio : ∀ u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / (2 * s0)) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledPlus s) := by
  exact (dimensionOneRosserPlusSecondRawPrimeSum_le_relaxed_of_two_le
    P hprime hlevel hz hs (by linarith) hcutoff).trans_lt
      (dimensionOneRosserSourcePlusSecondRelaxedPrimeSum_lt_absorbed
        P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp
          hgate hgrowth hdom hRatio)

theorem dimensionOneRosserSourceMinusSecondRawPrimeSum_lt_absorbed
    (P : Finset Nat) {K level z s s0 : Real}
    (hK : 0 <= K) (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0) (hcutoff : 2 <= level ^ (1 / s0))
    (hsource : s0 ^ 50 = Real.log level *
      (Real.log (Real.log level)) ^ 3)
    (hLExp : Real.exp 1 <= Real.log level)
    (hgate : 124800 + 14400 * Real.log (Real.log (Real.log level)) <=
      Real.log (Real.log level))
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= (Real.log level) ^ (1 / 24 : Real))
    (hRatio : ∀ u : Real,
      level ^ (1 / s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) z / s *
        (Real.log level) ^ (-1 / 3 : Real)) *
        ((1 - 1 / (2 * s0)) *
          (1 + s ^ 50 / Real.log level) ^ s *
            dimensionOneDelayScaledMinus s) := by
  exact (dimensionOneRosserMinusSecondRawPrimeSum_le_relaxed_of_two_le
    P hprime hlevel hz hs hsLower hcutoff).trans_lt
      (dimensionOneRosserSourceMinusSecondRelaxedPrimeSum_lt_absorbed
        P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp
          hgate hgrowth hdom hRatio)

private theorem sourceSignLedger_of_estimates
    {boundary first second scale decay boundaryProfile firstProfile
      secondProfile D : Real}
    (hD : 0 <= D)
    (hboundary : boundary < scale * decay * boundaryProfile)
    (hfirst : first <= scale * firstProfile)
    (hsecond : second < scale * decay * secondProfile) :
    boundary + first + D * second <
      scale * (firstProfile +
        decay * (boundaryProfile + D * secondProfile)) := by
  have hsecondScaled :
      D * second <= D * (scale * decay * secondProfile) :=
    mul_le_mul_of_nonneg_left hsecond.le hD
  calc
    boundary + first + D * second <
        scale * decay * boundaryProfile + scale * firstProfile +
          D * (scale * decay * secondProfile) :=
      add_lt_add_of_lt_of_le
        (add_lt_add_of_lt_of_le hboundary hfirst) hsecondScaled
    _ = _ := by ring

/- Three-term ledger for the upper target. -/
theorem exists_dimensionOneRosserPlusSourceCutoffThreeTermLedger :
    ∃ S : Real, Real.exp 5000 + 1 <= S ∧
      ∀ (P : Finset Nat) (R : Nat) {D K level z s s0 : Real},
        0 <= D -> 0 < R -> 0 <= K ->
          (∀ p ∈ P, p.Prime) ->
            2 <= level -> 2 <= z ->
              s = Real.log level / Real.log z -> 3 <= s -> s < s0 ->
                2 <= level ^ (1 / s0) -> S <= s0 ->
                  s0 ^ 50 = Real.log level *
                    (Real.log (Real.log level)) ^ 3 ->
                    Real.exp 1 <= Real.log level ->
                      124800 + 14400 *
                          Real.log (Real.log (Real.log level)) <=
                        Real.log (Real.log level) ->
                      dimensionOneRosserSecondLevelThreshold <=
                        Real.log level ->
                      13824 * K <=
                        (Real.log level) ^ (1 / 24 : Real) ->
                      (∀ u : Real,
                        level ^ (1 / s0) <= u -> u < z ->
                        sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
                            sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
                          (Real.log z / Real.log u) *
                            (1 + K / Real.log u)) ->
                        upperRosserFailurePartialSum P
                            (fun p => (p : Real)⁻¹) level
                            (level ^ (1 / s0)) R +
                          dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
                          D * dimensionOneRosserPlusSecondRawPrimeSum
                            P level s0 z <
                        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
                          ((dimensionOneRosserModelPlusPartialSum R s -
                              dimensionOneRosserModelPlusPartialSum R s0 +
                            (2 * K * s0 /
                              (Real.log level * (1 - 1 / s))) *
                              dimensionOneRosserModelMinusPartialSum R
                                (s - 1)) +
                            (Real.log level) ^ (-1 / 3 : Real) *
                              ((((1 + K * s0 / Real.log level) / s0) *
                                  (Real.log level) ^ (-1 / 24 : Real) *
                                  (dimensionOneRosserArtificialFactor
                                      (Real.log level) 0 s0 *
                                    dimensionOneDelayScaledPlus s0)) +
                                D * ((1 - 1 / (2 * s0)) *
                                  (1 + s ^ 50 / Real.log level) ^ s *
                                    dimensionOneDelayScaledPlus s))) := by
  obtain ⟨S, hS, hboundaryAll⟩ :=
    exists_dimensionOneRosserFailurePartialSums_sourceNormalized_transport
  refine ⟨S, hS, ?_⟩
  intro P R D K level z s s0 hD hR hK hprime hlevel hz hs hsLower
    hss0 hcutoff hsTail hsource hLExp hgate hgrowth hdom hRatio
  have hboundary := (hboundaryAll P R hprime hlevel hz hs
    (by linarith : 2 <= s) hss0 hcutoff hsTail hLExp hsource hRatio).1
  have hfirst := dimensionOneRosserPlusFirstPrimeSum_le_of_ratio P R hR hK
    hprime hlevel hz hs hsLower hss0 hcutoff hRatio
  have hsecond := dimensionOneRosserSourcePlusSecondRawPrimeSum_lt_absorbed
    P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp hgate
      hgrowth hdom hRatio
  exact sourceSignLedger_of_estimates hD hboundary hfirst hsecond

/- Three-term ledger for the lower successor target. -/
theorem exists_dimensionOneRosserMinusSourceCutoffThreeTermLedger :
    ∃ S : Real, Real.exp 5000 + 1 <= S ∧
      ∀ (P : Finset Nat) (R : Nat) {D K level z s s0 : Real},
        0 <= D -> 0 <= K ->
          (∀ p ∈ P, p.Prime) ->
            2 <= level -> 2 <= z ->
              s = Real.log level / Real.log z -> 2 <= s -> s < s0 ->
                2 <= level ^ (1 / s0) -> S <= s0 ->
                  s0 ^ 50 = Real.log level *
                    (Real.log (Real.log level)) ^ 3 ->
                    Real.exp 1 <= Real.log level ->
                      124800 + 14400 *
                          Real.log (Real.log (Real.log level)) <=
                        Real.log (Real.log level) ->
                      dimensionOneRosserSecondLevelThreshold <=
                        Real.log level ->
                      13824 * K <=
                        (Real.log level) ^ (1 / 24 : Real) ->
                      (∀ u : Real,
                        level ^ (1 / s0) <= u -> u < z ->
                        sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
                            sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
                          (Real.log z / Real.log u) *
                            (1 + K / Real.log u)) ->
                        lowerRosserFailurePartialSum P
                            (fun p => (p : Real)⁻¹) level
                            (level ^ (1 / s0)) (R + 1) +
                          dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
                          D * dimensionOneRosserMinusSecondRawPrimeSum
                            P level s0 z <
                        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
                          ((dimensionOneRosserModelMinusPartialSum (R + 1) s -
                              dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
                            (2 * K * s0 /
                              (Real.log level * (1 - 1 / s))) *
                              dimensionOneRosserModelPlusPartialSum R
                                (s - 1)) +
                            (Real.log level) ^ (-1 / 3 : Real) *
                              ((((1 + K * s0 / Real.log level) / s0) *
                                  (Real.log level) ^ (-1 / 24 : Real) *
                                  (dimensionOneRosserArtificialFactor
                                      (Real.log level) 0 s0 *
                                    dimensionOneDelayScaledMinus s0)) +
                                D * ((1 - 1 / (2 * s0)) *
                                  (1 + s ^ 50 / Real.log level) ^ s *
                                    dimensionOneDelayScaledMinus s))) := by
  obtain ⟨S, hS, hboundaryAll⟩ :=
    exists_dimensionOneRosserFailurePartialSums_sourceNormalized_transport
  refine ⟨S, hS, ?_⟩
  intro P R D K level z s s0 hD hK hprime hlevel hz hs hsLower
    hss0 hcutoff hsTail hsource hLExp hgate hgrowth hdom hRatio
  have hboundary := (hboundaryAll P (R + 1) hprime hlevel hz hs
    (by linarith : 2 <= s) hss0 hcutoff hsTail hLExp hsource hRatio).2
  have hfirst := dimensionOneRosserMinusFirstPrimeSum_le_of_ratio P R hK
    hprime hlevel hz hs hsLower hss0 hcutoff hRatio
  have hsecond := dimensionOneRosserSourceMinusSecondRawPrimeSum_lt_absorbed
    P hK hprime hlevel hz hs hsLower hss0 hcutoff hsource hLExp hgate
      hgrowth hdom hRatio
  exact sourceSignLedger_of_estimates hD hboundary hfirst hsecond

end PrimesRestrictedDigits
