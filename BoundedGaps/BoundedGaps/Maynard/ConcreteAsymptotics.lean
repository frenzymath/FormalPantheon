import BoundedGaps.Maynard.ConcreteS2

/-!
# The concrete normalized-asymptotics contract

This module packages the two limits from Maynard2013v3, Proposition
`MainProp` (source lines 202--216), for the fully frozen Engelsma candidate
and parameter families. The limits remain an explicit Packet B proposition.
-/

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def EngelsmaSmallKCandidateNormalizedAsymptotics (alpha : ℝ) : Prop :=
  Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaPreSieveResidue engelsmaSmallKCandidate N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds (maynardI 105 smallKCandidate)) ∧
    Tendsto
      (fun N : ℕ => primeWeightedSieveSum BoundedGaps.engelsmaTuple N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaPreSieveResidue engelsmaSmallKCandidate N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds
        (alpha * (∑ m : Fin 105, maynardJ 105 m smallKCandidate)))

theorem engelsmaSmallKCandidateNormalizedAsymptotics_of_component_limits
    {theta delta : ℝ} (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hS1Main : Tendsto
      (fun N : ℕ => engelsmaMaynardS1Main (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds (maynardI 105 smallKCandidate)))
    (hS1Error : Tendsto
      (fun N : ℕ => engelsmaMaynardS1Error (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds 0))
    (hS2Main : Tendsto
      (fun N : ℕ => engelsmaMaynardS2Main (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds ((theta / 2 - delta) * (∑ m : Fin 105,
          maynardJ 105 m smallKCandidate))))
    (hS2Error : Tendsto
      (fun N : ℕ => engelsmaMaynardS2Error (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds 0)) :
    EngelsmaSmallKCandidateNormalizedAsymptotics (theta / 2 - delta) := by
  refine ⟨?_, ?_⟩
  · exact tendsto_engelsmaMaynardS1_of_main_error
      (sub_pos.mpr hdeltaTheta) hS1Main hS1Error
  · exact tendsto_engelsmaMaynardS2_of_main_error
      hthetaHalf hdelta hdeltaTheta hS2Main hS2Error

set_option maxRecDepth 2000 in
theorem engelsmaSmallKCandidateNormalizedAsymptotics_of_main_and_envelopes
    {theta delta : ℝ} (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hS1Main : Tendsto
      (fun N : ℕ => engelsmaMaynardS1Main (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds (maynardI 105 smallKCandidate)))
    (hS1Envelope : Tendsto
      (fun N : ℕ =>
        ((engelsmaMaynardRadius (theta / 2 - delta) N : ℝ) *
          (1 + Real.log (engelsmaMaynardRadius (theta / 2 - delta) N)) ^
            Fintype.card BoundedGaps.engelsmaTuple) ^ 2 *
          ((engelsmaMaynardRadius (theta / 2 - delta) N : ℝ) *
            smallKCandidateBound *
            (1 + Real.log (engelsmaMaynardRadius (theta / 2 - delta) N)) ^
              (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 /
            engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds 0))
    (hS2Main : Tendsto
      (fun N : ℕ => engelsmaMaynardS2Main (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds ((theta / 2 - delta) * (∑ m : Fin 105,
          maynardJ 105 m smallKCandidate))))
    (hS2Error : Tendsto
      (fun N : ℕ => engelsmaMaynardS2Error (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds 0)) :
    EngelsmaSmallKCandidateNormalizedAsymptotics (theta / 2 - delta) := by
  exact engelsmaSmallKCandidateNormalizedAsymptotics_of_component_limits
    hthetaHalf hdelta hdeltaTheta hS1Main
    (tendsto_engelsmaMaynardS1Error_zero_of_explicit_log_envelope
      (sub_pos.mpr hdeltaTheta) hS1Envelope)
    hS2Main hS2Error

theorem boundedGapsStatement_of_bombieriVinogradov_and_concrete_normalized_asymptotics
    (hBV : bombieriVinogradov)
    (hAsymptotics : ∀ theta delta : ℝ,
      0 < theta → theta < 1 / 2 → hasPrimeLevel theta →
      0 < delta → delta < theta / 2 →
      EngelsmaSmallKCandidateNormalizedAsymptotics (theta / 2 - delta)) :
    BoundedGaps.boundedGapsStatement := by
  obtain ⟨theta, delta, htheta0, hthetaHalf, hlevel,
      hdelta0, hdeltaTheta, hmargin⟩ :=
    exists_smallKCandidate_level_delta_with_positive_mainTerm hBV
  have hasymptotics := hAsymptotics theta delta htheta0 hthetaHalf hlevel
    hdelta0 hdeltaTheta
  exact boundedGapsStatement_of_engelsmaSmallKCandidate_concrete_normalized_asymptotics
    (alpha := theta / 2 - delta) (sub_pos.mpr hdeltaTheta) hmargin
    hasymptotics.1 hasymptotics.2

end BoundedGaps.Maynard
