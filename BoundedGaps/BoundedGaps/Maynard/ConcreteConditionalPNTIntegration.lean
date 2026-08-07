import BoundedGaps.Maynard.ConcreteAsymptotics
import BoundedGaps.Maynard.ConcreteYDiagonalS1Limit
import BoundedGaps.Maynard.ConcreteS2MainNumeratorLimit
import BoundedGaps.Maynard.ConcreteS2PrimeLevelBridge

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

/-!
# Conditional PNT and Bombieri--Vinogradov integration

This module packages the proved concrete S1 limit, the SEM-406 conditional S2
main limit, and the prime-level S2 error bridge.  Ordinary PNT and
Bombieri--Vinogradov remain explicit hypotheses.
-/

theorem engelsmaSmallKCandidateNormalizedAsymptotics_of_primeLevel_and_pnt
    {theta delta : ℝ} (htheta : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta / 2)
    (hlevel : hasPrimeLevel theta)
    (hpnt : Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    EngelsmaSmallKCandidateNormalizedAsymptotics
      (theta / 2 - delta) := by
  have halpha : 0 < theta / 2 - delta := sub_pos.mpr hdeltaTheta
  have halphaQuarter : theta / 2 - delta < 1 / 4 := by
    linarith
  refine ⟨tendsto_engelsmaMaynardS1 halpha halphaQuarter, ?_⟩
  apply tendsto_engelsmaMaynardS2_of_main_and_primeLevel
    htheta hthetaHalf hdelta hdeltaTheta hlevel
  exact
    tendsto_engelsmaMaynardS2Main_div_scale_of_pnt_eq_maynardNumerator
      halpha hpnt

theorem boundedGapsStatement_of_bombieriVinogradov_and_pnt
    (hBV : bombieriVinogradov)
    (hpnt : Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    BoundedGaps.boundedGapsStatement := by
  apply boundedGapsStatement_of_bombieriVinogradov_and_concrete_normalized_asymptotics
    hBV
  intro theta delta htheta hthetaHalf hlevel hdelta hdeltaTheta
  exact engelsmaSmallKCandidateNormalizedAsymptotics_of_primeLevel_and_pnt
    htheta hthetaHalf hdelta hdeltaTheta hlevel hpnt

#print axioms
  engelsmaSmallKCandidateNormalizedAsymptotics_of_primeLevel_and_pnt
#print axioms boundedGapsStatement_of_bombieriVinogradov_and_pnt

end BoundedGaps.Maynard
