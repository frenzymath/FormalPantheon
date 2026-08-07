import BoundedGaps.Maynard.ConcreteS2
import BoundedGaps.Maynard.ConcreteS2TauErrorLimit

namespace BoundedGaps.Maynard

open Filter

/-! Prime-level distribution removes the remaining concrete S2 error. -/

theorem tendsto_engelsmaMaynardS2_of_main_and_primeLevel
    {theta delta I : ℝ} (htheta : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta / 2)
    (hlevel : hasPrimeLevel theta)
    (hmain : Tendsto
      (fun N : ℕ => engelsmaMaynardS2Main (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds I)) :
    Tendsto
      (fun N : ℕ => primeWeightedSieveSum BoundedGaps.engelsmaTuple N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius (theta / 2 - delta))
          engelsmaMaynardModulus engelsmaPreSieveResidue
          engelsmaSmallKCandidate N) /
            engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds I) := by
  apply tendsto_engelsmaMaynardS2_of_main_error
    hthetaHalf hdelta hdeltaTheta hmain
  exact tendsto_engelsmaMaynardS2Error_zero_of_primeLevel
    htheta hthetaHalf hdelta hdeltaTheta hlevel

end BoundedGaps.Maynard
