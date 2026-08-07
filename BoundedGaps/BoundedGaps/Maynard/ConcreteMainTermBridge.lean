import BoundedGaps.Maynard.ConcreteS1DiagonalBridge
import BoundedGaps.Maynard.ConcreteS2PrimeLevelBridge
import BoundedGaps.Maynard.LevelSelection

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

/-! The bounded-gaps conclusion now requires only the two concrete main terms. -/

theorem boundedGapsStatement_of_engelsma_diagonal_and_s2Main
    {theta delta : ℝ} (htheta : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta / 2)
    (hlevel : hasPrimeLevel theta)
    (hmargin :
      0 < (theta / 2 - delta) *
          (∑ m : Fin 105, maynardJ 105 m smallKCandidate) -
        maynardI 105 smallKCandidate)
    (hS1Diagonal : Tendsto
      (fun N : ℕ =>
        ((N : ℝ) / engelsmaMaynardModulus N *
          engelsmaMaynardYDiagonal (theta / 2 - delta) N) /
          engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds (maynardI 105 smallKCandidate)))
    (hS2Main : Tendsto
      (fun N : ℕ => engelsmaMaynardS2Main (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds ((theta / 2 - delta) *
        (∑ m : Fin 105, maynardJ 105 m smallKCandidate)))) :
    BoundedGaps.boundedGapsStatement := by
  have halpha : 0 < theta / 2 - delta := sub_pos.mpr hdeltaTheta
  have halphaQuarter : theta / 2 - delta < 1 / 4 := by linarith
  apply boundedGapsStatement_of_engelsmaSmallKCandidate_concrete_normalized_asymptotics
    halpha hmargin
  · exact tendsto_engelsmaMaynardS1_of_diagonal_limit
      halpha halphaQuarter hS1Diagonal
  · exact tendsto_engelsmaMaynardS2_of_main_and_primeLevel
      htheta hthetaHalf hdelta hdeltaTheta hlevel hS2Main

theorem boundedGapsStatement_of_bombieriVinogradov_and_concrete_mainTerms
    (hBV : bombieriVinogradov)
    (hS1Diagonal : ∀ theta delta : ℝ,
      0 < theta → theta < 1 / 2 → hasPrimeLevel theta →
      0 < delta → delta < theta / 2 →
      Tendsto
        (fun N : ℕ =>
          ((N : ℝ) / engelsmaMaynardModulus N *
            engelsmaMaynardYDiagonal (theta / 2 - delta) N) /
            engelsmaMaynardScale (theta / 2 - delta) N)
        atTop (nhds (maynardI 105 smallKCandidate)))
    (hS2Main : ∀ theta delta : ℝ,
      0 < theta → theta < 1 / 2 → hasPrimeLevel theta →
      0 < delta → delta < theta / 2 →
      Tendsto
        (fun N : ℕ => engelsmaMaynardS2Main (theta / 2 - delta) N /
          engelsmaMaynardScale (theta / 2 - delta) N)
        atTop (nhds ((theta / 2 - delta) *
          (∑ m : Fin 105, maynardJ 105 m smallKCandidate)))) :
    BoundedGaps.boundedGapsStatement := by
  obtain ⟨theta, delta, htheta, hthetaHalf, hlevel,
      hdelta, hdeltaTheta, hmargin⟩ :=
    exists_smallKCandidate_level_delta_with_positive_mainTerm hBV
  exact boundedGapsStatement_of_engelsma_diagonal_and_s2Main
    htheta hthetaHalf hdelta hdeltaTheta hlevel hmargin
    (hS1Diagonal theta delta htheta hthetaHalf hlevel hdelta hdeltaTheta)
    (hS2Main theta delta htheta hthetaHalf hlevel hdelta hdeltaTheta)

end BoundedGaps.Maynard
