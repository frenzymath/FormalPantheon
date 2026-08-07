import BoundedGaps.Maynard.ConcreteIndependentMomentLimit
import BoundedGaps.Maynard.ConcreteYDiagonalCollisionLimit
import BoundedGaps.Maynard.ConcreteS1DiagonalBridge

noncomputable section
namespace BoundedGaps.Maynard

open Filter

set_option maxRecDepth 10000 in
theorem tendsto_engelsmaMaynardYDiagonal
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (((N : ℝ) / engelsmaMaynardModulus N) *
        engelsmaMaynardYDiagonal alpha N) /
          engelsmaMaynardScale alpha N)
      atTop (nhds (maynardI 105 smallKCandidate)) := by
  apply tendsto_engelsmaMaynardYDiagonal_of_independent_collision_limits halpha
  · intro i j
    exact tendsto_normalizedEngelsmaIndependentQuadraticMoment halpha
      (smallKExponentB i + smallKExponentB j)
      (smallKExponentC i + smallKExponentC j)
  · intro i j
    exact tendsto_normalized_engelsmaCollisionQuadraticMoment_zero halpha
      (smallKExponentB i + smallKExponentB j)
      (smallKExponentC i + smallKExponentC j)

theorem tendsto_engelsmaMaynardS1Main
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      engelsmaMaynardS1Main alpha N / engelsmaMaynardScale alpha N)
      atTop (nhds (maynardI 105 smallKCandidate)) :=
  tendsto_engelsmaMaynardS1Main_of_diagonal_limit halpha
    (tendsto_engelsmaMaynardYDiagonal halpha)

theorem tendsto_engelsmaMaynardS1
    {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto (fun N : ℕ => sieveWeightSum N
      (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaPreSieveResidue engelsmaSmallKCandidate N) /
          engelsmaMaynardScale alpha N)
      atTop (nhds (maynardI 105 smallKCandidate)) :=
  tendsto_engelsmaMaynardS1_of_diagonal_limit halpha halphaQuarter
    (tendsto_engelsmaMaynardYDiagonal halpha)

end BoundedGaps.Maynard
