import BoundedGaps.Maynard.MaynardWeights
import BoundedGaps.Maynard.AsymptoticPositivity

/-!
# Concrete Maynard weights and the conditional positivity endpoint

This module instantiates the generic normalized-asymptotics bridge with the
finite coefficient and support defined from Maynard2013v3, Proposition
`MainProp` (source lines 202--216). The analytic limits and
Bombieri--Vinogradov input remain explicit hypotheses.
-/

namespace BoundedGaps.Maynard

open Filter Set

noncomputable def maynardSupportFamily
    (H : Finset ℕ) (R W : ℕ → ℕ) : ℕ → Finset (H → ℕ) :=
  fun N => maynardDivisorTupleSupport H (R N) (W N)

noncomputable def maynardCoefficientFamily
    (H : Finset ℕ) (R W : ℕ → ℕ) (F : (H → ℝ) → ℝ) :
    ℕ → (H → ℕ) → ℝ :=
  fun N d => maynardCoefficient H (R N) (W N) F d

noncomputable def maynardSquareDivisorWeightFamily
    (H : Finset ℕ) (R W : ℕ → ℕ) (F : (H → ℝ) → ℝ) :
    ℕ → ℕ → ℝ :=
  fun N n => squareDivisorWeight H
    (maynardSupportFamily H R W N)
    (maynardCoefficientFamily H R W F N) n

noncomputable def maynardPreSievedWeightFamily
    (H : Finset ℕ) (R W v : ℕ → ℕ) (F : (H → ℝ) → ℝ) :
    ℕ → ℕ → ℝ :=
  fun N n => preSievedSquareDivisorWeight H
    (maynardSupportFamily H R W N)
    (maynardCoefficientFamily H R W F N)
    (v N) (W N) n

theorem maynardSupportFamily_mem_isMaynard
    {H : Finset ℕ} {R W : ℕ → ℕ} {N : ℕ} {d : H → ℕ}
    (hd : d ∈ maynardSupportFamily H R W N) :
    IsMaynardDivisorTuple H (R N) (W N) d := by
  exact isMaynardDivisorTuple_of_mem_support hd

theorem hasEventuallyPositiveMaynardSquareDivisorSieveExcess_of_normalized_asymptotics
    {H : Finset ℕ} {rho I J : ℝ}
    (R W : ℕ → ℕ) (F : (H → ℝ) → ℝ) (scale : ℕ → ℝ)
    (hmargin : 0 < J - rho * I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hS1 : Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardSquareDivisorWeightFamily H R W F N) / scale N)
      atTop (nhds I))
    (hS2 : Tendsto
      (fun N : ℕ => primeWeightedSieveSum H N
        (maynardSquareDivisorWeightFamily H R W F N) / scale N)
      atTop (nhds J)) :
    HasEventuallyPositiveSquareDivisorSieveExcess H rho := by
  exact hasEventuallyPositiveSquareDivisorSieveExcess_of_normalized_asymptotics
    (D := maynardSupportFamily H R W)
    (lambda := maynardCoefficientFamily H R W F)
    scale hmargin hscale hS1 hS2

theorem hasEventuallyPositiveMaynardPreSievedSieveExcess_of_normalized_asymptotics
    {H : Finset ℕ} {rho I J : ℝ}
    (R W v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (scale : ℕ → ℝ)
    (hmargin : 0 < J - rho * I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hS1 : Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardPreSievedWeightFamily H R W v F N) / scale N)
      atTop (nhds I))
    (hS2 : Tendsto
      (fun N : ℕ => primeWeightedSieveSum H N
        (maynardPreSievedWeightFamily H R W v F N) / scale N)
      atTop (nhds J)) :
    HasEventuallyPositiveSieveExcess H rho := by
  exact hasEventuallyPositivePreSievedSieveExcess_of_normalized_asymptotics
    (D := maynardSupportFamily H R W)
    (lambda := maynardCoefficientFamily H R W F)
    v W scale hmargin hscale hS1 hS2

theorem boundedGapsStatement_of_engelsma_maynardPreSieved_normalized_asymptotics
    {I J : ℝ} (R W v : ℕ → ℕ)
    (F : (BoundedGaps.engelsmaTuple → ℝ) → ℝ) (scale : ℕ → ℝ)
    (hmargin : 0 < J - I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hS1 : Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple R W v F N) /
          scale N)
      atTop (nhds I))
    (hS2 : Tendsto
      (fun N : ℕ => primeWeightedSieveSum BoundedGaps.engelsmaTuple N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple R W v F N) /
          scale N)
      atTop (nhds J)) :
    BoundedGaps.boundedGapsStatement := by
  apply boundedGapsStatement_of_engelsma_eventuallyPositiveSieveExcess
  apply hasEventuallyPositiveMaynardPreSievedSieveExcess_of_normalized_asymptotics
    R W v F scale
  · simpa using hmargin
  · exact hscale
  · exact hS1
  · exact hS2

end BoundedGaps.Maynard
