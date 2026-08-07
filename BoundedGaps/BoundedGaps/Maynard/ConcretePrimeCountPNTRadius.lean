import BoundedGaps.Maynard.ConcretePrimeCountPNTInterval
import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics
import BoundedGaps.Maynard.ConcreteShiftedPrimeEndpointLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-
Radius and shifted corollaries of the explicit cumulative PNT boundary;
see SEM-402 and Maynard2013v3, Proposition 4.1. The PNT hypothesis remains a
theorem argument throughout.
-/
theorem tendsto_primeCountTotalInInterval_div_mul_log_radius_of_pnt
    {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ =>
        (primeCountTotalInInterval N : ℝ) / (N : ℝ) *
          Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds alpha) := by
  have hinterval :=
    tendsto_primeCountTotalInInterval_div_mul_log_sub_of_pnt hpnt
  have hradius := tendsto_log_engelsmaMaynardRadius_div_log_sub halpha
  have h := hinterval.mul hradius
  have hlogBase : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  have heq :
      (fun N : ℕ =>
        ((primeCountTotalInInterval N : ℝ) / (N : ℝ) *
            Real.log ((N - 1 : ℕ) : ℝ)) *
          (Real.log (engelsmaMaynardRadius alpha N) /
            Real.log ((N - 1 : ℕ) : ℝ))) =ᶠ[atTop]
      (fun N : ℕ =>
        (primeCountTotalInInterval N : ℝ) / (N : ℝ) *
          Real.log (engelsmaMaynardRadius alpha N)) := by
    filter_upwards [hlogBase.eventually (eventually_ne_atTop 0)] with N hlog0
    field_simp [hlog0]
  simpa using h.congr' heq

theorem tendsto_engelsmaShiftedPrimeIntervalFactor_of_pnt
    {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1))
    (h : BoundedGaps.engelsmaTuple) :
    Tendsto
      (fun N : ℕ =>
        (engelsmaShiftedPrimeIntervalCount N h / (N : ℝ)) *
          Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds alpha) := by
  have hunshifted :=
    tendsto_primeCountTotalInInterval_div_mul_log_radius_of_pnt
      halpha hpnt
  have hdiff :=
    tendsto_engelsmaShiftedPrimeIntervalFactor_sub_unshifted_zero
      halpha h
  have hsum := hunshifted.add hdiff
  have hsum' : Tendsto
      (fun N : ℕ =>
        (primeCountTotalInInterval N : ℝ) / (N : ℝ) *
            Real.log (engelsmaMaynardRadius alpha N) +
          ((engelsmaShiftedPrimeIntervalCount N h / (N : ℝ)) *
              Real.log (engelsmaMaynardRadius alpha N) -
            ((primeCountTotalInInterval N : ℝ) / (N : ℝ)) *
              Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds alpha) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [] with N
  ring

end BoundedGaps.Maynard
