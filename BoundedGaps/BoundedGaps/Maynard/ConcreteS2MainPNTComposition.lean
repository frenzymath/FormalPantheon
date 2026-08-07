import BoundedGaps.Maynard.ConcreteS2GoodComplementMainErrorLimit
import BoundedGaps.Maynard.ConcretePrimeCountPNTRadius
import BoundedGaps.Maynard.ConcreteS2GoodComplementMainLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

/-!
# Conditional full S2 main composition

The SEM-398 normalized error limit is composed with the SEM-404
complementary-main limit under the same visible cumulative PNT hypothesis.
The resulting target is the exact face-functional sum; SEM-403 identifies it
with Maynard's numerator.  No ordinary PNT or Bombieri--Vinogradov theorem is
asserted here.
-/

theorem tendsto_engelsmaMaynardS2Main_sub_goodComplementMain_div_scale_zero_of_pnt
    {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ =>
        (engelsmaMaynardS2Main alpha N -
          engelsmaMaynardS2GoodComplementMain alpha N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  apply tendsto_engelsmaMaynardS2Main_sub_goodComplementMain_div_scale_zero
    halpha
  intro m
  exact tendsto_engelsmaShiftedPrimeIntervalFactor_of_pnt
    halpha hpnt m

theorem tendsto_engelsmaMaynardS2Main_div_scale_of_pnt
    {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ =>
        engelsmaMaynardS2Main alpha N /
          engelsmaMaynardScale alpha N)
      atTop
      (nhds (alpha *
        (∑ m ∈ BoundedGaps.engelsmaTuple.attach,
          engelsmaS2GoodOuterFaceLimit m))) := by
  have herr :=
    tendsto_engelsmaMaynardS2Main_sub_goodComplementMain_div_scale_zero_of_pnt
      halpha hpnt
  have hmain :=
    tendsto_engelsmaMaynardS2GoodComplementMain_div_scale_of_pnt
      halpha hpnt
  have hadd := herr.add hmain
  have hadd' :
      Tendsto
        (fun N : ℕ =>
          (engelsmaMaynardS2Main alpha N -
            engelsmaMaynardS2GoodComplementMain alpha N) /
              engelsmaMaynardScale alpha N +
            engelsmaMaynardS2GoodComplementMain alpha N /
              engelsmaMaynardScale alpha N)
        atTop
        (nhds (alpha *
          (∑ m ∈ BoundedGaps.engelsmaTuple.attach,
            engelsmaS2GoodOuterFaceLimit m))) := by
    simpa using hadd
  apply hadd'.congr'
  filter_upwards [] with N
  ring

#print axioms
  tendsto_engelsmaMaynardS2Main_sub_goodComplementMain_div_scale_zero_of_pnt
#print axioms tendsto_engelsmaMaynardS2Main_div_scale_of_pnt

end BoundedGaps.Maynard
