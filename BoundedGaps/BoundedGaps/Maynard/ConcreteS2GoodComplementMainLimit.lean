import BoundedGaps.Maynard.ConcretePrimeCountPNTRadius
import BoundedGaps.Maynard.ConcreteS2GoodComplementExpansion
import BoundedGaps.Maynard.ConcreteS2GoodComplementScaleBridge
import BoundedGaps.Maynard.ConcreteS2FaceLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter MeasureTheory
open scoped BigOperators

/-!
# Conditional complementary S2 main limit

Under the explicit cumulative prime-number-theorem hypothesis, the exact
complementary main/scale identity is combined with the shifted prime-factor,
moment, and radius-ratio limits.  The resulting face sum is identified with
Maynard's numerator in `ConcreteS2FaceLimit`.  See Maynard2013v3, Proposition
4.1 and Sections 5--6, especially (5.18), (5.26)--(5.27), and (6.13)--(6.21).
-/

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
theorem tendsto_engelsmaMaynardS2GoodComplementMain_div_scale_of_pnt
    {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ =>
        engelsmaMaynardS2GoodComplementMain alpha N /
          engelsmaMaynardScale alpha N)
      atTop
      (nhds (alpha *
        (∑ m ∈ BoundedGaps.engelsmaTuple.attach,
          engelsmaS2GoodOuterFaceLimit m))) := by
  have hratio :=
    (tendsto_log_engelsmaMaynardRadius_div_realRadius halpha).pow 105
  have hterm : ∀ m : BoundedGaps.engelsmaTuple,
      Tendsto
        (fun N : ℕ =>
          (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
            normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment alpha N m *
            Real.log (engelsmaMaynardRadius alpha N) *
            (Real.log (engelsmaMaynardRadius alpha N) /
              Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop (nhds (alpha * engelsmaS2GoodOuterFaceLimit m)) := by
    intro m
    have hprime := tendsto_engelsmaShiftedPrimeIntervalFactor_of_pnt
      halpha hpnt m
    have hmoment :=
      tendsto_normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
        halpha m
    have hmul := (hprime.mul hmoment).mul hratio
    simpa [engelsmaS2GoodOuterFaceLimit, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
            (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
              normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment alpha N m *
              Real.log (engelsmaMaynardRadius alpha N) *
              (Real.log (engelsmaMaynardRadius alpha N) /
                Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop
        (nhds (∑ m ∈ BoundedGaps.engelsmaTuple.attach,
          alpha * engelsmaS2GoodOuterFaceLimit m)) := by
    apply tendsto_finsetSum
    intro m hm
    exact hterm m
  have hsum' :
      Tendsto
        (fun N : ℕ =>
          ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
            (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
              normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment alpha N m *
              Real.log (engelsmaMaynardRadius alpha N) *
              (Real.log (engelsmaMaynardRadius alpha N) /
                Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop
        (nhds (alpha * ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
          engelsmaS2GoodOuterFaceLimit m)) := by
    simpa [Finset.mul_sum] using hsum
  have hbridge : ∀ᶠ N : ℕ in atTop,
      engelsmaMaynardS2GoodComplementMain alpha N /
          engelsmaMaynardScale alpha N =
        ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
          (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
            normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment alpha N m *
            Real.log (engelsmaMaynardRadius alpha N) *
            (Real.log (engelsmaMaynardRadius alpha N) /
              Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
    filter_upwards [eventually_ge_atTop 1,
      eventually_one_lt_engelsmaMaynardRadius halpha,
      eventually_ge_atTop 3] with N hN hR hN3
    have hNpos : 0 < N := by omega
    have hRreal : 1 < engelsmaMaynardRealRadius alpha N := by
      unfold engelsmaMaynardRealRadius maynardRealCutoff
      apply Real.one_lt_rpow
      · exact_mod_cast (show 1 < N - 1 by omega)
      · exact halpha
    exact engelsmaMaynardS2GoodComplementMain_div_scale_eq hNpos hR hRreal
  apply hsum'.congr'
  filter_upwards [hbridge] with N hN
  exact hN.symm

#print axioms tendsto_engelsmaMaynardS2GoodComplementMain_div_scale_of_pnt

end BoundedGaps.Maynard
