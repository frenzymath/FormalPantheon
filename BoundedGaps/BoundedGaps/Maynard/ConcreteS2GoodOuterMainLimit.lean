import BoundedGaps.Maynard.ConcreteS2GoodOuterScaleBridge
import BoundedGaps.Maynard.ConcreteIndependentMomentLimit
import BoundedGaps.Maynard.ConcreteS2FaceLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter MeasureTheory
open scoped BigOperators

/-!
# Corrected conditional good-outer S2 main limit

The exact SEM-375 scale factor is composed with the existing normalized
104-dimensional face limit. SEM-389 records that the shifted-prime factor
tends to `alpha`, not one, because `log R / log N` tends to `alpha`. The
shifted-prime asymptotic remains an explicit hypothesis; this file does not
assert a prime number theorem.
-/

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
theorem tendsto_engelsmaMaynardS2GoodOuterMain_div_scale
    {alpha : ℝ} (halpha : 0 < alpha)
    (hprime : ∀ m : BoundedGaps.engelsmaTuple,
      Tendsto
        (fun N : ℕ =>
          (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
            Real.log (engelsmaMaynardRadius alpha N))
        atTop (nhds alpha)) :
    Tendsto
      (fun N : ℕ =>
        engelsmaMaynardS2GoodOuterMain alpha N /
          engelsmaMaynardScale alpha N)
      atTop
      (nhds (alpha * ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
        engelsmaS2GoodOuterFaceLimit m)) := by
  have hratio :=
    (tendsto_log_engelsmaMaynardRadius_div_realRadius halpha).pow 105
  have hfactor : ∀ m : BoundedGaps.engelsmaTuple,
      Tendsto
        (fun N : ℕ =>
          (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
            Real.log (engelsmaMaynardRadius alpha N) *
              (Real.log (engelsmaMaynardRadius alpha N) /
                Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop (nhds alpha) := by
    intro m
    simpa [mul_assoc] using (hprime m).mul hratio
  have hterm : ∀ m : BoundedGaps.engelsmaTuple,
      Tendsto
        (fun N : ℕ =>
          (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
            normalizedEngelsmaS2CoordinateFiberGoodOuterMoment alpha N m *
            Real.log (engelsmaMaynardRadius alpha N) *
              (Real.log (engelsmaMaynardRadius alpha N) /
                Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop (nhds (alpha * engelsmaS2GoodOuterFaceLimit m)) := by
    intro m
    have hmoment :=
      tendsto_normalizedEngelsmaS2CoordinateFiberGoodOuterMoment halpha m
    have hmul := (hfactor m).mul hmoment
    simpa [engelsmaS2GoodOuterFaceLimit, mul_assoc, mul_left_comm, mul_comm]
      using hmul
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
            (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
              normalizedEngelsmaS2CoordinateFiberGoodOuterMoment alpha N m *
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
              normalizedEngelsmaS2CoordinateFiberGoodOuterMoment alpha N m *
              Real.log (engelsmaMaynardRadius alpha N) *
                (Real.log (engelsmaMaynardRadius alpha N) /
                  Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop
        (nhds (alpha * ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
          engelsmaS2GoodOuterFaceLimit m)) := by
    simpa [Finset.mul_sum] using hsum
  have hbridge : ∀ᶠ N : ℕ in atTop,
      engelsmaMaynardS2GoodOuterMain alpha N /
          engelsmaMaynardScale alpha N =
        ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
          (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
            normalizedEngelsmaS2CoordinateFiberGoodOuterMoment alpha N m *
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
    exact engelsmaMaynardS2GoodOuterMain_div_scale_eq hNpos hR hRreal
  apply hsum'.congr'
  filter_upwards [hbridge] with N hN
  exact hN.symm

end BoundedGaps.Maynard
