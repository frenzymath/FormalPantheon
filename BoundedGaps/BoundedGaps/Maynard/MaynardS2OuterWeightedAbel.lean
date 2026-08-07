import BoundedGaps.Maynard.MaynardS2OuterCumulative
import BoundedGaps.Maynard.NormalizedWeightedAbel

noncomputable section

/-!
# Normalized weighted Abel transfer for the S2 outer coefficient

Maynard2013v3, source lines 550--560, applies partial summation after the
outer squarefree cumulative estimate.  This file supplies that exact finite
transfer, leaving all calculus premises explicit.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real

theorem abs_maynardS2OuterWeightedSum_sub_normalizedLogIntegral_le
    {D R : ℕ} (hD : 2 ≤ D) (hR : 1 < R)
    {G : ℝ → ℝ} (hG : Continuous G)
    (hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) R,
      HasDerivAt (fun t => G (Real.log t / Real.log R))
        (deriv (fun t => G (Real.log t / Real.log R)) x) x)
    (hfDerivInt : IntervalIntegrable
      (deriv (fun t => G (Real.log t / Real.log R))) volume 1 R)
    (hfInt : IntegrableOn
      (deriv (fun t => G (Real.log t / Real.log R)))
      (Set.Icc (1 : ℝ) R))
    (hfNormInt : IntegrableOn
      (fun t => |deriv (fun t => G (Real.log t / Real.log R)) t|)
      (Set.Ioc (1 : ℝ) R))
    (hmainInt : IntegrableOn
      (fun t => deriv (fun t => G (Real.log t / Real.log R)) t *
        (maynardS2OuterSingularSeries D * Real.log t))
      (Set.Ioc (1 : ℝ) R))
    {V : ℝ}
    (hvariation : (∫ t in Set.Ioc (1 : ℝ) R,
      |deriv (fun t => G (Real.log t / Real.log R)) t|) ≤
      V) :
    |(∑ k ∈ Finset.Icc 0 R,
        G (Real.log k / Real.log R) *
          maynardS2OuterSquarefreeAF (primorial D) k) -
        maynardS2OuterSingularSeries D * Real.log R *
          (∫ x in (0 : ℝ)..1, G x)| ≤
      maynardS2OuterCumulativeError D *
        (|G 1| + V) := by
  have hE := maynardS2OuterCumulativeError_nonneg hD
  have hc0 : maynardS2OuterSquarefreeAF (primorial D) 0 = 0 := by
    exact (maynardS2OuterSquarefreeAF (primorial D)).map_zero
  have happrox : ∀ t ∈ Set.Icc (1 : ℝ) R,
      |abelCumulative (maynardS2OuterSquarefreeAF (primorial D)) t -
          maynardS2OuterSingularSeries D * Real.log t| ≤
        maynardS2OuterCumulativeError D := by
    intro t ht
    exact abs_abelCumulative_maynardS2OuterSquarefreeAF_sub_log_le
      hD ht.1
  exact abs_weightedSum_sub_normalizedLogIntegral_le hR hc0 hE hG
    hfDeriv hfDerivInt hfInt hfNormInt hmainInt happrox hvariation

end BoundedGaps.Maynard
