import BoundedGaps.Maynard.ConcreteScalarEndpointZero

noncomputable section

namespace BoundedGaps.Maynard

open Filter Metric

theorem eventually_engelsmaSquarefreeMean_fractionalRadius_finset
    {alpha : ℝ} (halpha : 0 < alpha) (B : Finset ℝ)
    (hB : ∀ beta ∈ B, 0 ≤ beta) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ beta ∈ B,
      |squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) - beta| < epsilon := by
  apply B.eventually_all.mpr
  intro beta hbeta
  by_cases hzero : beta = 0
  · subst beta
    have hzeroLimit := tendsto_engelsmaSquarefreeMean_zeroEndpoint halpha
    have hev := hzeroLimit.eventually
      (Metric.ball_mem_nhds (0 : ℝ) hepsilon)
    filter_upwards [hev] with N hN
    simpa only [Real.dist_eq, sub_zero, mul_zero] using hN
  · have hbeta : 0 < beta :=
      lt_of_le_of_ne (hB beta hbeta) (Ne.symm hzero)
    have hlimit := tendsto_engelsmaSquarefreeMean_fractionalRadius halpha hbeta
    have hev := hlimit.eventually (Metric.ball_mem_nhds beta hepsilon)
    filter_upwards [hev] with N hN
    simpa only [Real.dist_eq, abs_sub_comm] using hN

end BoundedGaps.Maynard
