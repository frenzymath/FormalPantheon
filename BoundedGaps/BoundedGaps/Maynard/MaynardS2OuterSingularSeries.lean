import BoundedGaps.Maynard.MaynardS2OuterInfiniteSingularTail
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

/-!
# Complete S2 outer singular series

Maynard2013v3, source lines 552--560, uses the full GGPY singular density for
the outer weight.  This file identifies it as the pre-sieve density times the
convergent SEM-260 tail and records its finite-prefix convergence.
-/

namespace BoundedGaps.Maynard

open Filter

noncomputable def maynardS2OuterSingularSeries (D : ℕ) : ℝ :=
  preSieveSingularSeries D * maynardS2OuterInfiniteSingularTail D

theorem tendsto_maynardS2OuterFiniteSingularSeries
    {D : ℕ} (hD : 2 ≤ D) :
    Tendsto (fun Q => maynardS2OuterFiniteSingularSeries D Q) atTop
      (nhds (maynardS2OuterSingularSeries D)) := by
  have htail := (tendsto_maynardS2OuterSingularTail hD).comp
    (tendsto_add_atTop_nat 1)
  have hscaled := htail.const_mul (preSieveSingularSeries D)
  unfold maynardS2OuterSingularSeries
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop D] with Q hDQ
  exact (maynardS2OuterFiniteSingularSeries_eq hDQ).symm

theorem abs_maynardS2OuterSingularSeries_sub_preSieve_le
    {D : ℕ} (hD : 2 ≤ D) :
    |maynardS2OuterSingularSeries D - preSieveSingularSeries D| ≤
      preSieveSingularSeries D * (8 / (D : ℝ)) := by
  unfold maynardS2OuterSingularSeries
  have hS : 0 ≤ preSieveSingularSeries D :=
    (preSieveSingularSeries_pos_from_totient D).le
  rw [show preSieveSingularSeries D *
      maynardS2OuterInfiniteSingularTail D - preSieveSingularSeries D =
      preSieveSingularSeries D *
        (maynardS2OuterInfiniteSingularTail D - 1) by ring,
    abs_mul, abs_of_nonneg hS]
  exact mul_le_mul_of_nonneg_left
    (abs_maynardS2OuterInfiniteSingularTail_sub_one_le hD) hS

theorem abs_maynardS2OuterSingularSeries_div_preSieve_sub_one_le
    {D : ℕ} (hD : 2 ≤ D) :
    |maynardS2OuterSingularSeries D / preSieveSingularSeries D - 1| ≤
      8 / (D : ℝ) := by
  unfold maynardS2OuterSingularSeries
  have hS := preSieveSingularSeries_pos_from_totient D
  rw [mul_div_cancel_left₀ _ hS.ne']
  exact abs_maynardS2OuterInfiniteSingularTail_sub_one_le hD

end BoundedGaps.Maynard
