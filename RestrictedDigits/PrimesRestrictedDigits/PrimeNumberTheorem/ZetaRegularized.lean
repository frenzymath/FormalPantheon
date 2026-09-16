import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Riemann zeta function regularized at one

This removes the simple pole of the Riemann zeta function at one using its
residue-one normalization. The resulting entire function supplies the sharp
pole term needed in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorems 6.6--6.7.
-/

open Complex Filter Set

namespace PrimesRestrictedDigits

/-- The entire extension of `(s - 1) * ζ(s)` across `s = 1`. -/
noncomputable def regularizedRiemannZeta : Complex → Complex :=
  Function.update (fun w : Complex => (w - 1) * riemannZeta w) 1 1

@[simp]
theorem regularizedRiemannZeta_one : regularizedRiemannZeta 1 = 1 := by
  simp [regularizedRiemannZeta]

theorem regularizedRiemannZeta_apply_of_ne {s : Complex} (hs : s ≠ 1) :
    regularizedRiemannZeta s = (s - 1) * riemannZeta s := by
  exact Function.update_of_ne hs _ _

/-- The residue-one theorem removes the only possible singularity of
`(s - 1) * ζ(s)`. -/
theorem differentiable_regularizedRiemannZeta :
    Differentiable Complex regularizedRiemannZeta := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · apply DifferentiableAt.congr_of_eventuallyEq
    · exact (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
    · filter_upwards [eventually_ne_nhds hs] with w hw
      exact regularizedRiemannZeta_apply_of_ne hw
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      apply DifferentiableAt.congr_of_eventuallyEq
      · exact (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hw)
      · filter_upwards [eventually_ne_nhds hw] with v hv
        exact regularizedRiemannZeta_apply_of_ne hv
    · simpa only [regularizedRiemannZeta, continuousAt_update_same] using
        riemannZeta_residue_one

/-- The regularized zeta function is entire. -/
theorem analyticOnNhd_regularizedRiemannZeta :
    AnalyticOnNhd Complex regularizedRiemannZeta univ :=
  analyticOnNhd_univ_iff_differentiable.mpr differentiable_regularizedRiemannZeta

/-- Away from the pole and zeros of zeta, logarithmic differentiation of
`(s - 1) * ζ(s)` separates the pole term from the zeta logarithmic derivative. -/
theorem logDeriv_regularizedRiemannZeta_eq {s : Complex} (hs : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv regularizedRiemannZeta s =
      1 / (s - 1) + logDeriv riemannZeta s := by
  have hEqNhd : regularizedRiemannZeta =ᶠ[nhds s]
      fun w : Complex => (w - 1) * riemannZeta w := by
    filter_upwards [eventually_ne_nhds hs] with w hw
    exact regularizedRiemannZeta_apply_of_ne hw
  have hEq : regularizedRiemannZeta s = (s - 1) * riemannZeta s :=
    regularizedRiemannZeta_apply_of_ne hs
  calc
    logDeriv regularizedRiemannZeta s =
        logDeriv (fun w : Complex => (w - 1) * riemannZeta w) s := by
      simp only [logDeriv_apply, hEqNhd.deriv_eq, hEq]
    _ = logDeriv (fun w : Complex => w - 1) s + logDeriv riemannZeta s :=
      logDeriv_mul s (sub_ne_zero.mpr hs) hzeta
        (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs)
    _ = 1 / (s - 1) + logDeriv riemannZeta s := by
      simp [logDeriv_apply]

end PrimesRestrictedDigits
