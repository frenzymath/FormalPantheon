import BoundedGaps.Maynard.ConcreteS2MainPNTComposition
import BoundedGaps.Maynard.ConcreteS2FaceLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

/-!
# Conditional full S2 limit at Maynard's numerator target

This thin consumer rewrites the SEM-405 face-functional target using the exact
SEM-403 finite numerator identity.  It introduces no new analytic input.
-/

theorem tendsto_engelsmaMaynardS2Main_div_scale_of_pnt_eq_maynardNumerator
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
        (∑ m : Fin 105, maynardJ 105 m smallKCandidate))) := by
  have hmain := tendsto_engelsmaMaynardS2Main_div_scale_of_pnt
    halpha hpnt
  rw [sum_engelsmaS2GoodOuterFaceLimit_eq_maynardNumerator] at hmain
  exact hmain

#print axioms
  tendsto_engelsmaMaynardS2Main_div_scale_of_pnt_eq_maynardNumerator

end BoundedGaps.Maynard
