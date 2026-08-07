import BoundedGaps.Maynard.MaynardS2CoordinateFiberWirsing
import BoundedGaps.Maynard.ConcreteRoughModulusPrimeLogMass

noncomputable section

/-!
# Logarithmic-radius S2 coordinate-fiber cumulative estimate

SEM-387 inserts the rough-modulus prime-log mass bound into SEM-386. The
explicit bracket is `log D + O(log log R)`; Maynard's later parameter choices
are needed before rewriting it purely on the `N` scale.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

theorem exists_uniform_abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_logarithmic :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ),
        IsMaynardDivisorTuple H R (primorial D) r →
        2 ≤ Real.log R →
        ∀ {t : ℝ}, 1 ≤ t →
          |abelCumulative
                (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
              maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
            11 * maynardS2CoordinateFiberSingularSeries D m r *
              (K + Real.log D +
                (Real.log (Real.log R) + C + 2) + Real.log 2) := by
  obtain ⟨K, hK, hcum⟩ :=
    exists_uniform_abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_wirsing
  obtain ⟨C₀, hmass⟩ := exists_uniform_primeLogDivisorMass_le_log_log_add
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right C₀ 0
  refine ⟨K, C, hK, hC, ?_⟩
  intro H D R m r hr hlogR t ht
  let P : ℕ := maynardS2OffCoordinateProduct H m r
  have hP : 0 < P := by
    dsimp [P]
    exact maynardS2OffCoordinateProduct_pos m r hr
  have hSqP : Squarefree P := by
    dsimp [P]
    exact maynardS2OffCoordinateProduct_squarefree m r hr
  have hPR : P < R := by
    dsimp [P]
    exact maynardS2OffCoordinateProduct_lt m r hr
  have hmass₀ := hmass hP hSqP hPR hlogR
  have hmassC :
      primeLogDivisorMass P ≤ Real.log (Real.log R) + C + 2 := by
    have hC₀ : C₀ ≤ C := le_max_left C₀ 0
    linarith
  have hbase := hcum m r hr ht
  have hS : 0 ≤ maynardS2CoordinateFiberSingularSeries D m r :=
    (maynardS2CoordinateFiberSingularSeries_pos m r hr).le
  have hfactor : 0 ≤ 11 * maynardS2CoordinateFiberSingularSeries D m r :=
    mul_nonneg (by norm_num) hS
  exact hbase.trans (mul_le_mul_of_nonneg_left (by
    dsimp [P, C] at hmassC ⊢
    linarith) hfactor)

end BoundedGaps.Maynard
