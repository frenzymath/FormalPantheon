import BoundedGaps.Maynard.WirsingAllEndpoints
import BoundedGaps.Maynard.MaynardS2CoordinateFiberHarmonicBridge

noncomputable section

/-!
# Wirsing cumulative estimate for an S2 coordinate fiber

SEM-386 specializes the all-endpoint reciprocal-totient estimate to the exact
coordinate-fiber coefficient. The constant eleven includes the real-endpoint
natural-floor correction. Maynard's later source-level scalarization separately
retains its `r m = 1` hypothesis.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped ArithmeticFunction.Moebius BigOperators

theorem exists_uniform_abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_wirsing :
    ∃ K : ℝ, 0 < K ∧
      ∀ {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ),
        IsMaynardDivisorTuple H R (primorial D) r →
        ∀ {t : ℝ}, 1 ≤ t →
          |abelCumulative
                (maynardS2CoordinateFiberCoefficient H (primorial D) m r) t -
              maynardS2CoordinateFiberSingularSeries D m r * Real.log t| ≤
            11 * maynardS2CoordinateFiberSingularSeries D m r *
              (K + Real.log D +
                primeLogDivisorMass
                  (maynardS2OffCoordinateProduct H m r) + Real.log 2) := by
  obtain ⟨K, hK, hmean⟩ :=
    exists_uniform_abs_squarefreeCoprimeInvTotientMean_sub_density_log_le
  refine ⟨K, hK, ?_⟩
  intro H D R m r hr t ht
  let P : ℕ := maynardS2OffCoordinateProduct H m r
  let W : ℕ := primorial D * P
  let q : ℕ := ⌊t⌋₊
  let S : ℝ := maynardS2CoordinateFiberSingularSeries D m r
  let B : ℝ := K + Real.log D + primeLogDivisorMass P + Real.log 2
  have hP : 0 < P := by
    dsimp [P]
    exact maynardS2OffCoordinateProduct_pos m r hr
  have hSqP : Squarefree P := by
    dsimp [P]
    exact maynardS2OffCoordinateProduct_squarefree m r hr
  have hcop : Nat.Coprime (primorial D) P := by
    dsimp [P]
    exact maynardS2OffCoordinateProduct_coprime m r hr
  have hSqW : Squarefree W := by
    dsimp [W]
    exact (Nat.squarefree_mul hcop).mpr ⟨squarefree_primorial D, hSqP⟩
  have hDensity : coprimeHarmonicDensity W = S := by
    simpa [W, P, S] using
      (coprimeHarmonicDensity_augmented_eq_coordinateFiberSingularSeries
        m r hr)
  have hS : 0 < S := by
    dsimp [S]
    exact maynardS2CoordinateFiberSingularSeries_pos m r hr
  have hmeanBound := hmean (D := D) (P := P) (Q := q) hP hSqW
  rw [hDensity] at hmeanBound
  have hmeanBound' :
      |squarefreeCoprimeInvTotientMean W q - S * Real.log q| ≤
        10 * S * B := by
    simpa [W, P, B] using hmeanBound
  have hfloor := abs_log_natFloor_sub_log_le_log_two_global ht
  have hfloorTerm :
      |S * Real.log q - S * Real.log t| ≤ S * Real.log 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hS.le]
    exact mul_le_mul_of_nonneg_left (by simpa [q] using hfloor) hS.le
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hmass : 0 ≤ primeLogDivisorMass P := by
    unfold primeLogDivisorMass
    positivity
  have hlog2B : Real.log 2 ≤ B := by
    dsimp [B]
    linarith
  have hfloorB : S * Real.log 2 ≤ S * B :=
    mul_le_mul_of_nonneg_left hlog2B hS.le
  rw [abelCumulative_maynardS2CoordinateFiberCoefficient_eq_mean]
  change |squarefreeCoprimeInvTotientMean W q - S * Real.log t| ≤ _
  calc
    |squarefreeCoprimeInvTotientMean W q - S * Real.log t| =
        |(squarefreeCoprimeInvTotientMean W q - S * Real.log q) +
          (S * Real.log q - S * Real.log t)| := by ring_nf
    _ ≤ |squarefreeCoprimeInvTotientMean W q - S * Real.log q| +
          |S * Real.log q - S * Real.log t| := abs_add_le _ _
    _ ≤ 10 * S * B + S * Real.log 2 :=
      add_le_add hmeanBound' hfloorTerm
    _ ≤ 11 * S * B := by linarith
    _ = 11 * maynardS2CoordinateFiberSingularSeries D m r *
        (K + Real.log D +
          primeLogDivisorMass
            (maynardS2OffCoordinateProduct H m r) + Real.log 2) := by
      rfl

end BoundedGaps.Maynard
