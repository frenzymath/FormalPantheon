import BoundedGaps.Maynard.ConcreteS2GoodComplementOuterMoment
import BoundedGaps.Maynard.MaynardS2CoordinateFiberWirsingFaceSquare

set_option maxRecDepth 7000

noncomputable section

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped BigOperators

/-!
# Summed good-fiber full-face Wirsing estimate

SEM-393 sums the SEM-392 pointwise square estimate over the exact good
coordinate support. The main term is identified directly with the existing
complementary/full-face outer moment, so the endpoint loss is not counted
twice.
-/

theorem exists_uniform_abs_engelsmaS2CoordinateFiberGoodSquareDiagonal_sub_complementOuterMoment_le_wirsing :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ {R D : ℕ} (m : BoundedGaps.engelsmaTuple),
        2 ≤ Real.log R →
        |engelsmaS2CoordinateFiberGoodSquareDiagonal R D m -
            preSieveSingularSeries D ^ 2 *
              engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m| ≤
          preSieveSingularSeries D ^ 2 *
            (smallKCandidateBound ^ 2 *
              (132 * (K + Real.log D +
                (Real.log (Real.log R) + C + 2) + Real.log 2) +
                Real.log 3) *
              (2 * Real.log R +
                (132 * (K + Real.log D +
                  (Real.log (Real.log R) + C + 2) + Real.log 2) +
                  Real.log 3))) *
            ∏ _h ∈ Finset.univ.erase m,
              maynardS2OuterSquarefreeMean (primorial D) R := by
  obtain ⟨K, C, hK, hC, hpointwise⟩ :=
    exists_uniform_abs_maynardS2CoordinateFiberSum_sq_div_gProduct_sub_faceIntegral_sq_div_gProduct_le_wirsing
  refine ⟨K, C, hK, hC, ?_⟩
  intro R D m hlogR
  let G := engelsmaS2CoordinateFiberGoodSupport R D m
  let Y := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
      (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
        engelsmaSmallKCandidate) m r
  let g := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)
  let W := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    maynardS2OuterSquarefreeAF (primorial D)
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)
  let I := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    ∫ x in (0 : ℝ)..(
      1 - Real.log (maynardS2OffCoordinateProduct
        BoundedGaps.engelsmaTuple m r) / Real.log R),
      engelsmaS2CoordinateFiberPolynomialTest R m r x
  let P : ℝ := preSieveSingularSeries D ^ 2
  let H : ℝ := 132 * (K + Real.log D +
    (Real.log (Real.log R) + C + 2) + Real.log 2) + Real.log 3
  let T : ℝ := smallKCandidateBound ^ 2 * H * (2 * Real.log R + H)
  have hlogpos : 0 < Real.log R := by linarith
  have hRreal : (1 : ℝ) < (R : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg R)).mp hlogpos
  have hR : 1 < R := by exact_mod_cast hRreal
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hloglogR : 0 ≤ Real.log (Real.log R) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg smallKCandidateBound) hH)
      (add_nonneg (mul_nonneg (by norm_num) hlogpos.le) hH)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hfactor : 0 ≤ P * T := mul_nonneg hP hT
  have hpoint : ∀ r ∈ G,
      |Y r ^ 2 / g r - P * W r * (Real.log R * I r) ^ 2| ≤
        P * W r * T := by
    intro r hrMem
    have hrData := Finset.mem_filter.mp hrMem
    have hr := isMaynardDivisorTuple_of_mem_support hrData.1
    have hsquare := hpointwise m hr hrData.2.1 hlogR hrData.2.2
    have hface :=
      engelsmaS2CoordinateFiber_complementIntegral_eq_faceIntegral
        m hr hR hrData.2.1
    have hmain :
        (maynardS2CoordinateFiberSingularSeries D m r * Real.log R *
            engelsmaS2CoordinateFiberFaceIntegral R m r) ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ) =
          P * W r * (Real.log R * I r) ^ 2 := by
      have hweight :=
        maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
          m r hr hrData.2.1
      have hweight' :
          maynardS2CoordinateFiberSingularSeries D m r ^ 2 / g r =
            P * W r := by
        simpa [P, W, g] using hweight
      rw [← hface]
      change
        (maynardS2CoordinateFiberSingularSeries D m r * Real.log R * I r) ^ 2 /
            g r = P * W r * (Real.log R * I r) ^ 2
      calc
        (maynardS2CoordinateFiberSingularSeries D m r * Real.log R * I r) ^ 2 /
            g r =
          (maynardS2CoordinateFiberSingularSeries D m r ^ 2 / g r) *
            (Real.log R * I r) ^ 2 := by ring
        _ = P * W r * (Real.log R * I r) ^ 2 := by
          rw [hweight']
    rw [hmain] at hsquare
    simpa [Y, g, W, I, P, T, H, mul_assoc] using hsquare
  rw [engelsmaS2CoordinateFiberGoodSquareDiagonal,
    engelsmaS2CoordinateFiberGoodComplementOuterMoment,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  change |∑ r ∈ G,
    (Y r ^ 2 / g r - P * (W r * (Real.log R * I r) ^ 2))| ≤
      P * T * ∏ _h ∈ Finset.univ.erase m,
        maynardS2OuterSquarefreeMean (primorial D) R
  calc
    |∑ r ∈ G,
        (Y r ^ 2 / g r - P * (W r * (Real.log R * I r) ^ 2))| ≤
      ∑ r ∈ G,
        |Y r ^ 2 / g r - P * (W r * (Real.log R * I r) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ G, P * W r * T := by
      apply Finset.sum_le_sum
      intro r hrMem
      simpa [mul_assoc] using hpoint r hrMem
    _ = (P * T) * ∑ r ∈ G, W r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hrMem
      ring
    _ ≤ (P * T) * ∏ _h ∈ Finset.univ.erase m,
        maynardS2OuterSquarefreeMean (primorial D) R := by
      exact mul_le_mul_of_nonneg_left
        (engelsmaS2CoordinateFiberGoodOuterMass_le_faceBox R D m) hfactor

end BoundedGaps.Maynard
