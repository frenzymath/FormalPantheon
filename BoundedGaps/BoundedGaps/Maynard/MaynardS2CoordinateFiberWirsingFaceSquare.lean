import BoundedGaps.Maynard.MaynardS2CoordinateFiberWirsingFace
import BoundedGaps.Maynard.MaynardS2CoordinateFiberOuterWeight

set_option maxRecDepth 6000

noncomputable section

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped BigOperators

/-!
# Pointwise square of the full-face S2 fiber estimate

SEM-392 squares the SEM-391 linear estimate and then divides it by the exact
tuple `g` product. The resulting error is pointwise and tuple-independent
apart from the normalized outer squarefree weight; summation is a later node.
-/

theorem exists_uniform_abs_maynardS2CoordinateFiberSum_sq_sub_faceIntegral_sq_le_wirsing :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
          {r : BoundedGaps.engelsmaTuple → ℕ},
        IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
          (primorial D) r →
        r m = 1 →
        2 ≤ Real.log R →
        1 < maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) →
        |maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
              (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
                engelsmaSmallKCandidate) m r ^ 2 -
            (maynardS2CoordinateFiberSingularSeries D m r * Real.log R *
              engelsmaS2CoordinateFiberFaceIntegral R m r) ^ 2| ≤
          maynardS2CoordinateFiberSingularSeries D m r ^ 2 *
            smallKCandidateBound ^ 2 *
              (132 * (K + Real.log D +
                (Real.log (Real.log R) + C + 2) + Real.log 2) +
                Real.log 3) *
              (2 * Real.log R +
                (132 * (K + Real.log D +
                  (Real.log (Real.log R) + C + 2) + Real.log 2) +
                  Real.log 3)) := by
  obtain ⟨K, C, hK, hC, hlinear⟩ :=
    exists_uniform_abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_faceIntegral_le_wirsing
  refine ⟨K, C, hK, hC, ?_⟩
  intro R D m r hr hrm hlogR hQ
  let Y : ℝ := maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
    (primorial D) (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
      engelsmaSmallKCandidate) m r
  let S : ℝ := maynardS2CoordinateFiberSingularSeries D m r
  let L : ℝ := Real.log R
  let J : ℝ := engelsmaS2CoordinateFiberFaceIntegral R m r
  let A : ℝ := 132 * (K + Real.log D +
    (Real.log (Real.log R) + C + 2) + Real.log 2) + Real.log 3
  let E : ℝ := S * smallKCandidateBound * A
  let M : ℝ := S * L * J
  have hS : 0 ≤ S := by
    dsimp [S]
    exact (maynardS2CoordinateFiberSingularSeries_pos m r hr).le
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hloglogR : 0 ≤ Real.log (Real.log R) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hS smallKCandidateBound_nonneg) hA
  have hYM : |Y - M| ≤ E := by
    simpa [Y, M, E, S, L, J, A] using hlinear m hr hrm hlogR hQ
  have hJ : |J| ≤ smallKCandidateBound := by
    simpa [J, engelsmaS2CoordinateFiberFaceIntegral, Real.norm_eq_abs] using
      smallKFaceInner_norm_le (engelsmaIndexEquiv m)
        (engelsmaS2OffCoordinateLogFacePoint R m r)
  have hM : |M| ≤ S * L * smallKCandidateBound := by
    rw [abs_mul, abs_mul, abs_of_nonneg hS, abs_of_nonneg hL]
    exact mul_le_mul_of_nonneg_left hJ (mul_nonneg hS hL)
  have hY : |Y| ≤ |M| + E := by
    calc
      |Y| = |(Y - M) + M| := by congr 1; ring
      _ ≤ |Y - M| + |M| := abs_add_le _ _
      _ ≤ E + |M| := add_le_add hYM le_rfl
      _ = |M| + E := by ring
  have hsum : |Y + M| ≤ 2 * (S * L * smallKCandidateBound) + E := by
    calc
      |Y + M| ≤ |Y| + |M| := abs_add_le _ _
      _ ≤ (|M| + E) + |M| := add_le_add hY le_rfl
      _ ≤ ((S * L * smallKCandidateBound) + E) +
          (S * L * smallKCandidateBound) := by gcongr
      _ = 2 * (S * L * smallKCandidateBound) + E := by ring
  change |Y ^ 2 - M ^ 2| ≤
    S ^ 2 * smallKCandidateBound ^ 2 * A * (2 * L + A)
  calc
    |Y ^ 2 - M ^ 2| = |Y - M| * |Y + M| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ E * (2 * (S * L * smallKCandidateBound) + E) :=
      mul_le_mul hYM hsum (abs_nonneg _) hE
    _ = S ^ 2 * smallKCandidateBound ^ 2 * A * (2 * L + A) := by
      simp only [E]
      ring

theorem exists_uniform_abs_maynardS2CoordinateFiberSum_sq_div_gProduct_sub_faceIntegral_sq_div_gProduct_le_wirsing :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
          {r : BoundedGaps.engelsmaTuple → ℕ},
        IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
          (primorial D) r →
        r m = 1 →
        2 ≤ Real.log R →
        1 < maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) →
        |maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R (primorial D)
              (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
                engelsmaSmallKCandidate) m r ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ) -
            (maynardS2CoordinateFiberSingularSeries D m r * Real.log R *
              engelsmaS2CoordinateFiberFaceIntegral R m r) ^ 2 /
              ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)| ≤
          preSieveSingularSeries D ^ 2 *
            maynardS2OuterSquarefreeAF (primorial D)
              (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) *
            (smallKCandidateBound ^ 2 *
              (132 * (K + Real.log D +
                (Real.log (Real.log R) + C + 2) + Real.log 2) +
                Real.log 3) *
              (2 * Real.log R +
                (132 * (K + Real.log D +
                  (Real.log (Real.log R) + C + 2) + Real.log 2) +
                  Real.log 3))) := by
  obtain ⟨K, C, hK, hC, hsquare⟩ :=
    exists_uniform_abs_maynardS2CoordinateFiberSum_sq_sub_faceIntegral_sq_le_wirsing
  refine ⟨K, C, hK, hC, ?_⟩
  intro R D m r hr hrm hlogR hQ
  let Y : ℝ := maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
    (primorial D) (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
      engelsmaSmallKCandidate) m r
  let S : ℝ := maynardS2CoordinateFiberSingularSeries D m r
  let L : ℝ := Real.log R
  let J : ℝ := engelsmaS2CoordinateFiberFaceIntegral R m r
  let G : ℝ := ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)
  let A : ℝ := 132 * (K + Real.log D +
    (Real.log (Real.log R) + C + 2) + Real.log 2) + Real.log 3
  let T : ℝ := smallKCandidateBound ^ 2 * A * (2 * L + A)
  have hG : 0 ≤ G := by
    dsimp [G]
    exact Finset.prod_nonneg fun h _ => Nat.cast_nonneg _
  have hsq : |Y ^ 2 - (S * L * J) ^ 2| ≤ S ^ 2 * T := by
    simpa [Y, S, L, J, T, A, mul_assoc] using
      hsquare m hr hrm hlogR hQ
  have hweight : S ^ 2 / G = preSieveSingularSeries D ^ 2 *
      maynardS2OuterSquarefreeAF (primorial D)
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) := by
    simpa [S, G] using
      maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
        m r hr hrm
  change |Y ^ 2 / G - (S * L * J) ^ 2 / G| ≤
    preSieveSingularSeries D ^ 2 *
      maynardS2OuterSquarefreeAF (primorial D)
        (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) * T
  calc
    |Y ^ 2 / G - (S * L * J) ^ 2 / G| =
        |Y ^ 2 - (S * L * J) ^ 2| / G := by
      rw [show Y ^ 2 / G - (S * L * J) ^ 2 / G =
        (Y ^ 2 - (S * L * J) ^ 2) / G by ring, abs_div,
        abs_of_nonneg hG]
    _ ≤ (S ^ 2 * T) / G := div_le_div_of_nonneg_right hsq hG
    _ = (S ^ 2 / G) * T := by ring
    _ = preSieveSingularSeries D ^ 2 *
        maynardS2OuterSquarefreeAF (primorial D)
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r) * T := by
      rw [hweight]

end BoundedGaps.Maynard
