import BoundedGaps.Maynard.ConcreteS2ComplementFaceIdentification
import BoundedGaps.Maynard.MaynardS2CoordinateFiberPolynomialVariation
import BoundedGaps.Maynard.MaynardS2CoordinateFiberWirsingAbel

set_option maxRecDepth 5000

noncomputable section

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped BigOperators

/-!
# Full-face Wirsing--Abel estimate for an S2 coordinate fiber

SEM-391 combines the strict-endpoint Wirsing--Abel estimate with the concrete
polynomial variation bound and the independently verified simplex-support
identification. The result is still linear and pointwise in the outer divisor
tuple; squaring and summing are later steps.
-/

theorem abs_engelsmaS2CoordinateFiber_endpointIntegral_sub_faceIntegral_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hrm : r m = 1) (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    |(∫ x in (0 : ℝ)..(
        Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple m r)) / Real.log R),
        engelsmaS2CoordinateFiberPolynomialTest R m r x) -
      engelsmaS2CoordinateFiberFaceIntegral R m r| ≤
      smallKCandidateBound * (Real.log 3 / Real.log R) := by
  rw [← engelsmaS2CoordinateFiber_complementIntegral_eq_faceIntegral
    m hr hR hrm]
  exact abs_engelsmaS2CoordinateFiber_endpointIntegral_sub_complementIntegral_le
    m hr hR hQ

theorem exists_uniform_abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_faceIntegral_le_wirsing :
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
                engelsmaSmallKCandidate) m r -
            maynardS2CoordinateFiberSingularSeries D m r * Real.log R *
              engelsmaS2CoordinateFiberFaceIntegral R m r| ≤
          maynardS2CoordinateFiberSingularSeries D m r *
            smallKCandidateBound *
              (132 * (K + Real.log D +
                (Real.log (Real.log R) + C + 2) + Real.log 2) +
                Real.log 3) := by
  obtain ⟨K, C, hK, hC, habel⟩ :=
    exists_uniform_abs_maynardS2CoordinateFiberSum_engelsmaSmallK_sub_integral_le_wirsing
  refine ⟨K, C, hK, hC, ?_⟩
  intro R D m r hr hrm hlogR hQ
  let Y : ℝ := maynardS2CoordinateFiberSum BoundedGaps.engelsmaTuple R
    (primorial D) (maynardYValue BoundedGaps.engelsmaTuple R (primorial D)
      engelsmaSmallKCandidate) m r
  let S : ℝ := maynardS2CoordinateFiberSingularSeries D m r
  let L : ℝ := Real.log R
  let I : ℝ := ∫ x in (0 : ℝ)..(
    Real.log (maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
      Real.log R), engelsmaS2CoordinateFiberPolynomialTest R m r x
  let J : ℝ := engelsmaS2CoordinateFiberFaceIntegral R m r
  let B : ℝ := K + Real.log D +
    (Real.log (Real.log R) + C + 2) + Real.log 2
  let V : ℝ :=
    |engelsmaS2CoordinateFiberPolynomialTest R m r
        (Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple m r)) / Real.log R)| +
      ∫ t in Set.Ioc (1 : ℝ)
          (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)),
        |deriv (fun z => engelsmaS2CoordinateFiberPolynomialTest R m r
          (Real.log z / Real.log R)) t|
  have hP : 0 < maynardS2OffCoordinateProduct
      BoundedGaps.engelsmaTuple m r :=
    maynardS2OffCoordinateProduct_pos m r hr
  have hPR : maynardS2OffCoordinateProduct
      BoundedGaps.engelsmaTuple m r < R :=
    maynardS2OffCoordinateProduct_lt m r hr
  have hR : 1 < R := by omega
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hR)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact (maynardS2CoordinateFiberSingularSeries_pos m r hr).le
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hloglogR : 0 ≤ Real.log (Real.log R) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith
  have hA : 0 ≤ 11 * S * B := by positivity
  have habel' : |Y - S * L * I| ≤ (11 * S * B) * V := by
    simpa [Y, S, L, I, B, V] using habel m hr hrm hlogR hQ
  have hvariation : V ≤ 12 * smallKCandidateBound := by
    simpa [V] using
      (engelsmaS2CoordinateFiberPolynomial_endpoint_add_variation_le
        m hr hR hQ)
  have htruncated : |Y - S * L * I| ≤
      S * smallKCandidateBound * (132 * B) := by
    calc
      |Y - S * L * I| ≤ (11 * S * B) * V := habel'
      _ ≤ (11 * S * B) * (12 * smallKCandidateBound) :=
        mul_le_mul_of_nonneg_left hvariation hA
      _ = S * smallKCandidateBound * (132 * B) := by ring
  have hendpoint : |I - J| ≤
      smallKCandidateBound * (Real.log 3 / L) := by
    simpa [I, J, L] using
      (abs_engelsmaS2CoordinateFiber_endpointIntegral_sub_faceIntegral_le
        m hr hrm hR hQ)
  have hmain : |S * L * I - S * L * J| ≤
      S * smallKCandidateBound * Real.log 3 := by
    calc
      |S * L * I - S * L * J| = (S * L) * |I - J| := by
        rw [show S * L * I - S * L * J = (S * L) * (I - J) by ring,
          abs_mul, abs_of_nonneg (mul_nonneg hS hL.le)]
      _ ≤ (S * L) * (smallKCandidateBound * (Real.log 3 / L)) :=
        mul_le_mul_of_nonneg_left hendpoint (mul_nonneg hS hL.le)
      _ = S * smallKCandidateBound * Real.log 3 := by
        field_simp [hL.ne']
  change |Y - S * L * J| ≤ S * smallKCandidateBound * (132 * B + Real.log 3)
  calc
    |Y - S * L * J| = |(Y - S * L * I) +
        (S * L * I - S * L * J)| := by
      congr 1
      ring
    _ ≤ |Y - S * L * I| + |S * L * I - S * L * J| :=
      abs_add_le _ _
    _ ≤ S * smallKCandidateBound * (132 * B) +
        S * smallKCandidateBound * Real.log 3 :=
      add_le_add htruncated hmain
    _ = S * smallKCandidateBound * (132 * B + Real.log 3) := by ring

end BoundedGaps.Maynard
