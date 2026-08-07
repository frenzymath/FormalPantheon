import BoundedGaps.Maynard.ConcreteS2EndpointIntegral

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory

set_option maxRecDepth 5000 in
theorem abs_sq_log_mul_engelsmaS2CoordinateFiber_endpointIntegral_sub_complementIntegral_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r) (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    |((Real.log R) *
        (∫ x in (0 : ℝ)..(
          Real.log (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct
              BoundedGaps.engelsmaTuple m r)) / Real.log R),
          engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2 -
      ((Real.log R) *
        (∫ x in (0 : ℝ)..(
          1 - Real.log (maynardS2OffCoordinateProduct
            BoundedGaps.engelsmaTuple m r) / Real.log R),
          engelsmaS2CoordinateFiberPolynomialTest R m r x)) ^ 2| ≤
      (smallKCandidateBound * Real.log 3) *
        (2 * (Real.log R * smallKCandidateBound) +
          smallKCandidateBound * Real.log 3) := by
  let I : ℝ := ∫ x in (0 : ℝ)..(
      Real.log (maynardS2CoordinateFiberEndpoint R
        (maynardS2OffCoordinateProduct
          BoundedGaps.engelsmaTuple m r)) / Real.log R),
      engelsmaS2CoordinateFiberPolynomialTest R m r x
  let J : ℝ := ∫ x in (0 : ℝ)..(
      1 - Real.log (maynardS2OffCoordinateProduct
        BoundedGaps.engelsmaTuple m r) / Real.log R),
      engelsmaS2CoordinateFiberPolynomialTest R m r x
  let A := Real.log R * I
  let B := Real.log R * J
  let E := smallKCandidateBound * Real.log 3
  let M := Real.log R * smallKCandidateBound
  have hRlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hM : 0 ≤ M := mul_nonneg hRlog.le smallKCandidateBound_nonneg
  have hE : 0 ≤ E := mul_nonneg smallKCandidateBound_nonneg
    (Real.log_nonneg (by norm_num))
  have hIJs :=
    abs_engelsmaS2CoordinateFiber_endpointIntegral_sub_complementIntegral_le
      (m := m) (r := r) hr hR hQ
  have hIJ : |I - J| ≤
      smallKCandidateBound * (Real.log 3 / Real.log R) := by
    simpa [I, J] using hIJs
  have hAB : |A - B| ≤ E := by
    calc
      |A - B| = Real.log R * |I - J| := by
        rw [show A - B = Real.log R * (I - J) by simp [A, B]; ring,
          abs_mul, abs_of_nonneg hRlog.le]
      _ ≤ Real.log R *
          (smallKCandidateBound * (Real.log 3 / Real.log R)) :=
        mul_le_mul_of_nonneg_left hIJ hRlog.le
      _ = E := by
        field_simp [E, hRlog.ne']
        ring
  have hAsq :=
    sq_log_mul_engelsmaS2CoordinateFiberPolynomialTest_intervalIntegral_le
      (m := m) (r := r) hr hR hQ
  have hA : |A| ≤ M := by
    have hsq : |A| ^ 2 ≤ M ^ 2 := by
      rw [sq_abs]
      simpa [A, I, M] using hAsq
    exact (sq_le_sq₀ (abs_nonneg A) hM).mp hsq
  have hB : |B| ≤ M + E := by
    calc
      |B| = |(B - A) + A| := by congr 1; ring
      _ ≤ |B - A| + |A| := abs_add_le _ _
      _ = |A - B| + |A| := by rw [abs_sub_comm]
      _ ≤ E + M := add_le_add hAB hA
      _ = M + E := by ring
  have hsum : |A + B| ≤ 2 * M + E := by
    calc
      |A + B| ≤ |A| + |B| := abs_add_le _ _
      _ ≤ M + (M + E) := add_le_add hA hB
      _ = 2 * M + E := by ring
  change |A ^ 2 - B ^ 2| ≤ E * (2 * M + E)
  calc
    |A ^ 2 - B ^ 2| = |(A - B) * (A + B)| := by congr 1; ring
    _ = |A - B| * |A + B| := abs_mul _ _
    _ ≤ E * (2 * M + E) :=
      mul_le_mul hAB hsum (abs_nonneg _) hE

end BoundedGaps.Maynard
