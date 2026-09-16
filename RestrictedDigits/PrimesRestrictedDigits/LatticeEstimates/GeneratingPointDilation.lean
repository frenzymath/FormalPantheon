import PrimesRestrictedDigits.LatticeEstimates.AngleVector
import PrimesRestrictedDigits.LatticeEstimates.DirectionalDilation
import PrimesRestrictedDigits.LatticeEstimates.GeneratingPoints
import Mathlib.Tactic.FieldSimp

/-!
# Dilation bounds for the generating-point carrier

This proves the radius-`2*N` image bound in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 14.1.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Exact norm of projection onto a nonzero real line. -/
theorem norm_lineProjection_eq_abs_inner_div_norm
    (u : E) (hu : u ≠ 0) (x : E) :
    ‖lineProjection u x‖ = |inner Real u x| / ‖u‖ := by
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [lineProjection_apply, norm_smul, Real.norm_eq_abs, abs_div,
    abs_pow, abs_norm]
  field_simp

/-- Every source point has projected component of norm at most `delta`. -/
theorem norm_lineProjection_latticeAngleVector_le
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (delta N : Real) (hdelta : 0 < delta) (hN : 0 <= N)
    (Lambda : RankTwoIntegralLattice) {z : Fin 3 -> Int}
    (hz : z ∈ latticeGeneratingIntegerPoints a1 a2 Lambda delta N) :
    ‖lineProjection (latticeAngleVector a1 a2)
        (intVectorToEuclidean z)‖ <= delta := by
  have hA0 := latticeAngleVector_ne_zero hX a1 a2
  have hANorm : (0 : Real) < ‖latticeAngleVector a1 a2‖ :=
    norm_pos_iff.mpr hA0
  have hmem := (mem_latticeGeneratingIntegerPoints hN).mp hz
  have hdot :
      |inner Real (latticeAngleVector a1 a2) (intVectorToEuclidean z)| <=
        delta * (X : Real) := by
    rw [real_inner_comm]
    simpa [intVectorDot_angle_cast_eq_inner] using hmem.2.2
  have hXNorm := cast_le_norm_latticeAngleVector a1 a2
  rw [norm_lineProjection_eq_abs_inner_div_norm _ hA0]
  apply (div_le_iff₀ hANorm).2
  calc
    |inner Real (latticeAngleVector a1 a2) (intVectorToEuclidean z)| <=
        delta * (X : Real) := hdot
    _ <= delta * ‖latticeAngleVector a1 a2‖ :=
      mul_le_mul_of_nonneg_left hXNorm hdelta.le

/-- Directional dilation sends every generating point into the ball of radius
`2*N`, even when the dilation factor is below one. -/
theorem norm_directionalDilation_generatingPoint_le
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (delta N : Real) (hdelta : 0 < delta) (hN : 0 < N)
    (Lambda : RankTwoIntegralLattice) {z : Fin 3 -> Int}
    (hz : z ∈ latticeGeneratingIntegerPoints a1 a2 Lambda delta N) :
    ‖directionalDilation (latticeAngleVector a1 a2) (N / delta)
        (latticeAngleVector_ne_zero hX a1 a2) (div_ne_zero hN.ne' hdelta.ne')
        (intVectorToEuclidean z)‖ <= 2 * N := by
  have hscale : 0 <= N / delta := (div_pos hN hdelta).le
  calc
    ‖directionalDilation (latticeAngleVector a1 a2) (N / delta)
        (latticeAngleVector_ne_zero hX a1 a2) (div_ne_zero hN.ne' hdelta.ne')
        (intVectorToEuclidean z)‖ <=
      ‖intVectorToEuclidean z‖ +
        (N / delta) *
          ‖lineProjection (latticeAngleVector a1 a2)
            (intVectorToEuclidean z)‖ :=
      norm_directionalDilation_le _ _ _ (div_pos hN hdelta) _
    _ <= N + (N / delta) * delta := by
      apply add_le_add
      · exact ((mem_latticeGeneratingIntegerPoints hN.le).mp hz).2.1
      · exact mul_le_mul_of_nonneg_left
          (norm_lineProjection_latticeAngleVector_le
            hX a1 a2 delta N hdelta hN.le Lambda hz) hscale
    _ = 2 * N := by
      field_simp [hdelta.ne']
      ring

end PrimesRestrictedDigits
