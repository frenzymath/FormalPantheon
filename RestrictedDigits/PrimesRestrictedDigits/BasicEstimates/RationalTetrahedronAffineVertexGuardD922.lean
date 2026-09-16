import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronSubdivisionD918
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # RationalTetrahedronAffineVertexGuardD922 -/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

/-!
Vertex-checkable affine guards for a rational tetrahedron. The chamber constraints are affine,
so checking their four rational vertices suffices for every point in the closed barycentric
region.
-/

theorem RationalAffine.evalReal_barycentricPoint3
    (affine : RationalAffine 3) (vertex : Fin 4 → Fin 3 → Real)
    (w : Fin 4 → Real) (hsum : ∑ i, w i = 1) :
    affine.evalReal (barycentricPoint3 vertex w) =
      ∑ i, w i * affine.evalReal (vertex i) := by
  unfold RationalAffine.evalReal barycentricPoint3 barycentricCoordinate3
  change affine.constant +
      ∑ j, (affine.coefficient j : Real) *
        (∑ i, w i * vertex i j) =
    ∑ i, w i *
      ((affine.constant : Real) +
        ∑ j, (affine.coefficient j : Real) * vertex i j)
  have hdouble :
      ∑ j, (affine.coefficient j : Real) *
          (∑ i, w i * vertex i j) =
        ∑ i, w i *
          (∑ j, (affine.coefficient j : Real) * vertex i j) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hdouble]
  calc
    affine.constant +
        ∑ i, w i *
          (∑ j, (affine.coefficient j : Real) * vertex i j) =
      (∑ i, w i) * affine.constant +
        ∑ i, w i *
          (∑ j, (affine.coefficient j : Real) * vertex i j) := by
      rw [hsum]
      ring
    _ = (∑ i, w i * affine.constant) +
        ∑ i, w i *
          (∑ j, (affine.coefficient j : Real) * vertex i j) := by
      rw [Finset.sum_mul]
    _ = ∑ i, (w i * affine.constant +
        w i * (∑ j, (affine.coefficient j : Real) * vertex i j)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i, w i *
        ((affine.constant : Real) +
          ∑ j, (affine.coefficient j : Real) * vertex i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem RationalTetrahedron.affine_eval_le_of_vertices
    (T : RationalTetrahedron) (affine : RationalAffine 3)
    {bound : Real}
    (hvertex : ∀ i, affine.evalReal (T.vertexReal i) ≤ bound) :
    ∀ x ∈ T.region, affine.evalReal x ≤ bound := by
  intro x hx
  rcases hx with ⟨w, hw, hsum, rfl⟩
  rw [affine.evalReal_barycentricPoint3 T.vertexReal w hsum]
  have hweighted :
      (∑ i, w i * affine.evalReal (T.vertexReal i)) ≤
        ∑ i, w i * bound := by
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hvertex i) (hw i)
  rw [← Finset.sum_mul, hsum, one_mul] at hweighted
  exact hweighted

theorem RationalTetrahedron.affine_eval_ge_of_vertices
    (T : RationalTetrahedron) (affine : RationalAffine 3)
    {bound : Real}
    (hvertex : ∀ i, bound ≤ affine.evalReal (T.vertexReal i)) :
    ∀ x ∈ T.region, bound ≤ affine.evalReal x := by
  intro x hx
  rcases hx with ⟨w, hw, hsum, rfl⟩
  rw [affine.evalReal_barycentricPoint3 T.vertexReal w hsum]
  have hweighted :
      ∑ i, w i * bound ≤
        (∑ i, w i * affine.evalReal (T.vertexReal i)) := by
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hvertex i) (hw i)
  rw [← Finset.sum_mul, hsum, one_mul] at hweighted
  exact hweighted

theorem RationalTetrahedron.upperClosedConstraint_holds_of_vertices
    (T : RationalTetrahedron) (affine : RationalAffine 3) (bound : Rat)
    (hvertex : ∀ i, affine.evalReal (T.vertexReal i) ≤ (bound : Real)) :
    ∀ x ∈ T.region,
      (RationalAffineConstraint.mk affine .upperClosed bound).holds x := by
  intro x hx
  simpa [RationalAffineConstraint.holds] using
    (T.affine_eval_le_of_vertices affine (bound := (bound : Real)) hvertex x hx)

theorem RationalTetrahedron.lowerClosedConstraint_holds_of_vertices
    (T : RationalTetrahedron) (affine : RationalAffine 3) (bound : Rat)
    (hvertex : ∀ i, (bound : Real) ≤ affine.evalReal (T.vertexReal i)) :
    ∀ x ∈ T.region,
      (RationalAffineConstraint.mk affine .lowerClosed bound).holds x := by
  intro x hx
  simpa [RationalAffineConstraint.holds] using
    (T.affine_eval_ge_of_vertices affine (bound := (bound : Real)) hvertex x hx)

end PrimesRestrictedDigits
