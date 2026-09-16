import PrimesRestrictedDigits.BasicEstimates.RationalAffineReciprocalCapCastsD969

/-!
# Closed zero-vertex faces

Project-derived clipping geometry for `MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13).
Nonpositive vertex guards retain their entire zero face.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def RationalTetrahedron.zeroVertexFaceD1001 (T : RationalTetrahedron)
    (a : RationalAffine 3) (pivot : Fin 4) : RationalTetrahedron :=
  { vertex := fun i =>
      if rationalAffineEval_D969 a (T.vertex i) = 0 then T.vertex i
      else T.vertex pivot }

private theorem nonpositive_weighted_terms_eq_zero_D1001
    (w value : Fin 4 -> Real) (hw : ∀ i, 0 ≤ w i)
    (hvalue : ∀ i, value i ≤ 0) (hsum : 0 ≤ ∑ i, w i * value i) :
    ∀ i, w i * value i = 0 := by
  have hterm (i : Fin 4) : w i * value i ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hw i) (hvalue i)
  have hzero : ∑ i, w i * value i = 0 :=
    le_antisymm (Finset.sum_nonpos fun i _ => hterm i) hsum
  exact fun i => (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hterm j)).mp
    hzero i (Finset.mem_univ i)

theorem RationalTetrahedron.zeroVertexFace_eval_eq_zero_D1001
    (T : RationalTetrahedron) (a : RationalAffine 3) (pivot : Fin 4)
    (hpivot : rationalAffineEval_D969 a (T.vertex pivot) = 0) :
    ∀ i, rationalAffineEval_D969 a
      ((T.zeroVertexFaceD1001 a pivot).vertex i) = 0 := by
  intro i
  by_cases hi : rationalAffineEval_D969 a (T.vertex i) = 0
  · simp only [zeroVertexFaceD1001, hi, ite_true]
  · simpa only [zeroVertexFaceD1001, hi, ite_false] using hpivot

theorem RationalTetrahedron.zeroVertexFace_region_eq_D1001
    (T : RationalTetrahedron) (a : RationalAffine 3) (pivot : Fin 4)
    (hvertex : ∀ i, rationalAffineEval_D969 a (T.vertex i) ≤ 0)
    (hpivot : rationalAffineEval_D969 a (T.vertex pivot) = 0) :
    (T.zeroVertexFaceD1001 a pivot).region =
      T.region ∩ {x | 0 ≤ a.evalReal x} := by
  have hcast (U : RationalTetrahedron) (i : Fin 4) :
      a.evalReal (U.vertexReal i) =
        (rationalAffineEval_D969 a (U.vertex i) : Real) :=
    (rationalAffineEval_cast_D969 a (U.vertex i)).symm
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · have hrange : Set.range (T.zeroVertexFaceD1001 a pivot).vertexReal ⊆
          Set.range T.vertexReal := by
        rintro _ ⟨i, rfl⟩
        by_cases hi : rationalAffineEval_D969 a (T.vertex i) = 0
        · refine ⟨i, ?_⟩
          funext k
          simp [vertexReal, zeroVertexFaceD1001, hi]
        · refine ⟨pivot, ?_⟩
          funext k
          simp [vertexReal, zeroVertexFaceD1001, hi]
      rw [region_eq_convexHull] at hx ⊢
      exact convexHull_mono hrange hx
    · apply (T.zeroVertexFaceD1001 a pivot).affine_eval_ge_of_vertices a _ x hx
      intro i
      rw [hcast, T.zeroVertexFace_eval_eq_zero_D1001 a pivot hpivot i]
      simp
  · rintro x ⟨⟨w, hw, hsum, rfl⟩, hx⟩
    have hvalue (i : Fin 4) : a.evalReal (T.vertexReal i) ≤ 0 := by
      rw [hcast]
      exact Rat.cast_nonpos.mpr (hvertex i)
    have hterms := nonpositive_weighted_terms_eq_zero_D1001 w
      (fun i => a.evalReal (T.vertexReal i)) hw hvalue
      (by simpa only [Set.mem_setOf_eq,
        a.evalReal_barycentricPoint3 T.vertexReal w hsum] using hx)
    refine ⟨w, hw, hsum, ?_⟩
    funext k
    unfold barycentricPoint3 barycentricCoordinate3
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : rationalAffineEval_D969 a (T.vertex i) = 0
    · simp [vertexReal, zeroVertexFaceD1001, hi]
    · have hne : a.evalReal (T.vertexReal i) ≠ 0 := by
        rw [hcast]
        exact_mod_cast hi
      have hwi : w i = 0 := (mul_eq_zero.mp (hterms i)).resolve_right hne
      simp [hwi]

theorem RationalTetrahedron.region_inter_nonneg_eq_empty_of_vertices_neg_D1001
    (T : RationalTetrahedron) (a : RationalAffine 3)
    (hvertex : ∀ i, rationalAffineEval_D969 a (T.vertex i) < 0) :
    T.region ∩ {x | 0 ≤ a.evalReal x} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨⟨w, hw, hsum, rfl⟩, hx⟩
  have hvalue (i : Fin 4) : a.evalReal (T.vertexReal i) < 0 := by
    rw [show a.evalReal (T.vertexReal i) =
      (rationalAffineEval_D969 a (T.vertex i) : Real) from
      (rationalAffineEval_cast_D969 a (T.vertex i)).symm]
    exact Rat.cast_lt_zero.mpr (hvertex i)
  have hterms := nonpositive_weighted_terms_eq_zero_D1001 w
    (fun i => a.evalReal (T.vertexReal i)) hw (fun i => (hvalue i).le)
    (by simpa only [Set.mem_setOf_eq,
      a.evalReal_barycentricPoint3 T.vertexReal w hsum] using hx)
  have hwzero (i : Fin 4) : w i = 0 :=
    (mul_eq_zero.mp (hterms i)).resolve_right (hvalue i).ne
  simp only [hwzero, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

end PrimesRestrictedDigits
