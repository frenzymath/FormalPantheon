import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronQuadraticVertexMomentD965

/-!
# Cubic moments of physical vertex interpolants

The exact three-factor moment retains both affine numerator factors in the P2 secant
certificate. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

private theorem region_compact_D975 (T : RationalTetrahedron) :
    IsCompact T.region := by
  rw [T.region_eq_convexHull]
  exact (Set.finite_range T.vertexReal).isCompact_convexHull Real

theorem RationalTetrahedron.vertexInterpolant_mul_mul_integrableOn_D975
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a b c : Fin 4 -> Real) :
    IntegrableOn (fun x => T.vertexInterpolant_D965 hdet a x *
      T.vertexInterpolant_D965 hdet b x * T.vertexInterpolant_D965 hdet c x)
      T.region (volume : Measure (Fin 3 -> Real)) := by
  exact (((T.vertexInterpolant_continuous_D965 hdet a).mul
    (T.vertexInterpolant_continuous_D965 hdet b)).mul
      (T.vertexInterpolant_continuous_D965 hdet c)).continuousOn.integrableOn_compact
        (region_compact_D975 T)

private def tripleExponent_D975 (i j k : Fin 4) : Fin 4 -> Nat :=
  fun l => (if l = i then 1 else 0) + (if l = j then 1 else 0) +
    (if l = k then 1 else 0)

private theorem tripleExponent_product_D975
    (f : Fin 4 -> Real) (i j k : Fin 4) :
    (∏ l, f l ^ tripleExponent_D975 i j k l) = f i * f j * f k := by
  unfold tripleExponent_D975
  simp_rw [pow_add]
  simp only [Finset.prod_mul_distrib]
  simp

private theorem tripleExponent_sum_D975 (i j k : Fin 4) :
    (∑ l, tripleExponent_D975 i j k l) = 3 := by
  unfold tripleExponent_D975
  simp only [Finset.sum_add_distrib]
  simp

private theorem tripleExponent_factorial_D975 (i j k : Fin 4) :
    (∏ l, (Nat.factorial (tripleExponent_D975 i j k l) : Real)) =
      1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
        (if j = k then 1 else 0) + 2 * (if i = j ∧ i = k then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [tripleExponent_D975, Fin.prod_univ_four] <;>
    norm_num [Fin.ext_iff]

private theorem region_weight_mul_mul_integral_D975
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (i j k : Fin 4) :
    (∫ x in T.region, T.barycentricWeight_D930 hdet i x *
      T.barycentricWeight_D930 hdet j x * T.barycentricWeight_D930 hdet k x
      ∂(volume : Measure (Fin 3 -> Real))) =
      (T.volumeRat : Real) / 120 *
        (1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
          (if j = k then 1 else 0) + 2 * (if i = j ∧ i = k then 1 else 0)) := by
  have hm := T.region_barycentricMoment_D930 hdet (tripleExponent_D975 i j k)
  have hm' :
      (∫ x in T.region,
        ∏ l, T.barycentricWeight_D930 hdet l x ^ tripleExponent_D975 i j k l
        ∂(volume : Measure (Fin 3 -> Real))) =
        |LinearMap.det T.barycentricEdgeLinearMap| *
          (∏ l, (Nat.factorial (tripleExponent_D975 i j k l) : Real)) /
          (Nat.factorial ((∑ l, tripleExponent_D975 i j k l) + 3) : Real) := by
    simpa [Fin.prod_univ_four, Fin.sum_univ_four, mul_assoc] using hm
  simp_rw [tripleExponent_product_D975] at hm'
  rw [tripleExponent_sum_D975, tripleExponent_factorial_D975] at hm'
  rw [show (Nat.factorial (3 + 3) : Real) = 720 by norm_num] at hm'
  rw [hm', T.barycentricEdgeLinearMap_absDet_eq_six_volumeRat_D928]
  ring

private theorem weight_mul_mul_integrableOn_D975
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (i j k : Fin 4) :
    IntegrableOn (fun x => T.barycentricWeight_D930 hdet i x *
      T.barycentricWeight_D930 hdet j x * T.barycentricWeight_D930 hdet k x)
      T.region (volume : Measure (Fin 3 -> Real)) := by
  exact (((T.barycentricWeight_continuous_D965 hdet i).mul
    (T.barycentricWeight_continuous_D965 hdet j)).mul
      (T.barycentricWeight_continuous_D965 hdet k)).continuousOn.integrableOn_compact
        (region_compact_D975 T)

set_option maxRecDepth 2048 in
theorem RationalTetrahedron.region_vertexInterpolant_mul_mul_integral_D975
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a b c : Fin 4 -> Real) :
    (∫ x in T.region, T.vertexInterpolant_D965 hdet a x *
      T.vertexInterpolant_D965 hdet b x * T.vertexInterpolant_D965 hdet c x
      ∂(volume : Measure (Fin 3 -> Real))) =
      (T.volumeRat : Real) / 120 *
        ((∑ i, a i) * (∑ i, b i) * (∑ i, c i) +
          (∑ i, a i * b i) * (∑ i, c i) +
          (∑ i, a i * c i) * (∑ i, b i) +
          (∑ i, b i * c i) * (∑ i, a i) + 2 * (∑ i, a i * b i * c i)) := by
  let term := fun (i j k : Fin 4) (x : Fin 3 -> Real) =>
    (a i * b j * c k) * (T.barycentricWeight_D930 hdet i x *
      T.barycentricWeight_D930 hdet j x * T.barycentricWeight_D930 hdet k x)
  have hint (i j k : Fin 4) :
      IntegrableOn (term i j k) T.region (volume : Measure (Fin 3 -> Real)) :=
    (weight_mul_mul_integrableOn_D975 T hdet i j k).const_mul (a i * b j * c k)
  have hexpand : (fun x : Fin 3 -> Real => T.vertexInterpolant_D965 hdet a x *
      T.vertexInterpolant_D965 hdet b x * T.vertexInterpolant_D965 hdet c x) =
      (fun x => ∑ i, ∑ j, ∑ k, term i j k x) := by
    funext x
    simp only [RationalTetrahedron.vertexInterpolant_D965, Fin.sum_univ_four, term]
    ring
  rw [hexpand]
  calc
    (∫ x in T.region, ∑ i, ∑ j, ∑ k, term i j k x
        ∂(volume : Measure (Fin 3 -> Real))) =
        ∑ i, ∑ j, ∑ k, ∫ x in T.region, term i j k x
          ∂(volume : Measure (Fin 3 -> Real)) := by
      rw [integral_finsetSum Finset.univ (fun i hi =>
        integrable_finsetSum Finset.univ fun j hj =>
          integrable_finsetSum Finset.univ fun k hk => hint i j k)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum Finset.univ (fun j hj =>
        integrable_finsetSum Finset.univ fun k hk => hint i j k)]
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_finsetSum Finset.univ (fun k hk => hint i j k)
    _ = ∑ i, ∑ j, ∑ k, (a i * b j * c k) *
        ((T.volumeRat : Real) / 120 *
          (1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
            (if j = k then 1 else 0) + 2 * (if i = j ∧ i = k then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [term]
      rw [integral_const_mul, region_weight_mul_mul_integral_D975]
    _ = (T.volumeRat : Real) / 120 *
        ((∑ i, a i) * (∑ i, b i) * (∑ i, c i) +
          (∑ i, a i * b i) * (∑ i, c i) +
          (∑ i, a i * c i) * (∑ i, b i) +
          (∑ i, b i * c i) * (∑ i, a i) + 2 * (∑ i, a i * b i * c i)) := by
      simp only [Fin.sum_univ_four]
      norm_num [Fin.ext_iff]
      ring

end
end PrimesRestrictedDigits
