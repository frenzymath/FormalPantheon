import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronDetVolumeNullImageD928
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronPhysicalBarycentricMomentsD930
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Quadratic moments of vertex interpolants

For a nondegenerate rational tetrahedron, packages the exact integral of the product of two
affine interpolants specified by their four vertex values. The normalization uses the existing
absolute rational volume.

Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12), via.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def RationalTetrahedron.vertexInterpolant_D965
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a : Fin 4 -> Real) (x : Fin 3 -> Real) : Real :=
  ∑ i, T.barycentricWeight_D930 hdet i x * a i

private theorem d965_pullback_continuous
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0) :
    Continuous (T.barycentricPullbackCoordinate_D930 hdet) := by
  let e := T.barycentricEdgeLinearMap.equivOfDetNeZero hdet
  change Continuous (fun y : Fin 3 -> Real => e.symm (y - T.vertexReal 0))
  exact (e.toContinuousLinearEquiv.symm).continuous.comp
    (continuous_id.sub continuous_const)

theorem RationalTetrahedron.barycentricWeight_continuous_D965
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (i : Fin 4) :
    Continuous (fun x : Fin 3 -> Real =>
      T.barycentricWeight_D930 hdet i x) := by
  have hp := d965_pullback_continuous T hdet
  have h0 : Continuous (fun x : Fin 3 -> Real =>
      T.barycentricPullbackCoordinate_D930 hdet x 0) :=
    (continuous_apply 0).comp hp
  have h1 : Continuous (fun x : Fin 3 -> Real =>
      T.barycentricPullbackCoordinate_D930 hdet x 1) :=
    (continuous_apply 1).comp hp
  have h2 : Continuous (fun x : Fin 3 -> Real =>
      T.barycentricPullbackCoordinate_D930 hdet x 2) :=
    (continuous_apply 2).comp hp
  unfold RationalTetrahedron.barycentricWeight_D930
  fin_cases i
  · exact ((continuous_const.sub h0).sub h1).sub h2
  · exact h0
  · exact h1
  · exact h2

theorem RationalTetrahedron.vertexInterpolant_continuous_D965
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a : Fin 4 -> Real) :
    Continuous (T.vertexInterpolant_D965 hdet a) := by
  unfold RationalTetrahedron.vertexInterpolant_D965
  exact continuous_finsetSum Finset.univ fun i hi =>
    (T.barycentricWeight_continuous_D965 hdet i).mul continuous_const

private theorem d965_region_compact (T : RationalTetrahedron) :
    IsCompact T.region := by
  rw [T.region_eq_convexHull]
  exact (Set.finite_range T.vertexReal).isCompact_convexHull Real

theorem RationalTetrahedron.vertexInterpolant_mul_integrableOn_D965
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a b : Fin 4 -> Real) :
    IntegrableOn (fun x =>
      T.vertexInterpolant_D965 hdet a x *
        T.vertexInterpolant_D965 hdet b x)
      T.region (volume : Measure (Fin 3 -> Real)) := by
  exact ((T.vertexInterpolant_continuous_D965 hdet a).mul
    (T.vertexInterpolant_continuous_D965 hdet b)).continuousOn.integrableOn_compact
      (d965_region_compact T)

private def d965PairExponent (i j : Fin 4) : Fin 4 -> Nat :=
  fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

private theorem d965_pairExponent_product
    (f : Fin 4 -> Real) (i j : Fin 4) :
    (∏ k, f k ^ d965PairExponent i j k) = f i * f j := by
  unfold d965PairExponent
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib]
  simp

private theorem d965_pairExponent_sum (i j : Fin 4) :
    (∑ k, d965PairExponent i j k) = 2 := by
  unfold d965PairExponent
  rw [Finset.sum_add_distrib]
  simp

private theorem d965_pairExponent_factorial_product (i j : Fin 4) :
    (∏ k, (Nat.factorial (d965PairExponent i j k) : Real)) =
      if i = j then 2 else 1 := by
  by_cases hij : i = j
  · subst j
    have he : d965PairExponent i i = fun k => if k = i then 2 else 0 := by
      funext k
      by_cases hki : k = i <;> simp [d965PairExponent, hki]
    rw [he]
    have hf : (fun k : Fin 4 =>
        (Nat.factorial (if k = i then 2 else 0) : Real)) =
        fun k => if k = i then 2 else 1 := by
      funext k
      by_cases hki : k = i <;> simp [hki]
    rw [hf]
    simp
  · rw [if_neg hij]
    apply Finset.prod_eq_one
    intro k hk
    by_cases hki : k = i
    · subst k
      simp [d965PairExponent, hij]
    · by_cases hkj : k = j
      · subst k
        simp [d965PairExponent, hki]
      · simp [d965PairExponent, hki, hkj]

private theorem d965_region_weight_mul_integral
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (i j : Fin 4) :
    (∫ x in T.region,
      T.barycentricWeight_D930 hdet i x *
        T.barycentricWeight_D930 hdet j x
      ∂(volume : Measure (Fin 3 -> Real))) =
      (T.volumeRat : Real) / 20 * (1 + if i = j then 1 else 0) := by
  have hm := T.region_barycentricMoment_D930 hdet (d965PairExponent i j)
  have hm' :
      (∫ x in T.region,
        ∏ k, T.barycentricWeight_D930 hdet k x ^ d965PairExponent i j k
        ∂(volume : Measure (Fin 3 -> Real))) =
        |LinearMap.det T.barycentricEdgeLinearMap| *
          (∏ k, (Nat.factorial (d965PairExponent i j k) : Real)) /
          (Nat.factorial ((∑ k, d965PairExponent i j k) + 3) : Real) := by
    simpa [Fin.prod_univ_four, Fin.sum_univ_four, mul_assoc] using hm
  rw [show (fun x : Fin 3 -> Real =>
      ∏ k, T.barycentricWeight_D930 hdet k x ^ d965PairExponent i j k) =
      fun x => T.barycentricWeight_D930 hdet i x *
        T.barycentricWeight_D930 hdet j x by
          funext x
          exact d965_pairExponent_product
            (fun k => T.barycentricWeight_D930 hdet k x) i j] at hm'
  rw [d965_pairExponent_sum, d965_pairExponent_factorial_product] at hm'
  norm_num [Nat.factorial] at hm'
  rw [hm', T.barycentricEdgeLinearMap_absDet_eq_six_volumeRat_D928]
  by_cases hij : i = j <;> simp [hij] <;> ring

private theorem d965_weight_mul_integrableOn
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (i j : Fin 4) :
    IntegrableOn (fun x =>
      T.barycentricWeight_D930 hdet i x *
        T.barycentricWeight_D930 hdet j x)
      T.region (volume : Measure (Fin 3 -> Real)) := by
  exact ((T.barycentricWeight_continuous_D965 hdet i).mul
    (T.barycentricWeight_continuous_D965 hdet j)).continuousOn.integrableOn_compact
      (d965_region_compact T)

theorem RationalTetrahedron.region_vertexInterpolant_mul_integral_D965
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a b : Fin 4 -> Real) :
    (∫ x in T.region,
      T.vertexInterpolant_D965 hdet a x *
        T.vertexInterpolant_D965 hdet b x
      ∂(volume : Measure (Fin 3 -> Real))) =
      (T.volumeRat : Real) / 20 *
        ((∑ i, a i) * (∑ i, b i) + ∑ i, a i * b i) := by
  have hexpand : (fun x : Fin 3 -> Real =>
      T.vertexInterpolant_D965 hdet a x *
        T.vertexInterpolant_D965 hdet b x) =
      (fun x => ∑ i, ∑ j,
        (a i * b j) *
          (T.barycentricWeight_D930 hdet i x *
            T.barycentricWeight_D930 hdet j x)) := by
    funext x
    unfold RationalTetrahedron.vertexInterpolant_D965
    calc
      (∑ i, T.barycentricWeight_D930 hdet i x * a i) *
          (∑ j, T.barycentricWeight_D930 hdet j x * b j) =
          ∑ i, (T.barycentricWeight_D930 hdet i x * a i) *
            (∑ j, T.barycentricWeight_D930 hdet j x * b j) := by
        rw [Finset.sum_mul]
      _ = ∑ i, ∑ j,
          (T.barycentricWeight_D930 hdet i x * a i) *
            (T.barycentricWeight_D930 hdet j x * b j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ j,
          (a i * b j) *
            (T.barycentricWeight_D930 hdet i x *
              T.barycentricWeight_D930 hdet j x) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  calc
    (∫ x in T.region,
        T.vertexInterpolant_D965 hdet a x *
          T.vertexInterpolant_D965 hdet b x
        ∂(volume : Measure (Fin 3 -> Real))) =
        ∫ x in T.region, ∑ i, ∑ j,
          (a i * b j) *
            (T.barycentricWeight_D930 hdet i x *
              T.barycentricWeight_D930 hdet j x)
          ∂(volume : Measure (Fin 3 -> Real)) := by rw [hexpand]
    _ = ∑ i, ∫ x in T.region, ∑ j,
          (a i * b j) *
            (T.barycentricWeight_D930 hdet i x *
              T.barycentricWeight_D930 hdet j x)
          ∂(volume : Measure (Fin 3 -> Real)) := by
      simpa only [Finset.sum_apply] using
        (integral_finsetSum
          (μ := (volume : Measure (Fin 3 -> Real)).restrict T.region)
          (s := (Finset.univ : Finset (Fin 4)))
          (f := fun i x => ∑ j,
            (a i * b j) *
              (T.barycentricWeight_D930 hdet i x *
                T.barycentricWeight_D930 hdet j x))
          (fun i hi => integrable_finsetSum Finset.univ fun j hj =>
            (d965_weight_mul_integrableOn T hdet i j).const_mul (a i * b j)))
    _ = ∑ i, ∑ j, ∫ x in T.region,
          (a i * b j) *
            (T.barycentricWeight_D930 hdet i x *
              T.barycentricWeight_D930 hdet j x)
          ∂(volume : Measure (Fin 3 -> Real)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Finset.sum_apply] using
        (integral_finsetSum
          (μ := (volume : Measure (Fin 3 -> Real)).restrict T.region)
          (s := (Finset.univ : Finset (Fin 4)))
          (f := fun j x =>
            (a i * b j) *
              (T.barycentricWeight_D930 hdet i x *
                T.barycentricWeight_D930 hdet j x))
          (fun j hj =>
            (d965_weight_mul_integrableOn T hdet i j).const_mul (a i * b j)))
    _ = ∑ i, ∑ j, (a i * b j) *
          ((T.volumeRat : Real) / 20 * (1 + if i = j then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, d965_region_weight_mul_integral T hdet i j]
    _ = (T.volumeRat : Real) / 20 *
        ((∑ i, a i) * (∑ i, b i) + ∑ i, a i * b i) := by
      simp only [Fin.sum_univ_four]
      simp
      ring

end

end PrimesRestrictedDigits
