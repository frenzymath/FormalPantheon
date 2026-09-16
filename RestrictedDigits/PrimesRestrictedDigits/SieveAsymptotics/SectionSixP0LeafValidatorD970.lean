import PrimesRestrictedDigits.BasicEstimates.RationalAffineReciprocalCapCastsD969
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronIntegratedForestReplayD966
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0AffineKernelsD968

/-!
# Exact rational leaf validation for the P0 profile

The payload bounds the derived density weight; the integral comparison charges the physical
tetrahedron volume once. Concrete root coverage and certificate data are separate obligations.
Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def sectionSixP0LeafWeightD970 (T : RationalTetrahedron) : Rat :=
  positivePartAffineReciprocalWeightRat_D969 T sectionSixP0BaselineNumeratorD968
    sectionSixP0BaselineDenominatorD968 +
  positivePartAffineReciprocalWeightRat_D969 T sectionSixP0ExcessNumeratorD968
    sectionSixP0ExcessDenominatorD968

def sectionSixP0LeafValidD970 (T : RationalTetrahedron) (q : Rat) : Bool :=
  decide ((∀ i, 0 < T.vertex i 0 ∧ 0 < T.vertex i 1 ∧
    (16249 / 250000 : Rat) ≤ T.vertex i 2 ∧
    0 < 1 - T.vertex i 0 - T.vertex i 1 - T.vertex i 2) ∧
    sectionSixP0LeafWeightD970 T ≤ q)

private theorem vertex_guard_D970 (T : RationalTetrahedron) (q : Rat)
    (hv : sectionSixP0LeafValidD970 T q = true) :
    ∀ i, 0 < T.vertexReal i 0 ∧ 0 < T.vertexReal i 1 ∧
      (16249 / 250000 : Real) ≤ T.vertexReal i 2 ∧
      0 < 1 - T.vertexReal i 0 - T.vertexReal i 1 - T.vertexReal i 2 := by
  have h := (of_decide_eq_true hv).1
  intro i
  dsimp only [RationalTetrahedron.vertexReal]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast (h i).1
  · exact_mod_cast (h i).2.1
  · have hw := (Rat.cast_le (K := Real)).2 (h i).2.2.1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hw
    exact hw
  · exact_mod_cast (h i).2.2.2

theorem sectionSixP0Leaf_integrable_D970 (T : RationalTetrahedron) (q : Rat)
    (hv : sectionSixP0LeafValidD970 T q = true) :
    IntegrableOn (fun x : Fin 3 -> Real =>
      sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2))
      T.region volume :=
  sectionSixP0_profile_integrableOn_D968 T (vertex_guard_D970 T q hv)

theorem sectionSixP0Leaf_nonneg_D970 (T : RationalTetrahedron) (q : Rat)
    (hv : sectionSixP0LeafValidD970 T q = true)
    {x : Fin 3 -> Real} (hx : x ∈ T.region) :
    0 ≤ sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2) :=
  sectionSixP0_profile_nonneg_D968 T (vertex_guard_D970 T q hv) hx

private theorem rational_denominators_positive_D970 {m : Nat}
    (T : RationalTetrahedron) (p : Fin m -> RationalAffine 3)
    (hp : ∀ k i, 0 < (p k).evalReal (T.vertexReal i)) :
    ∀ k i, 0 < rationalAffineEval_D969 (p k) (T.vertex i) := by
  intro k i
  apply (Rat.cast_pos (K := Real)).1
  rw [rationalAffineEval_cast_D969]
  exact hp k i

theorem sectionSixP0Leaf_integral_le_D970 (T : RationalTetrahedron) (q : Rat)
    (hv : sectionSixP0LeafValidD970 T q = true) :
    (∫ x in T.region,
      sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2)) ≤
        ((T.volumeRat * q : Rat) : Real) := by
  have hguard := vertex_guard_D970 T q hv
  obtain ⟨hbase, hexcess⟩ := sectionSixP0_denominators_positive_D968 T hguard
  have hweight : sectionSixP0LeafWeightD970 T ≤ q := (of_decide_eq_true hv).2
  have hbaseInt := T.positivePartAffineReciprocal_integrableOn_D967
    sectionSixP0BaselineNumeratorD968 sectionSixP0BaselineDenominatorD968 hbase
  have hexcessInt := T.positivePartAffineReciprocal_integrableOn_D967
    sectionSixP0ExcessNumeratorD968 sectionSixP0ExcessDenominatorD968 hexcess
  have hbaseCap := T.positivePartAffineReciprocal_setIntegral_le_rat_D969
    sectionSixP0BaselineNumeratorD968 sectionSixP0BaselineDenominatorD968
    (rational_denominators_positive_D970 T _ hbase)
  have hexcessCap := T.positivePartAffineReciprocal_setIntegral_le_rat_D969
    sectionSixP0ExcessNumeratorD968 sectionSixP0ExcessDenominatorD968
    (rational_denominators_positive_D970 T _ hexcess)
  calc
    (∫ x in T.region,
        sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2)) =
        ∫ x in T.region,
          positivePartAffineReciprocalKernel_D967 sectionSixP0BaselineNumeratorD968
            sectionSixP0BaselineDenominatorD968 x +
          positivePartAffineReciprocalKernel_D967 sectionSixP0ExcessNumeratorD968
            sectionSixP0ExcessDenominatorD968 x := by
      apply setIntegral_congr_fun T.region_measurable_D924
      intro x hx
      apply sectionSixP0TwoCeilingProfile_eq_affineKernels_D968
      have h := T.affine_eval_ge_of_vertices (sectionSixP0CoordinateD968 2)
        (bound := (16249 / 250000 : Real))
        (by intro i; simpa only [sectionSixP0CoordinateD968_eval] using (hguard i).2.2.1)
        x hx
      simpa only [sectionSixP0CoordinateD968_eval] using h
    _ = (∫ x in T.region,
          positivePartAffineReciprocalKernel_D967 sectionSixP0BaselineNumeratorD968
            sectionSixP0BaselineDenominatorD968 x) +
        (∫ x in T.region,
          positivePartAffineReciprocalKernel_D967 sectionSixP0ExcessNumeratorD968
            sectionSixP0ExcessDenominatorD968 x) := integral_add hbaseInt hexcessInt
    _ ≤ ((T.volumeRat * positivePartAffineReciprocalWeightRat_D969 T
          sectionSixP0BaselineNumeratorD968 sectionSixP0BaselineDenominatorD968 : Rat) : Real) +
        ((T.volumeRat * positivePartAffineReciprocalWeightRat_D969 T
          sectionSixP0ExcessNumeratorD968 sectionSixP0ExcessDenominatorD968 : Rat) : Real) :=
      add_le_add hbaseCap hexcessCap
    _ = ((T.volumeRat * sectionSixP0LeafWeightD970 T : Rat) : Real) := by
      rw [sectionSixP0LeafWeightD970, mul_add, Rat.cast_add]
    _ ≤ ((T.volumeRat * q : Rat) : Real) :=
      (Rat.cast_le (K := Real)).2 (mul_le_mul_of_nonneg_left hweight T.volumeRat_nonneg)

theorem sectionSixP0Forest_integral_le_D970 (n : Nat)
    (roots : Fin n -> RationalTetrahedron)
    (trees : Fin n -> RationalTetraSubdivision Rat)
    (target : Set (Fin 3 -> Real)) (htarget : MeasurableSet target)
    (hcover : target ⊆ ⋃ r, (roots r).region)
    (hvalid : ∀ r, (trees r).coverValid sectionSixP0LeafValidD970 (roots r) = true) :
    (∫ x in target,
      sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2)) ≤
        ((∑ r, (trees r).replayWeightRat (roots r) (fun _ q => q) : Rat) : Real) := by
  apply rationalTetraForest_setIntegral_le_replayWeightRat_D966
    n roots trees sectionSixP0LeafValidD970 (fun _ q => q) target _ htarget hcover hvalid
  · exact sectionSixP0Leaf_integrable_D970
  · intro T q hv x hx
    exact sectionSixP0Leaf_nonneg_D970 T q hv hx
  · exact sectionSixP0Leaf_integral_le_D970

end PrimesRestrictedDigits
