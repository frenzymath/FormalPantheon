import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2LeafDataD988
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2NativeProfileRegularityD987
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronIntegratedForestReplayD966

/-!
# Sound exact validation of native P2 leaves

All selected slot inequalities are checked against the original profile. The rational density
is charged with physical volume exactly once, and assembles the resulting bounds without a
disjointness assumption. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem cast_positive_D989 (T : RationalTetrahedron) (a : RationalAffine 3)
    (ha : ∀ i, 0 < rationalAffineEval_D969 a (T.vertex i)) :
    ∀ i, 0 < a.evalReal (T.vertexReal i) := by
  intro i
  have h := (Rat.cast_pos (K := Real)).2 (ha i)
  have hcast : (rationalAffineEval_D969 a (T.vertex i) : Real) =
      a.evalReal (T.vertexReal i) := by
    change (rationalAffineEval_D969 a (T.vertex i) : Real) =
      a.evalReal (fun j => (T.vertex i j : Real))
    exact rationalAffineEval_cast_D969 a (T.vertex i)
  rwa [hcast] at h

private theorem vertex_positive_D989 (T : RationalTetrahedron)
    (p : SectionSixP2LeafPayloadD988) (hv : sectionSixP2LeafValidD988 T p = true) :
    ∀ i, 0 < sectionSixP2AffineUD983.evalReal (T.vertexReal i) ∧
      0 < sectionSixP2AffineVD983.evalReal (T.vertexReal i) ∧
      0 < sectionSixP2AffineDD983.evalReal (T.vertexReal i) ∧
      0 < sectionSixP2AffineWD983.evalReal (T.vertexReal i) ∧
      0 < sectionSixP2AffineBD983.evalReal (T.vertexReal i) := by
  have h := (of_decide_eq_true hv).1
  intro i
  exact ⟨cast_positive_D989 T _ (fun j => (h j).1) i,
    cast_positive_D989 T _ (fun j => (h j).2.1) i,
    cast_positive_D989 T _ (fun j => (h j).2.2.1) i,
    cast_positive_D989 T _ (fun j => (h j).2.2.2.1) i,
    cast_positive_D989 T _ (fun j => (h j).2.2.2.2) i⟩

theorem sectionSixP2Leaf_integrable_D989 (T : RationalTetrahedron)
    (p : SectionSixP2LeafPayloadD988) (hv : sectionSixP2LeafValidD988 T p = true) :
    IntegrableOn (fun x : Fin 3 -> Real =>
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2))
      T.region volume := by
  have h := vertex_positive_D989 T p hv
  exact T.sectionSixP2RefinedProfile_integrableOn_D987
    (fun i => (h i).1) (fun i => (h i).2.1) (fun i => (h i).2.2.1)
    (fun i => (h i).2.2.2.1) (fun i => (h i).2.2.2.2.le)

theorem sectionSixP2Leaf_nonneg_D989 (T : RationalTetrahedron)
    (p : SectionSixP2LeafPayloadD988) (hv : sectionSixP2LeafValidD988 T p = true)
    {x : Fin 3 -> Real} (hx : x ∈ T.region) :
    0 ≤ sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2) := by
  have h := vertex_positive_D989 T p hv
  exact T.sectionSixP2RefinedProfile_nonneg_D987
    (fun i => (h i).1) (fun i => (h i).2.1) (fun i => (h i).2.2.1)
    (fun i => (h i).2.2.2.1) (fun i => (h i).2.2.2.2.le) x hx

private theorem budget_positive_D989 (T : RationalTetrahedron) (q : Rat) (hq : 0 < q)
    (hB : ∀ i, 0 < rationalAffineEval_D969 sectionSixP2AffineBD983 (T.vertex i)) :
    ∀ i, 0 < rationalAffineEval_D969 (sectionSixP2BudgetMultipleD983 q) (T.vertex i) := by
  intro i
  apply (Rat.cast_pos (K := Real)).1
  rw [rationalAffineEval_cast_D969, sectionSixP2BudgetMultipleD983_eval]
  exact mul_pos ((Rat.cast_pos (K := Real)).2 hq) (cast_positive_D989 T _ hB i)

private theorem inverse_choice_cap_D989 (T : RationalTetrahedron)
    (hU : ∀ i, 0 < rationalAffineEval_D969 sectionSixP2AffineUD983 (T.vertex i))
    (hV : ∀ i, 0 < rationalAffineEval_D969 sectionSixP2AffineVD983 (T.vertex i))
    (hD : ∀ i, 0 < rationalAffineEval_D969 sectionSixP2AffineDD983 (T.vertex i))
    (hW : ∀ i, 0 < rationalAffineEval_D969 sectionSixP2AffineWD983 (T.vertex i))
    (hB : ∀ i, 0 < rationalAffineEval_D969 sectionSixP2AffineBD983 (T.vertex i))
    (i : Fin 8) (code : Fin 32) :
    (∫ x in T.region, sectionSixP2ClampedInverseAffinePayloadD982
      sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
      sectionSixP2AffineWD983 (sectionSixP2InverseLowerD986 i)
      (sectionSixP2InverseUpperD986 i) sectionSixP2AffineBD983
      (sectionSixP2InverseArgumentLowerD986 i : Real)
      (sectionSixP2InverseArgumentUpperD986 i : Real) x) ≤
        ((T.volumeRat * sectionSixP2InverseChoiceWeightD988 T i code : Rat) : Real) := by
  apply T.sectionSixP2InverseAffine_setIntegral_le_rat_D985
    sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
    sectionSixP2AffineWD983 (sectionSixP2InverseLowerD986 i)
    (sectionSixP2InverseUpperD986 i) sectionSixP2AffineBD983 hU hV hD hW
    (budget_positive_D989 T _ (by positivity) hB)
    (budget_positive_D989 T _ (by positivity) hB) _
    (sectionSixP2InverseArgumentLowerD986 i) (sectionSixP2InverseArgumentUpperD986 i)
    _ _ _ (Fin.ofNat 4 code.val) (code.val / 4 % 2 == 1)
    (code.val / 8 % 2 == 1) (code.val / 16 % 2 == 1)
  · intro j
    apply (Rat.cast_le (K := Real)).1
    simp only [rationalAffineEval_cast_D969,
      sectionSixP2InverseLowerD986_eval, sectionSixP2InverseUpperD986_eval]
    have hBj := (Rat.cast_pos (K := Real)).2 (hB j)
    rw [rationalAffineEval_cast_D969] at hBj
    fin_cases i <;> norm_num <;> nlinarith
  · fin_cases i <;> norm_num [sectionSixP2InverseArgumentLowerD986]
  · fin_cases i <;> norm_num [sectionSixP2InverseArgumentUpperD986]
  · intro j
    apply (Rat.cast_le (K := Real)).1
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_one,
      rationalAffineEval_cast_D969, sectionSixP2InverseLowerD986_eval]
    fin_cases i <;> norm_num [sectionSixP2InverseArgumentUpperD986] <;>
      ring_nf <;> exact le_rfl

theorem sectionSixP2Leaf_integral_le_D989 (T : RationalTetrahedron)
    (p : SectionSixP2LeafPayloadD988) (hv : sectionSixP2LeafValidD988 T p = true) :
    (∫ x in T.region,
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2)) ≤
        ((T.volumeRat * p.upper : Rat) : Real) := by
  have h := (of_decide_eq_true hv).1
  have hReal := vertex_positive_D989 T p hv
  let c := fun (L H : RationalAffine 3) (C : Rat) =>
    sectionSixP2ClampedConstantAffinePayloadD981 sectionSixP2AffineUD983
      sectionSixP2AffineVD983 sectionSixP2AffineDD983 sectionSixP2AffineWD983 L H (C : Real)
  let s := fun i : Fin 8 => sectionSixP2ClampedInverseAffinePayloadD982
    sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
    sectionSixP2AffineWD983 (sectionSixP2InverseLowerD986 i)
    (sectionSixP2InverseUpperD986 i) sectionSixP2AffineBD983
    (sectionSixP2InverseArgumentLowerD986 i : Real)
    (sectionSixP2InverseArgumentUpperD986 i : Real)
  have cInt (L H : RationalAffine 3) (C : Rat) : IntegrableOn (c L H C) T.region volume :=
    T.sectionSixP2ConstantAffine_integrableOn_D981 _ _ _ _ L H (C : Real)
      (fun i => (hReal i).1) (fun i => (hReal i).2.1)
      (fun i => (hReal i).2.2.1) (fun i => (hReal i).2.2.2.1)
  have sInt (i : Fin 8) : IntegrableOn (s i) T.region volume :=
    T.sectionSixP2InverseAffine_integrableOn_D982 _ _ _ _ _ _ _ _ _
      (fun j => (hReal j).1) (fun j => (hReal j).2.1)
      (fun j => (hReal j).2.2.1) (fun j => (hReal j).2.2.2.1)
  have cCap (L H : RationalAffine 3)
      (hL : ∀ i, 0 < rationalAffineEval_D969 L (T.vertex i))
      (hH : ∀ i, 0 < rationalAffineEval_D969 H (T.vertex i))
      (C : Rat) (hC : 0 ≤ C) (code : Fin 16) :
      (∫ x in T.region, c L H C x) ≤
        ((T.volumeRat * sectionSixP2ConstantChoiceWeightD988 T L H C code : Rat) : Real) :=
    T.sectionSixP2ConstantAffine_setIntegral_le_rat_D985 _ _ _ _ L H
      (fun i => (h i).1) (fun i => (h i).2.1)
      (fun i => (h i).2.2.1) (fun i => (h i).2.2.2.1) hL hH C hC
      (Fin.ofNat 4 code.val) (code.val / 4 % 2 == 1) (code.val / 8 % 2 == 1)
  have bPos (q : Rat) (hq : 0 < q) :=
    budget_positive_D989 T q hq (fun i => (h i).2.2.2.2)
  let first := c sectionSixP2AffineDD983 (sectionSixP2BudgetMultipleD983 (4 / 17)) (281 / 500)
  let second := c (sectionSixP2BudgetMultipleD983 (4 / 17))
    (sectionSixP2BudgetMultipleD983 (1 / 4)) (564383 / 1000000)
  let middle := fun i : Fin 8 => c (sectionSixP2MiddleLowerD986 i)
    (sectionSixP2MiddleUpperD986 i) (sectionSixP2MiddleCapRatD986 i)
  have firstInt : IntegrableOn first T.region volume := cInt _ _ _
  have secondInt : IntegrableOn second T.region volume := cInt _ _ _
  have middleInt (i : Fin 8) : IntegrableOn (middle i) T.region volume := cInt _ _ _
  have middleSumInt : IntegrableOn (fun x => ∑ i : Fin 8, middle i x) T.region volume := by
    change Integrable _ (volume.restrict T.region)
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin 8)) (fun i _ => middleInt i)
  have inverseSumInt : IntegrableOn (fun x => ∑ i : Fin 8, s i x) T.region volume := by
    change Integrable _ (volume.restrict T.region)
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin 8)) (fun i _ => sInt i)
  have firstSecondInt : IntegrableOn (fun x => first x + second x) T.region volume :=
    firstInt.add secondInt
  have firstMiddleInt : IntegrableOn
      (fun x => first x + second x + ∑ i : Fin 8, middle i x) T.region volume :=
    firstSecondInt.add middleSumInt
  have sumIdentity :
      (∫ x in T.region,
        sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2)) =
        (∫ x in T.region, first x) + (∫ x in T.region, second x) +
          (∑ i : Fin 8, ∫ x in T.region, middle i x) +
          ∑ i : Fin 8, ∫ x in T.region, s i x := by
    calc
      _ = ∫ x in T.region,
          first x + second x + (∑ i : Fin 8, middle i x) + ∑ i : Fin 8, s i x := by
        apply setIntegral_congr_fun T.region_measurable_D924
        intro x hx
        have hxB := T.affine_eval_ge_of_vertices sectionSixP2AffineBD983
          (fun i => (hReal i).2.2.2.2.le) x hx
        simpa only [c, s, first, second, middle, Rat.cast_div, Rat.cast_ofNat] using
          sectionSixP2RefinedProfile_eq_affineSlots_D986 x hxB
      _ = _ := by
        rw [integral_add firstMiddleInt inverseSumInt,
          integral_add firstSecondInt middleSumInt,
          integral_add firstInt secondInt,
          integral_finsetSum _ (fun i _ => middleInt i),
          integral_finsetSum _ (fun i _ => sInt i)]
  have firstCap := cCap sectionSixP2AffineDD983 (sectionSixP2BudgetMultipleD983 (4 / 17))
    (fun i => (h i).2.2.1) (bPos _ (by norm_num)) (281 / 500) (by norm_num) p.baseline
  have secondCap := cCap (sectionSixP2BudgetMultipleD983 (4 / 17))
    (sectionSixP2BudgetMultipleD983 (1 / 4)) (bPos _ (by norm_num))
    (bPos _ (by norm_num)) (564383 / 1000000) (by norm_num) p.legacy
  have middleCap (i : Fin 8) := cCap (sectionSixP2MiddleLowerD986 i)
    (sectionSixP2MiddleUpperD986 i) (bPos _ (by positivity)) (bPos _ (by positivity))
    (sectionSixP2MiddleCapRatD986 i)
    (by fin_cases i <;> norm_num [sectionSixP2MiddleCapRatD986]) (p.middle i)
  have inverseCap (i : Fin 8) := inverse_choice_cap_D989 T
    (fun j => (h j).1) (fun j => (h j).2.1) (fun j => (h j).2.2.1)
    (fun j => (h j).2.2.2.1) (fun j => (h j).2.2.2.2) i (p.inverse i)
  calc
    _ ≤ ((T.volumeRat * sectionSixP2LeafWeightD988 T p : Rat) : Real) := by
      rw [sumIdentity]
      have hsum := add_le_add
        (add_le_add (add_le_add firstCap secondCap)
          (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8)))
            (fun i _ => middleCap i)))
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8)))
          (fun i _ => inverseCap i))
      simpa only [sectionSixP2LeafWeightD988, mul_add, Finset.mul_sum,
        Rat.cast_add, Rat.cast_sum, first, second, middle, c, s] using hsum
    _ ≤ ((T.volumeRat * p.upper : Rat) : Real) :=
      (Rat.cast_le (K := Real)).2
        (mul_le_mul_of_nonneg_left (of_decide_eq_true hv).2 T.volumeRat_nonneg)

theorem sectionSixP2Forest_integral_le_D989 (n : Nat)
    (roots : Fin n -> RationalTetrahedron)
    (trees : Fin n -> RationalTetraSubdivision SectionSixP2LeafPayloadD988)
    (target : Set (Fin 3 -> Real)) (htarget : MeasurableSet target)
    (hcover : target ⊆ ⋃ r, (roots r).region)
    (hvalid : ∀ r, (trees r).coverValid sectionSixP2LeafValidD988 (roots r) = true) :
    (∫ x in target,
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2)) ≤
        ((∑ r, (trees r).replayWeightRat (roots r) (fun _ p => p.upper) : Rat) : Real) := by
  apply rationalTetraForest_setIntegral_le_replayWeightRat_D966 n roots trees
    sectionSixP2LeafValidD988 (fun _ p => p.upper) target _ htarget hcover hvalid
  · exact sectionSixP2Leaf_integrable_D989
  · intro T p hv x hx
    exact sectionSixP2Leaf_nonneg_D989 T p hv hx
  · exact sectionSixP2Leaf_integral_le_D989

end PrimesRestrictedDigits
