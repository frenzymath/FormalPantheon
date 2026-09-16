import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2NativeAffineSlotsD986

/-!
# Sign and integrability of the native P2 profile

The exact affine-slot decomposition is nonnegative and integrable under vertex-checkable
positivity conditions. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

private theorem constantPayload_nonneg_D987
    {u v W l h C : Real} (hu : 0 < u) (hv : 0 < v) (hW : 0 < W)
    (hl : 0 < l) (hlh : l ≤ h) (hC : 0 ≤ C) :
    0 ≤ sectionSixBuchstabConstantPayload u v W l h C := by
  unfold sectionSixBuchstabConstantPayload
  exact mul_nonneg (div_nonneg hC (by positivity))
    (sub_nonneg.mpr (one_div_le_one_div_of_le hl hlh))

private theorem clampedConstantPayload_nonneg_D987
    {u v d W rhoL rhoH C : Real}
    (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) (hW : 0 < W)
    (hrho : rhoL ≤ rhoH) (hC : 0 ≤ C) :
    0 ≤ sectionSixBuchstabConstantPayload u v W
      (max d (min W rhoL)) (max d (min W rhoH)) C := by
  exact constantPayload_nonneg_D987 hu hv hW
    (hd.trans_le (le_max_left _ _))
    (max_le_max_left d (min_le_min_left W hrho)) hC

private theorem clampedConstantPayload_from_self_nonneg_D987
    {u v d W rhoH C : Real}
    (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) (hW : 0 < W) (hC : 0 ≤ C) :
    0 ≤ sectionSixBuchstabConstantPayload u v W
      (max d (min W d)) (max d (min W rhoH)) C := by
  rw [max_eq_left (min_le_right W d)]
  exact constantPayload_nonneg_D987 hu hv hW hd (le_max_left _ _) hC

private theorem clampedSecantPayload_nonneg_D987
    {u v d W rhoL rhoH B a b : Real}
    (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) (hW : 0 < W)
    (hrho : rhoL ≤ rhoH) (ha : 0 < a) (hb : 0 < b)
    (hwall : B ≤ (b + 1) * rhoL) :
    0 ≤ sectionSixBuchstabSecantPayload u v W B
      (max d (min W rhoL)) (max d (min W rhoH)) a b := by
  let L := max d (min W rhoL)
  let H := max d (min W rhoH)
  change 0 ≤ sectionSixBuchstabSecantPayload u v W B L H a b
  have hLH : L ≤ H := by
    dsimp only [L, H]
    exact max_le_max_left d (min_le_min_left W hrho)
  have hLpos : 0 < L := by
    exact hd.trans_le (by dsimp only [L]; exact le_max_left _ _)
  by_cases hpos : 0 < H - L
  · have hshape := sectionSixBuchstabClampedEndpoints_of_posWidth_D976
      (d := d) (W := W) (rhoL := rhoL) (rhoH := rhoH) hpos
    have hrhoLle : rhoL ≤ L := by
      dsimp only [L]
      rw [hshape.1]
      exact le_max_right _ _
    have hwallL : B ≤ (b + 1) * L :=
      hwall.trans (mul_le_mul_of_nonneg_left hrhoLle (by linarith))
    exact sectionSixBuchstabSecantPayload_nonneg_D977
      hu hv hW hLpos hLH ha hb hwallL
  · have hzero : H - L = 0 :=
      le_antisymm (le_of_not_gt hpos) (sub_nonneg.mpr hLH)
    have hHL : H = L := by linarith
    rw [hHL]
    simp [sectionSixBuchstabSecantPayload]

private theorem affine_positive_on_region_D987
    (T : RationalTetrahedron) (a : RationalAffine 3)
    (ha : ∀ i, 0 < a.evalReal (T.vertexReal i))
    {x : Fin 3 -> Real} (hx : x ∈ T.region) : 0 < a.evalReal x := by
  rcases hx with ⟨w, hw, hsum, rfl⟩
  rw [a.evalReal_barycentricPoint3 T.vertexReal w hsum]
  have h := (convex_Ioi (0 : Real)).sum_mem
    (t := (Finset.univ : Finset (Fin 4))) (w := w)
    (z := fun i => a.evalReal (T.vertexReal i))
    (fun i _ => hw i) hsum (fun i _ => ha i)
  simpa only [smul_eq_mul, mem_Ioi] using h

theorem sectionSixP2RefinedProfile_nonneg_D987 (x : Fin 3 -> Real)
    (hU : 0 < sectionSixP2AffineUD983.evalReal x)
    (hV : 0 < sectionSixP2AffineVD983.evalReal x)
    (hD : 0 < sectionSixP2AffineDD983.evalReal x)
    (hW : 0 < sectionSixP2AffineWD983.evalReal x)
    (hB : 0 ≤ sectionSixP2AffineBD983.evalReal x) :
    0 ≤ sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound
      ((x 0, x 1), x 2) := by
  rw [sectionSixP2RefinedProfile_eq_affineSlots_D986 x hB]
  have hfirst : 0 ≤ sectionSixP2ClampedConstantAffinePayloadD981
      sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
      sectionSixP2AffineWD983 sectionSixP2AffineDD983
      (sectionSixP2BudgetMultipleD983 (4 / 17)) (281 / 500) x := by
    unfold sectionSixP2ClampedConstantAffinePayloadD981
    exact clampedConstantPayload_from_self_nonneg_D987 hU hV hD hW (by norm_num)
  have hsecond : 0 ≤ sectionSixP2ClampedConstantAffinePayloadD981
      sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
      sectionSixP2AffineWD983 (sectionSixP2BudgetMultipleD983 (4 / 17))
      (sectionSixP2BudgetMultipleD983 (1 / 4)) (564383 / 1000000) x := by
    unfold sectionSixP2ClampedConstantAffinePayloadD981
    apply clampedConstantPayload_nonneg_D987 hU hV hD hW
    · simp only [sectionSixP2BudgetMultipleD983_eval]
      norm_num
      linarith
    · norm_num
  have hmiddle : 0 ≤ ∑ i : Fin 8, sectionSixP2ClampedConstantAffinePayloadD981
      sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
      sectionSixP2AffineWD983 (sectionSixP2MiddleLowerD986 i)
      (sectionSixP2MiddleUpperD986 i) (sectionSixP2MiddleCapRatD986 i : Real) x := by
    apply Finset.sum_nonneg
    intro i hi
    unfold sectionSixP2ClampedConstantAffinePayloadD981
    apply clampedConstantPayload_nonneg_D987 hU hV hD hW
    · rw [sectionSixP2MiddleLowerD986_eval, sectionSixP2MiddleUpperD986_eval]
      fin_cases i <;> norm_num <;> nlinarith
    · fin_cases i <;> norm_num [sectionSixP2MiddleCapRatD986]
  have hinverse : 0 ≤ ∑ i : Fin 8, sectionSixP2ClampedInverseAffinePayloadD982
      sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
      sectionSixP2AffineWD983 (sectionSixP2InverseLowerD986 i)
      (sectionSixP2InverseUpperD986 i) sectionSixP2AffineBD983
      (sectionSixP2InverseArgumentLowerD986 i : Real)
      (sectionSixP2InverseArgumentUpperD986 i : Real) x := by
    apply Finset.sum_nonneg
    intro i hi
    unfold sectionSixP2ClampedInverseAffinePayloadD982
    apply clampedSecantPayload_nonneg_D987 hU hV hD hW
    · rw [sectionSixP2InverseLowerD986_eval, sectionSixP2InverseUpperD986_eval]
      fin_cases i <;> norm_num <;> nlinarith
    · fin_cases i <;> norm_num [sectionSixP2InverseArgumentLowerD986]
    · fin_cases i <;> norm_num [sectionSixP2InverseArgumentUpperD986]
    · rw [sectionSixP2InverseLowerD986_eval]
      fin_cases i <;> norm_num [sectionSixP2InverseArgumentUpperD986] <;>
        ring_nf <;> exact le_rfl
  exact add_nonneg (add_nonneg (add_nonneg hfirst hsecond) hmiddle) hinverse

theorem RationalTetrahedron.sectionSixP2RefinedProfile_integrableOn_D987
    (T : RationalTetrahedron)
    (hU : ∀ i, 0 < sectionSixP2AffineUD983.evalReal (T.vertexReal i))
    (hV : ∀ i, 0 < sectionSixP2AffineVD983.evalReal (T.vertexReal i))
    (hD : ∀ i, 0 < sectionSixP2AffineDD983.evalReal (T.vertexReal i))
    (hW : ∀ i, 0 < sectionSixP2AffineWD983.evalReal (T.vertexReal i))
    (hB : ∀ i, 0 ≤ sectionSixP2AffineBD983.evalReal (T.vertexReal i)) :
    IntegrableOn (fun x : Fin 3 -> Real =>
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2))
      T.region volume := by
  have hfirst := T.sectionSixP2ConstantAffine_integrableOn_D981
    sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
    sectionSixP2AffineWD983 sectionSixP2AffineDD983
    (sectionSixP2BudgetMultipleD983 (4 / 17)) (281 / 500) hU hV hD hW
  have hsecond := T.sectionSixP2ConstantAffine_integrableOn_D981
    sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
    sectionSixP2AffineWD983 (sectionSixP2BudgetMultipleD983 (4 / 17))
    (sectionSixP2BudgetMultipleD983 (1 / 4)) (564383 / 1000000) hU hV hD hW
  have hmiddle : IntegrableOn (fun x : Fin 3 -> Real =>
      ∑ i : Fin 8, sectionSixP2ClampedConstantAffinePayloadD981
        sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
        sectionSixP2AffineWD983 (sectionSixP2MiddleLowerD986 i)
      (sectionSixP2MiddleUpperD986 i) (sectionSixP2MiddleCapRatD986 i : Real) x)
      T.region volume := by
    change Integrable _ (volume.restrict T.region)
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin 8)) fun i hi =>
      T.sectionSixP2ConstantAffine_integrableOn_D981
        sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
        sectionSixP2AffineWD983 (sectionSixP2MiddleLowerD986 i)
        (sectionSixP2MiddleUpperD986 i) (sectionSixP2MiddleCapRatD986 i : Real)
        hU hV hD hW
  have hinverse : IntegrableOn (fun x : Fin 3 -> Real =>
      ∑ i : Fin 8, sectionSixP2ClampedInverseAffinePayloadD982
        sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
        sectionSixP2AffineWD983 (sectionSixP2InverseLowerD986 i)
        (sectionSixP2InverseUpperD986 i) sectionSixP2AffineBD983
        (sectionSixP2InverseArgumentLowerD986 i : Real)
        (sectionSixP2InverseArgumentUpperD986 i : Real) x) T.region volume := by
    change Integrable _ (volume.restrict T.region)
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin 8)) fun i hi =>
      T.sectionSixP2InverseAffine_integrableOn_D982
        sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
        sectionSixP2AffineWD983 (sectionSixP2InverseLowerD986 i)
        (sectionSixP2InverseUpperD986 i) sectionSixP2AffineBD983
        (sectionSixP2InverseArgumentLowerD986 i : Real)
        (sectionSixP2InverseArgumentUpperD986 i : Real) hU hV hD hW
  have hslots : IntegrableOn (fun x : Fin 3 -> Real =>
      sectionSixP2ClampedConstantAffinePayloadD981
        sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
        sectionSixP2AffineWD983 sectionSixP2AffineDD983
        (sectionSixP2BudgetMultipleD983 (4 / 17)) (281 / 500) x +
      sectionSixP2ClampedConstantAffinePayloadD981
        sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
        sectionSixP2AffineWD983 (sectionSixP2BudgetMultipleD983 (4 / 17))
        (sectionSixP2BudgetMultipleD983 (1 / 4)) (564383 / 1000000) x +
      (∑ i : Fin 8, sectionSixP2ClampedConstantAffinePayloadD981
        sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
        sectionSixP2AffineWD983 (sectionSixP2MiddleLowerD986 i)
        (sectionSixP2MiddleUpperD986 i) (sectionSixP2MiddleCapRatD986 i : Real) x) +
      ∑ i : Fin 8, sectionSixP2ClampedInverseAffinePayloadD982
        sectionSixP2AffineUD983 sectionSixP2AffineVD983 sectionSixP2AffineDD983
        sectionSixP2AffineWD983 (sectionSixP2InverseLowerD986 i)
        (sectionSixP2InverseUpperD986 i) sectionSixP2AffineBD983
        (sectionSixP2InverseArgumentLowerD986 i : Real)
        (sectionSixP2InverseArgumentUpperD986 i : Real) x) T.region volume := by
    exact ((hfirst.add hsecond).add hmiddle).add hinverse
  apply hslots.congr_fun
  · intro x hx
    exact (sectionSixP2RefinedProfile_eq_affineSlots_D986 x
      (T.affine_eval_ge_of_vertices sectionSixP2AffineBD983 hB x hx)).symm
  · exact T.region_measurable_D924

theorem RationalTetrahedron.sectionSixP2RefinedProfile_nonneg_D987
    (T : RationalTetrahedron)
    (hU : ∀ i, 0 < sectionSixP2AffineUD983.evalReal (T.vertexReal i))
    (hV : ∀ i, 0 < sectionSixP2AffineVD983.evalReal (T.vertexReal i))
    (hD : ∀ i, 0 < sectionSixP2AffineDD983.evalReal (T.vertexReal i))
    (hW : ∀ i, 0 < sectionSixP2AffineWD983.evalReal (T.vertexReal i))
    (hB : ∀ i, 0 ≤ sectionSixP2AffineBD983.evalReal (T.vertexReal i)) :
    ∀ x ∈ T.region,
      0 ≤ sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound
        ((x 0, x 1), x 2) := by
  intro x hx
  exact PrimesRestrictedDigits.sectionSixP2RefinedProfile_nonneg_D987 x
    (affine_positive_on_region_D987 T sectionSixP2AffineUD983 hU hx)
    (affine_positive_on_region_D987 T sectionSixP2AffineVD983 hV hx)
    (affine_positive_on_region_D987 T sectionSixP2AffineDD983 hD hx)
    (affine_positive_on_region_D987 T sectionSixP2AffineWD983 hW hx)
    (T.affine_eval_ge_of_vertices sectionSixP2AffineBD983 hB x hx)

end
end PrimesRestrictedDigits
