import BoundedGaps.Maynard.VariationalBounds
import BoundedGaps.Maynard.FaceDecomposition

/-!
# Boundedness of Maynard's variational quotient

The coordinate split, Fubini, and the unit-interval `L²` bound show that each
face functional is at most the denominator. Thus the `k = 105` ratio set is
bounded above by 105, supplying the side condition needed by `sSup`.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

theorem maynardJ_le_I (F : (Fin 105 → ℝ) → ℝ)
    (hF : MaynardAdmissible 105 F) (m : Fin 105) :
    maynardJ 105 m F ≤ maynardI 105 F := by
  let e := faceCoordinateEquiv m
  let sx : Set ℝ := Set.Icc (0 : ℝ) 1
  let st : Set (maynardFaceIndex 105 m → ℝ) :=
    maynardCubeOf (maynardFaceIndex 105 m)
  let g : ℝ × (maynardFaceIndex 105 m → ℝ) → ℝ :=
    fun z => F (e.symm z) ^ 2
  have he := faceCoordinateEquiv_measurePreserving m
  have hesymm := he.symm e
  have hprodOn : IntegrableOn g (sx ×ˢ st) := by
    have h := (hesymm.integrableOn_comp_preimage
      e.symm.measurableEmbedding).mpr hF.2.1
    rw [faceCoordinateEquiv_symm_preimage_cube] at h
    exact h
  have hprod : Integrable g
      ((volume.restrict sx).prod (volume.restrict st)) := by
    rw [Measure.prod_restrict]
    simpa only [Measure.volume_eq_prod] using hprodOn.integrable
  have htransport :
      (∫ z in sx ×ˢ st, g z) =
        ∫ u in maynardCube 105, F u ^ 2 := by
    have h := hesymm.setIntegral_preimage_emb e.symm.measurableEmbedding
      (fun u : Fin 105 → ℝ => F u ^ 2) (maynardCube 105)
    rw [faceCoordinateEquiv_symm_preimage_cube] at h
    exact h
  have hfubini :
      (∫ z in sx ×ˢ st, g z) =
        ∫ t in st, ∫ x in sx, F (maynardInsertCoordinate m x t) ^ 2 := by
    rw [Measure.volume_eq_prod]
    rw [← Measure.prod_restrict]
    rw [integral_prod_symm g hprod]
    apply integral_congr_ae
    filter_upwards [] with t
    apply integral_congr_ae
    filter_upwards [] with x
    simp [g, e, faceCoordinateEquiv_symm_apply]
  have hsection : ∀ᵐ t ∂volume.restrict st,
      Integrable (fun x => F (maynardInsertCoordinate m x t) ^ 2)
        (volume.restrict sx) := by
    have h := hprod.prod_left_ae
    filter_upwards [h] with t ht
    simpa [g, e, faceCoordinateEquiv_symm_apply] using ht
  have hright : Integrable
      (fun t => ∫ x in sx, F (maynardInsertCoordinate m x t) ^ 2)
      (volume.restrict st) := by
    have h := hprod.integral_prod_right
    simpa [g, e, faceCoordinateEquiv_symm_apply] using h
  have hleft : Integrable
      (fun t => (∫ x in sx, F (maynardInsertCoordinate m x t)) ^ 2)
      (volume.restrict st) := hF.2.2.2 m
  have hpoint :
      (fun t => (∫ x in sx, F (maynardInsertCoordinate m x t)) ^ 2) ≤ᵐ[
        volume.restrict st]
      (fun t => ∫ x in sx, F (maynardInsertCoordinate m x t) ^ 2) := by
    filter_upwards [hsection] with t ht
    have hmeas : AEStronglyMeasurable
        (fun x => F (maynardInsertCoordinate m x t))
        (volume.restrict sx) :=
      (hF.2.2.1 m t).aestronglyMeasurable
    have hlp : MemLp (fun x => F (maynardInsertCoordinate m x t)) 2
        (volume.restrict sx) :=
      (memLp_two_iff_integrable_sq hmeas).2 ht
    exact unitInterval_integral_sq_le _ hlp
  have hJ := integral_mono_ae hleft hright hpoint
  unfold maynardJ maynardI
  rw [← htransport, hfubini]
  exact hJ

theorem maynardNumerator_le (F : (Fin 105 → ℝ) → ℝ)
    (hF : MaynardAdmissible 105 F) :
    (∑ m : Fin 105, maynardJ 105 m F) ≤ 105 * maynardI 105 F := by
  calc
    (∑ m : Fin 105, maynardJ 105 m F) ≤
        ∑ _m : Fin 105, maynardI 105 F :=
      Finset.sum_le_sum (fun m hm => maynardJ_le_I F hF m)
    _ = 105 * maynardI 105 F := by simp

theorem maynardRatio_le (F : (Fin 105 → ℝ) → ℝ)
    (hF : MaynardAdmissible 105 F) (hI : 0 < maynardI 105 F) :
    maynardRatio 105 F ≤ 105 := by
  rw [maynardRatio]
  rw [div_le_iff₀ hI]
  simpa [mul_comm] using maynardNumerator_le F hF

theorem maynardRatioSet_105_bddAbove : BddAbove (maynardRatioSet 105) := by
  refine ⟨105, ?_⟩
  intro r hr
  rcases hr with ⟨F, hF, hI, rfl⟩
  exact maynardRatio_le F hF hI

end
end BoundedGaps.Maynard
