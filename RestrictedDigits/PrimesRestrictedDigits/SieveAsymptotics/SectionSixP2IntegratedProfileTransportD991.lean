import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2NativeProfileRegularityD987
import PrimesRestrictedDigits.BasicEstimates.CoordinateNestedEquivD905
import PrimesRestrictedDigits.BasicEstimates.RationalAffineReciprocalCapCastsD969
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2TransformedKernel

/-!
# Integrated transport of the original P2 profile

The three root regions supply profile integrability. Existing fiber and coordinate identities
then compare the literal target with its native profile integral, without any numerical
premise or new measure normalization. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs.
(6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem root_fields_D991 (r : Fin 3) (i : Fin 4) :
    0 < sectionSixP2AffineUD983.evalReal ((sectionSixP2RootD974 r).vertexReal i) ∧
    0 < sectionSixP2AffineVD983.evalReal ((sectionSixP2RootD974 r).vertexReal i) ∧
    0 < sectionSixP2AffineDD983.evalReal ((sectionSixP2RootD974 r).vertexReal i) ∧
    0 < sectionSixP2AffineWD983.evalReal ((sectionSixP2RootD974 r).vertexReal i) ∧
    0 ≤ sectionSixP2AffineBD983.evalReal ((sectionSixP2RootD974 r).vertexReal i) := by
  have hrat : ∀ r : Fin 3, ∀ i : Fin 4,
      0 < rationalAffineEval_D969 sectionSixP2AffineUD983 ((sectionSixP2RootD974 r).vertex i) ∧
      0 < rationalAffineEval_D969 sectionSixP2AffineVD983 ((sectionSixP2RootD974 r).vertex i) ∧
      0 < rationalAffineEval_D969 sectionSixP2AffineDD983 ((sectionSixP2RootD974 r).vertex i) ∧
      0 < rationalAffineEval_D969 sectionSixP2AffineWD983 ((sectionSixP2RootD974 r).vertex i) ∧
      0 ≤ rationalAffineEval_D969 sectionSixP2AffineBD983 ((sectionSixP2RootD974 r).vertex i) := by
    decide +kernel
  have hcast (f : RationalAffine 3) :
      (rationalAffineEval_D969 f ((sectionSixP2RootD974 r).vertex i) : Real) =
        f.evalReal ((sectionSixP2RootD974 r).vertexReal i) := by
    change (rationalAffineEval_D969 f ((sectionSixP2RootD974 r).vertex i) : Real) =
      f.evalReal (fun j => ((sectionSixP2RootD974 r).vertex i j : Real))
    exact rationalAffineEval_cast_D969 f _
  rw [← hcast sectionSixP2AffineUD983, ← hcast sectionSixP2AffineVD983,
    ← hcast sectionSixP2AffineDD983, ← hcast sectionSixP2AffineWD983,
    ← hcast sectionSixP2AffineBD983]
  exact ⟨Rat.cast_pos.2 (hrat r i).1, Rat.cast_pos.2 (hrat r i).2.1,
    Rat.cast_pos.2 (hrat r i).2.2.1, Rat.cast_pos.2 (hrat r i).2.2.2.1,
    Rat.cast_nonneg.2 (hrat r i).2.2.2.2⟩

theorem sectionSixP2NativeProfile_integrable_D991 :
    IntegrableOn (fun x : Fin 3 -> Real =>
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2))
      {x | ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P2FullOuter}
      volume := by
  have hroots (r : Fin 3) : IntegrableOn (fun x : Fin 3 -> Real =>
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2))
      (sectionSixP2RootD974 r).region volume :=
    (sectionSixP2RootD974 r).sectionSixP2RefinedProfile_integrableOn_D987
      (fun i => (root_fields_D991 r i).1)
      (fun i => (root_fields_D991 r i).2.1)
      (fun i => (root_fields_D991 r i).2.2.1)
      (fun i => (root_fields_D991 r i).2.2.2.1)
      (fun i => (root_fields_D991 r i).2.2.2.2)
  exact (integrableOn_finite_iUnion.2 hroots).mono_set
    sectionSixP2FullOuter_subset_roots_D974

theorem sectionSixP2NestedProfile_integrable_D991 :
    IntegrableOn sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound
      sectionSixFirstLowCentralSmallI5P2FullOuter volume := by
  apply (coordinateNestedEquiv_preserving.integrableOn_comp_preimage
    coordinateNestedEquiv.measurableEmbedding).mp
  simpa only [Function.comp_def, Set.preimage, coordinateNestedEquiv_apply] using
    sectionSixP2NativeProfile_integrable_D991

private theorem outer_measurable_D991 :
    MeasurableSet sectionSixFirstLowCentralSmallI5P2FullOuter := by
  unfold sectionSixFirstLowCentralSmallI5P2FullOuter
  measurability

private theorem lower_measurable_D991 :
    Measurable sectionSixFirstLowCentralSmallI5P2FullLower := by
  unfold sectionSixFirstLowCentralSmallI5P2FullLower
  fun_prop

private theorem upper_measurable_D991 :
    Measurable sectionSixFirstLowCentralSmallI5P2FullUpper := by
  unfold sectionSixFirstLowCentralSmallI5P2FullUpper
  fun_prop

private theorem outer_ordered_D991 {x : ((Real × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P2FullOuter) :
    sectionSixFirstLowCentralSmallI5P2FullLower x ≤
      sectionSixFirstLowCentralSmallI5P2FullUpper x := by
  change (0 : Real) ≤ min x.2
    ((1 - sectionSixThetaTwo (1 / 1000000 : Real) -
      3 * x.1.1 - x.1.2 - x.2) / 2)
  exact le_min hx.2.2.2.1.le hx.2.2.2.2.2.2.2

private theorem inner_integrable_D991 :
    IntegrableOn (fun x : ((Real × Real) × Real) =>
      ∫ q in sectionSixFirstLowCentralSmallI5P2FullLower x..
        sectionSixFirstLowCentralSmallI5P2FullUpper x,
        sectionSixFirstLowCentralSmallI5P2TransformedKernel (x, q))
      sectionSixFirstLowCentralSmallI5P2FullOuter volume :=
  integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P2FullOuter
    sectionSixFirstLowCentralSmallI5P2FullLower
    sectionSixFirstLowCentralSmallI5P2FullUpper
    sectionSixFirstLowCentralSmallI5P2TransformedKernel
    outer_measurable_D991 lower_measurable_D991 upper_measurable_D991
    (fun _ hx => outer_ordered_D991 hx)
    sectionSixFirstLowCentralSmallI5P2FullCell_integrable

theorem sectionSixP2Domain_integral_le_profile_D991 :
    (∫ z in sectionSixFirstLowCentralSmallI5P2Domain,
      sectionSixFirstLowCentralSmallI5P2TransformedKernel z
        ∂(volume : Measure SectionSixAffineT)) ≤
      ∫ x in sectionSixFirstLowCentralSmallI5P2FullOuter,
        sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound x := by
  change (∫ z : ((Real × Real) × Real) × Real in
    sectionSixFirstLowCentralSmallI5P2Domain,
    sectionSixFirstLowCentralSmallI5P2TransformedKernel z
      ∂((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real))) ≤ _
  rw [sectionSixFirstLowCentralSmallI5P2Domain_setIntegral_eq_fullOuter_iterated]
  exact setIntegral_mono_on inner_integrable_D991 sectionSixP2NestedProfile_integrable_D991
    outer_measurable_D991 (fun _ hx =>
      sectionSixFirstLowCentralSmallI5P2FullOuter_qfiber_le_refinedProfile hx)

theorem sectionSixP2Target_integral_le_nativeProfile_D991 :
    (∫ z in sectionSixFirstLowCentralSmallI5P2Target,
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume : Measure SectionSixAffineT)) ≤
      ∫ x in {x : Fin 3 -> Real |
        ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P2FullOuter},
        sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2) := by
  rw [sectionSixFirstLowCentralSmallI5P2Target_setIntegral_eq_transformedKernel]
  have htransport := coordinateNestedEquiv_preserving.setIntegral_preimage_emb
    coordinateNestedEquiv.measurableEmbedding
    sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound
    sectionSixFirstLowCentralSmallI5P2FullOuter
  apply sectionSixP2Domain_integral_le_profile_D991.trans_eq
  simpa only [Set.preimage, coordinateNestedEquiv_apply] using htransport.symm

end PrimesRestrictedDigits
