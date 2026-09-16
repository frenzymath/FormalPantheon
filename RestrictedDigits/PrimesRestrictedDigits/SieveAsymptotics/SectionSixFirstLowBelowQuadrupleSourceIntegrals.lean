import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleRegions
import Mathlib.Analysis.Convex.Measure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The literal source integral for the low-below clean quadruple term

The exact clean region retains three weak role-order faces. Maynard's literal `R_4` region
opens those faces and adds an upper-coordinate wall that follows from the accepted parameter
range. This file removes precisely the three null affine faces.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13), region `R_4`.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private abbrev LowBelowQuadruple := ((Real × Real) × Real) × Real

private abbrev lowBelowSourceTriple :
    LowBelowQuadruple →ₗ[Real] ((Real × Real) × Real) :=
  LinearMap.fst Real ((Real × Real) × Real) Real

private abbrev lowBelowSourcePair :
    LowBelowQuadruple →ₗ[Real] (Real × Real) :=
  (LinearMap.fst Real (Real × Real) Real).comp lowBelowSourceTriple

private abbrev lowBelowSourceU : LowBelowQuadruple →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp lowBelowSourcePair

private abbrev lowBelowSourceV : LowBelowQuadruple →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp lowBelowSourcePair

private abbrev lowBelowSourceW : LowBelowQuadruple →ₗ[Real] Real :=
  (LinearMap.snd Real (Real × Real) Real).comp lowBelowSourceTriple

private abbrev lowBelowSourceT : LowBelowQuadruple →ₗ[Real] Real :=
  LinearMap.snd Real ((Real × Real) × Real) Real

private def lowBelowSourceTWFace : Set LowBelowQuadruple :=
  {x | x.2 = x.1.2}

private def lowBelowSourceWVFace : Set LowBelowQuadruple :=
  {x | x.1.2 = x.1.1.2}

private def lowBelowSourceVUFace : Set LowBelowQuadruple :=
  {x | x.1.1.2 = x.1.1.1}

private def lowBelowSourceBoundary : Set LowBelowQuadruple :=
  lowBelowSourceTWFace ∪ lowBelowSourceWVFace ∪ lowBelowSourceVUFace

local instance lowBelowSourcePairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance lowBelowSourceTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance lowBelowSourceFourfoldHaar :
    Measure.IsAddHaarMeasure (volume : Measure LowBelowQuadruple) :=
  Measure.prod.instIsAddHaarMeasure volume volume

private theorem volume_lowBelowLinearLevelSet_eq_zero
    (L : LowBelowQuadruple →ₗ[Real] Real) (hL : L ≠ 0)
    (c : Real) (y : LowBelowQuadruple) (hy : L y = c) :
    volume {x | L x = c} = 0 := by
  let s : AffineSubspace Real LowBelowQuadruple := AffineSubspace.mk' y L.ker
  have hset : {x | L x = c} = (s : Set LowBelowQuadruple) := by
    ext x
    change L x = c ↔ L (x - y) = 0
    rw [map_sub, hy, sub_eq_zero]
  rw [hset]
  apply Measure.addHaar_affineSubspace
  intro hs
  have hdirection := congrArg AffineSubspace.direction hs
  have hker : L.ker = ⊤ := by
    simpa [s] using hdirection
  exact hL ((LinearMap.ker_eq_top).mp hker)

private theorem lowBelowSourceTWMap_ne_zero :
    lowBelowSourceT - lowBelowSourceW ≠ 0 := by
  intro h
  have hpoint := congrArg
    (fun L : LowBelowQuadruple →ₗ[Real] Real => L (((0, 0), 0), 1)) h
  norm_num [lowBelowSourceT, lowBelowSourceW, lowBelowSourceTriple] at hpoint

private theorem lowBelowSourceWVMap_ne_zero :
    lowBelowSourceW - lowBelowSourceV ≠ 0 := by
  intro h
  have hpoint := congrArg
    (fun L : LowBelowQuadruple →ₗ[Real] Real => L (((0, 0), 1), 0)) h
  norm_num [lowBelowSourceW, lowBelowSourceV, lowBelowSourcePair,
    lowBelowSourceTriple] at hpoint

private theorem lowBelowSourceVUMap_ne_zero :
    lowBelowSourceV - lowBelowSourceU ≠ 0 := by
  intro h
  have hpoint := congrArg
    (fun L : LowBelowQuadruple →ₗ[Real] Real => L (((0, 1), 0), 0)) h
  norm_num [lowBelowSourceV, lowBelowSourceU, lowBelowSourcePair,
    lowBelowSourceTriple] at hpoint

private theorem volume_lowBelowSourceTWFace :
    volume lowBelowSourceTWFace = 0 := by
  simpa [lowBelowSourceTWFace, lowBelowSourceT, lowBelowSourceW,
    lowBelowSourceTriple, sub_eq_zero] using
      volume_lowBelowLinearLevelSet_eq_zero
        (lowBelowSourceT - lowBelowSourceW) lowBelowSourceTWMap_ne_zero 0 0
          (by simp)

private theorem volume_lowBelowSourceWVFace :
    volume lowBelowSourceWVFace = 0 := by
  simpa [lowBelowSourceWVFace, lowBelowSourceW, lowBelowSourceV,
    lowBelowSourcePair, lowBelowSourceTriple, sub_eq_zero] using
      volume_lowBelowLinearLevelSet_eq_zero
        (lowBelowSourceW - lowBelowSourceV) lowBelowSourceWVMap_ne_zero 0 0
          (by simp)

private theorem volume_lowBelowSourceVUFace :
    volume lowBelowSourceVUFace = 0 := by
  simpa [lowBelowSourceVUFace, lowBelowSourceV, lowBelowSourceU,
    lowBelowSourcePair, lowBelowSourceTriple, sub_eq_zero] using
      volume_lowBelowLinearLevelSet_eq_zero
        (lowBelowSourceV - lowBelowSourceU) lowBelowSourceVUMap_ne_zero 0 0
          (by simp)

private theorem volume_lowBelowSourceBoundary :
    volume lowBelowSourceBoundary = 0 := by
  unfold lowBelowSourceBoundary
  exact measure_union_null
    (measure_union_null volume_lowBelowSourceTWFace volume_lowBelowSourceWVFace)
    volume_lowBelowSourceVUFace

private theorem lowBelowSourceRegion_subset_exact (epsilon : Real) :
    sectionSixFirstLowBelowQuadrupleSourceRegion epsilon ⊆
      sectionSixFirstLowBelowQuadrupleRegion epsilon := by
  rintro x ⟨hgap, htw, hwv, hvu, _hu, huv, hA, hB, hC, hD, hE, hF⟩
  exact ⟨hgap, htw.le, hwv.le, hvu.le, huv, hA, hB, hC, hD, hE, hF⟩

private theorem lowBelowExact_sdiff_source_subset_boundary
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64) :
    sectionSixFirstLowBelowQuadrupleRegion epsilon \
        sectionSixFirstLowBelowQuadrupleSourceRegion epsilon ⊆
      lowBelowSourceBoundary := by
  rintro x ⟨hexact, hnotSource⟩
  rcases hexact with
    ⟨hgap, htw, hwv, hvu, huv, hA, hB, hC, hD, hE, hF⟩
  by_contra hnotBoundary
  have htw' : x.2 < x.1.2 := lt_of_le_of_ne htw fun h =>
    hnotBoundary (by simp [lowBelowSourceBoundary, lowBelowSourceTWFace, h])
  have hwv' : x.1.2 < x.1.1.2 := lt_of_le_of_ne hwv fun h =>
    hnotBoundary (by simp [lowBelowSourceBoundary, lowBelowSourceWVFace, h])
  have hvu' : x.1.1.2 < x.1.1.1 := lt_of_le_of_ne hvu fun h =>
    hnotBoundary (by simp [lowBelowSourceBoundary, lowBelowSourceVUFace, h])
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hu : x.1.1.1 < sectionSixThetaOne epsilon := by
    linarith
  apply hnotSource
  exact ⟨hgap, htw', hwv', hvu', hu, huv, hA, hB, hC, hD, hE, hF⟩

private theorem lowBelowExact_ae_eq_source
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64) :
    sectionSixFirstLowBelowQuadrupleRegion epsilon =ᵐ[volume]
      sectionSixFirstLowBelowQuadrupleSourceRegion epsilon := by
  rw [ae_eq_set]
  constructor
  · exact measure_mono_null
      (lowBelowExact_sdiff_source_subset_boundary epsilon hepsilon
        hepsilonSmall)
      volume_lowBelowSourceBoundary
  · rw [measure_eq_zero_iff_ae_notMem]
    exact ae_of_all _ fun x hx =>
      hx.2 (lowBelowSourceRegion_subset_exact epsilon hx.1)

theorem sectionSixFirstLowBelowQuadrupleIntegral_eq_source
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowBelowQuadrupleIntegral epsilon =
      ∫ x in sectionSixFirstLowBelowQuadrupleSourceRegion epsilon,
        sectionSixFirstLowBelowQuadrupleKernel x := by
  unfold sectionSixFirstLowBelowQuadrupleIntegral
  apply setIntegral_congr_set
  exact lowBelowExact_ae_eq_source epsilon hepsilon hepsilonSmall

end

end PrimesRestrictedDigits
