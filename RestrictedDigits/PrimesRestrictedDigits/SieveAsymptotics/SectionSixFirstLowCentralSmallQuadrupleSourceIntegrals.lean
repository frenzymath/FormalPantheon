import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleRegions
import Mathlib.Analysis.Convex.Measure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The literal source integral for the low central-small clean quadruple term

The exact clean carrier and Maynard's source region share all five closed-band exclusions.
They differ only where a weak role, outer-cutoff, or terminal-cap wall is an equality. This
file removes those five null affine faces.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12), region `R_3`.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private abbrev LowQuadruple := ((Real × Real) × Real) × Real

private abbrev lowSourceTriple :
    LowQuadruple →ₗ[Real] ((Real × Real) × Real) :=
  LinearMap.fst Real ((Real × Real) × Real) Real

private abbrev lowSourcePair : LowQuadruple →ₗ[Real] (Real × Real) :=
  (LinearMap.fst Real (Real × Real) Real).comp lowSourceTriple

private abbrev lowSourceU : LowQuadruple →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp lowSourcePair

private abbrev lowSourceV : LowQuadruple →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp lowSourcePair

private abbrev lowSourceW : LowQuadruple →ₗ[Real] Real :=
  (LinearMap.snd Real (Real × Real) Real).comp lowSourceTriple

private abbrev lowSourceT : LowQuadruple →ₗ[Real] Real :=
  LinearMap.snd Real ((Real × Real) × Real) Real

private abbrev lowSourceCap : LowQuadruple →ₗ[Real] Real :=
  lowSourceU + lowSourceV + lowSourceW + (2 : Real) • lowSourceT

private def lowSourceTWFace : Set LowQuadruple :=
  {x | x.2 = x.1.2}

private def lowSourceWVFace : Set LowQuadruple :=
  {x | x.1.2 = x.1.1.2}

private def lowSourceVUFace : Set LowQuadruple :=
  {x | x.1.1.2 = x.1.1.1}

private def lowSourceUFace (epsilon : Real) : Set LowQuadruple :=
  {x | x.1.1.1 = sectionSixThetaOne epsilon}

private def lowSourceCapFace : Set LowQuadruple :=
  {x | x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 = 1}

private def lowSourceBoundary (epsilon : Real) : Set LowQuadruple :=
  lowSourceTWFace ∪ lowSourceWVFace ∪ lowSourceVUFace ∪
    lowSourceUFace epsilon ∪ lowSourceCapFace

local instance lowSourcePairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance lowSourceTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance lowSourceFourfoldHaar :
    Measure.IsAddHaarMeasure (volume : Measure LowQuadruple) :=
  Measure.prod.instIsAddHaarMeasure volume volume

private theorem volume_linearLevelSet_eq_zero
    (L : LowQuadruple →ₗ[Real] Real) (hL : L ≠ 0)
    (c : Real) (y : LowQuadruple) (hy : L y = c) :
    volume {x | L x = c} = 0 := by
  let s : AffineSubspace Real LowQuadruple := AffineSubspace.mk' y L.ker
  have hset : {x | L x = c} = (s : Set LowQuadruple) := by
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

private theorem lowSourceTWMap_ne_zero : lowSourceT - lowSourceW ≠ 0 := by
  intro h
  have hpoint := congrArg
    (fun L : LowQuadruple →ₗ[Real] Real => L (((0, 0), 0), 1)) h
  norm_num [lowSourceT, lowSourceW, lowSourceTriple] at hpoint

private theorem lowSourceWVMap_ne_zero : lowSourceW - lowSourceV ≠ 0 := by
  intro h
  have hpoint := congrArg
    (fun L : LowQuadruple →ₗ[Real] Real => L (((0, 0), 1), 0)) h
  norm_num [lowSourceW, lowSourceV, lowSourcePair, lowSourceTriple] at hpoint

private theorem lowSourceVUMap_ne_zero : lowSourceV - lowSourceU ≠ 0 := by
  intro h
  have hpoint := congrArg
    (fun L : LowQuadruple →ₗ[Real] Real => L (((0, 1), 0), 0)) h
  norm_num [lowSourceV, lowSourceU, lowSourcePair, lowSourceTriple] at hpoint

private theorem lowSourceUMap_ne_zero : lowSourceU ≠ 0 := by
  intro h
  have hpoint := congrArg
    (fun L : LowQuadruple →ₗ[Real] Real => L (((1, 0), 0), 0)) h
  norm_num [lowSourceU, lowSourcePair, lowSourceTriple] at hpoint

private theorem lowSourceCapMap_ne_zero : lowSourceCap ≠ 0 := by
  intro h
  have hpoint := congrArg
    (fun L : LowQuadruple →ₗ[Real] Real => L (((1, 0), 0), 0)) h
  norm_num [lowSourceCap, lowSourceU, lowSourceV, lowSourceW, lowSourceT,
    lowSourcePair, lowSourceTriple] at hpoint

private theorem volume_lowSourceTWFace : volume lowSourceTWFace = 0 := by
  simpa [lowSourceTWFace, lowSourceT, lowSourceW, lowSourceTriple,
    sub_eq_zero] using
      volume_linearLevelSet_eq_zero (lowSourceT - lowSourceW)
        lowSourceTWMap_ne_zero 0 0 (by simp)

private theorem volume_lowSourceWVFace : volume lowSourceWVFace = 0 := by
  simpa [lowSourceWVFace, lowSourceW, lowSourceV, lowSourcePair,
    lowSourceTriple, sub_eq_zero] using
      volume_linearLevelSet_eq_zero (lowSourceW - lowSourceV)
        lowSourceWVMap_ne_zero 0 0 (by simp)

private theorem volume_lowSourceVUFace : volume lowSourceVUFace = 0 := by
  simpa [lowSourceVUFace, lowSourceV, lowSourceU, lowSourcePair,
    lowSourceTriple, sub_eq_zero] using
      volume_linearLevelSet_eq_zero (lowSourceV - lowSourceU)
        lowSourceVUMap_ne_zero 0 0 (by simp)

private theorem volume_lowSourceUFace (epsilon : Real) :
    volume (lowSourceUFace epsilon) = 0 := by
  let y : LowQuadruple :=
    (((sectionSixThetaOne epsilon, 0), 0), 0)
  simpa [lowSourceUFace, lowSourceU, lowSourcePair, lowSourceTriple] using
    volume_linearLevelSet_eq_zero lowSourceU lowSourceUMap_ne_zero
      (sectionSixThetaOne epsilon) y (by simp [y, lowSourceU, lowSourcePair,
        lowSourceTriple])

private theorem volume_lowSourceCapFace : volume lowSourceCapFace = 0 := by
  let y : LowQuadruple := (((1, 0), 0), 0)
  simpa [lowSourceCapFace, lowSourceCap, lowSourceU, lowSourceV, lowSourceW,
    lowSourceT, lowSourcePair, lowSourceTriple] using
      volume_linearLevelSet_eq_zero lowSourceCap lowSourceCapMap_ne_zero 1 y
        (by simp [y, lowSourceCap, lowSourceU, lowSourceV, lowSourceW,
          lowSourceT, lowSourcePair, lowSourceTriple])

private theorem volume_lowSourceBoundary (epsilon : Real) :
    volume (lowSourceBoundary epsilon) = 0 := by
  unfold lowSourceBoundary
  exact measure_union_null
    (measure_union_null
      (measure_union_null
        (measure_union_null volume_lowSourceTWFace volume_lowSourceWVFace)
        volume_lowSourceVUFace)
      (volume_lowSourceUFace epsilon))
    volume_lowSourceCapFace

private theorem lowSourceRegion_subset_exact (epsilon : Real) :
    sectionSixFirstLowCentralSmallQuadrupleSourceRegion epsilon ⊆
      sectionSixFirstLowCentralSmallQuadrupleRegion epsilon := by
  rintro x ⟨hgap, htw, hwv, hvu, hu, hsquare, _hcapW, hcap,
    hcentral, _hcentralUpper, _hpq, huw, hut, hvw, hvt, hwt⟩
  exact ⟨hgap, htw.le, hwv.le, hvu.le, hu.le, hcentral, hsquare, hcap.le,
    huw, hut, hvw, hvt, hwt⟩

private theorem lowExact_sdiff_source_subset_boundary
    (epsilon : Real) :
    sectionSixFirstLowCentralSmallQuadrupleRegion epsilon \
        sectionSixFirstLowCentralSmallQuadrupleSourceRegion epsilon ⊆
      lowSourceBoundary epsilon := by
  rintro x ⟨hexact, hnotSource⟩
  rcases hexact with ⟨hgap, htw, hwv, hvu, hu, hcentral, hsquare, hcap,
    huw, hut, hvw, hvt, hwt⟩
  by_contra hnotBoundary
  have htw' : x.2 < x.1.2 := lt_of_le_of_ne htw fun h =>
    hnotBoundary (by simp [lowSourceBoundary, lowSourceTWFace, h])
  have hwv' : x.1.2 < x.1.1.2 := lt_of_le_of_ne hwv fun h =>
    hnotBoundary (by simp [lowSourceBoundary, lowSourceWVFace, h])
  have hvu' : x.1.1.2 < x.1.1.1 := lt_of_le_of_ne hvu fun h =>
    hnotBoundary (by simp [lowSourceBoundary, lowSourceVUFace, h])
  have hu' : x.1.1.1 < sectionSixThetaOne epsilon :=
    lt_of_le_of_ne hu fun h =>
      hnotBoundary (by simp [lowSourceBoundary, lowSourceUFace, h])
  have hcap' : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 :=
    lt_of_le_of_ne hcap fun h =>
      hnotBoundary (by simp [lowSourceBoundary, lowSourceCapFace, h])
  have hcapW : x.1.1.1 + x.1.1.2 + 2 * x.1.2 < 1 := by
    linarith
  have hcentralUpper :
      x.1.1.1 + x.1.1.2 < 1 - sectionSixThetaTwo epsilon := by
    simp only [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
      at hgap hsquare ⊢
    linarith
  have hpq : x.1.1.1 + x.1.1.2 ∉
      Set.Icc (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) := by
    intro hpq
    exact (not_lt_of_ge hpq.2) hcentral
  apply hnotSource
  exact ⟨hgap, htw', hwv', hvu', hu', hsquare, hcapW, hcap', hcentral,
    hcentralUpper, hpq, huw, hut, hvw, hvt, hwt⟩

private theorem lowExact_ae_eq_source
    (epsilon : Real) (_ : 0 < epsilon) (_ : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralSmallQuadrupleRegion epsilon =ᵐ[volume]
      sectionSixFirstLowCentralSmallQuadrupleSourceRegion epsilon := by
  rw [ae_eq_set]
  constructor
  · exact measure_mono_null
      (lowExact_sdiff_source_subset_boundary epsilon)
      (volume_lowSourceBoundary epsilon)
  · rw [measure_eq_zero_iff_ae_notMem]
    exact ae_of_all _ fun x hx => hx.2 (lowSourceRegion_subset_exact epsilon hx.1)

theorem sectionSixFirstLowCentralSmallQuadrupleIntegral_eq_source
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon =
      ∫ x in sectionSixFirstLowCentralSmallQuadrupleSourceRegion epsilon,
        sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  unfold sectionSixFirstLowCentralSmallQuadrupleIntegral
  apply setIntegral_congr_set
  exact lowExact_ae_eq_source epsilon hepsilon hepsilonSmall

end

end PrimesRestrictedDigits
