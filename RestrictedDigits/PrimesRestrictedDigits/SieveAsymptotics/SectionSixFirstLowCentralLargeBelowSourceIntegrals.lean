import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowRegions

/-!
# The literal source integral for the low central-large below term

The finite continuation region retains five weak walls. This file proves that opening
precisely those walls changes the region only on a null frontier, and hence leaves Maynard's
`I_3` integral unchanged.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.10).
-/

open MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

private abbrev triplePair : ((Real × Real) × Real) →ₗ[Real] Real × Real :=
  LinearMap.fst Real (Real × Real) Real

private abbrev tripleU : ((Real × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp triplePair

private abbrev tripleV : ((Real × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp triplePair

private abbrev tripleW : ((Real × Real) × Real) →ₗ[Real] Real :=
  LinearMap.snd Real (Real × Real) Real

private theorem sectionSixFirstLowCentralLargeBelowSourceRegion_convex
    (epsilon : Real) :
    Convex Real
      (sectionSixFirstLowCentralLargeBelowSourceRegion epsilon) := by
  have h :=
    (convex_halfSpace_gt tripleV.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_lt (tripleV - tripleU).isLinear 0).inter
        ((convex_halfSpace_lt tripleU.isLinear
          (sectionSixThetaOne epsilon)).inter
          ((convex_halfSpace_gt (tripleU + tripleV).isLinear
            (sectionSixThetaTwo epsilon)).inter
            ((convex_halfSpace_lt (tripleU + tripleV).isLinear
              (1 - sectionSixThetaTwo epsilon)).inter
              ((convex_halfSpace_gt
                (tripleU + (2 : Real) • tripleV).isLinear
                (1 - sectionSixThetaOne epsilon)).inter
                ((convex_halfSpace_lt
                  (tripleU + (2 : Real) • tripleV).isLinear 1).inter
                  ((convex_halfSpace_lt (tripleV - tripleW).isLinear 0).inter
                    ((convex_halfSpace_lt
                      (tripleU + tripleV + (2 : Real) • tripleW).isLinear
                      1).inter
                      (convex_halfSpace_lt
                        (tripleV + tripleW).isLinear
                        (sectionSixThetaOne epsilon))))))))))
  simpa [sectionSixFirstLowCentralLargeBelowSourceRegion, tripleU, tripleV,
    tripleW, triplePair, Set.inter_def, sub_neg] using h

private theorem sectionSixFirstLowCentralLargeBelowSourceRegion_subset
    (epsilon : Real) :
    sectionSixFirstLowCentralLargeBelowSourceRegion epsilon ⊆
      sectionSixFirstLowCentralLargeBelowRegion epsilon := by
  rintro x ⟨hgap, horder, hu, hsumLower, hsumUpper,
    hsquareLower, hsquareUpper, hvw, hcap, hbelow⟩
  exact ⟨hgap, horder.le, hu.le, hsumLower, hsumUpper,
    hsquareLower.le, hsquareUpper.le, hvw, hcap.le, hbelow⟩

private noncomputable def approachTriple
    (x y : (Real × Real) × Real) (n : Nat) : (Real × Real) × Real :=
  let t : Real := 1 / (n + 1)
  (1 - t) • x + t • y

private theorem approachTriple_tendsto
    (x y : (Real × Real) × Real) :
    Filter.Tendsto (approachTriple x y) Filter.atTop (nhds x) := by
  change Filter.Tendsto (fun n : Nat =>
    (1 - (1 : Real) / (n + 1)) • x + ((1 : Real) / (n + 1)) • y)
      Filter.atTop (nhds x)
  have ht : Filter.Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : Filter.Tendsto (fun _ : Nat => (1 : Real))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa using ((hone.sub ht).smul_const x).add (ht.smul_const y)

private theorem subset_closure_of_triple_combinations
    {exact source : Set ((Real × Real) × Real)}
    (y : (Real × Real) × Real)
    (hcombo : ∀ x ∈ exact, ∀ a b : Real,
      0 <= a -> 0 < b -> a + b = 1 -> a • x + b • y ∈ source) :
    exact ⊆ closure source := by
  intro x hx
  rw [mem_closure_iff_seq_limit]
  refine ⟨approachTriple x y, ?_, approachTriple_tendsto x y⟩
  intro n
  let t : Real := 1 / (n + 1)
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have htone : t <= 1 := by
    apply (div_le_one (by positivity : (0 : Real) < n + 1)).2
    norm_num
  exact hcombo x hx (1 - t) t (sub_nonneg.mpr htone) htpos (by ring)

private theorem combo_lt_combo {a b x x' y y' : Real}
    (ha : 0 <= a) (hb : 0 < b) (hx : x <= x') (hy : y < y') :
    a * x + b * y < a * x' + b * y' := by
  have hx' : 0 <= a * (x' - x) := mul_nonneg ha (sub_nonneg.mpr hx)
  have hy' : 0 < b * (y' - y) := mul_pos hb (sub_pos.mpr hy)
  nlinarith

private theorem sectionSixFirstLowCentralLargeBelowRegion_subset_closure
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralLargeBelowRegion epsilon ⊆
      closure (sectionSixFirstLowCentralLargeBelowSourceRegion epsilon) := by
  let y : (Real × Real) × Real := ((7 / 20, 3 / 20), 9 / 50)
  have hy : y ∈
      sectionSixFirstLowCentralLargeBelowSourceRegion epsilon := by
    simp only [sectionSixFirstLowCentralLargeBelowSourceRegion, mem_setOf_eq]
    rw [sectionSixThetaGap_eq]
    simp only [sectionSixThetaOne, sectionSixThetaTwo]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp [y] <;> norm_num <;> linarith
  apply subset_closure_of_triple_combinations y
  intro x hx a b ha hb hab
  rcases hx with ⟨hxgap, hxorder, hxupper, hxsumLower, hxsumUpper,
    hxsquareLower, hxsquareUpper, hxvw, hxcap, hxbelow⟩
  rcases hy with ⟨hygap, hyorder, hyupper, hysumLower, hysumUpper,
    hysquareLower, hysquareUpper, hyvw, hycap, hybelow⟩
  change sectionSixThetaGap epsilon < a * x.1.2 + b * y.1.2 ∧
    a * x.1.2 + b * y.1.2 < a * x.1.1 + b * y.1.1 ∧
    a * x.1.1 + b * y.1.1 < sectionSixThetaOne epsilon ∧
    sectionSixThetaTwo epsilon <
      a * x.1.1 + b * y.1.1 + (a * x.1.2 + b * y.1.2) ∧
    a * x.1.1 + b * y.1.1 + (a * x.1.2 + b * y.1.2) <
      1 - sectionSixThetaTwo epsilon ∧
    1 - sectionSixThetaOne epsilon <
      a * x.1.1 + b * y.1.1 + 2 * (a * x.1.2 + b * y.1.2) ∧
    a * x.1.1 + b * y.1.1 + 2 * (a * x.1.2 + b * y.1.2) < 1 ∧
    a * x.1.2 + b * y.1.2 < a * x.2 + b * y.2 ∧
    a * x.1.1 + b * y.1.1 + (a * x.1.2 + b * y.1.2) +
      2 * (a * x.2 + b * y.2) < 1 ∧
    a * x.1.2 + b * y.1.2 + (a * x.2 + b * y.2) <
      sectionSixThetaOne epsilon
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [combo_lt_combo ha hb hxgap.le hygap]
  · exact combo_lt_combo ha hb hxorder hyorder
  · nlinarith [combo_lt_combo ha hb hxupper hyupper]
  · nlinarith [combo_lt_combo ha hb hxsumLower.le hysumLower]
  · nlinarith [combo_lt_combo ha hb hxsumUpper.le hysumUpper]
  · nlinarith [combo_lt_combo ha hb hxsquareLower hysquareLower]
  · nlinarith [combo_lt_combo ha hb hxsquareUpper hysquareUpper]
  · exact combo_lt_combo ha hb hxvw.le hyvw
  · nlinarith [combo_lt_combo ha hb hxcap hycap]
  · nlinarith [combo_lt_combo ha hb hxbelow.le hybelow]

local instance sectionSixFirstLowCentralLargeBelowSourcePairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstLowCentralLargeBelowSourceTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

private theorem ae_eq_of_subset_closure
    {source exact : Set ((Real × Real) × Real)}
    (hsource : source ⊆ exact) (hexact : exact ⊆ closure source)
    (hconvex : Convex Real source) :
    exact =ᵐ[volume] source := by
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null _ (hconvex.addHaar_frontier volume)
    intro x hx
    rw [frontier]
    exact ⟨hexact hx.1, fun hxi => hx.2 (interior_subset hxi)⟩
  · rw [measure_eq_zero_iff_ae_notMem]
    exact ae_of_all _ fun x hx => hx.2 (hsource hx.1)

theorem sectionSixFirstLowCentralLargeBelowIntegral_eq_source
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralLargeBelowIntegral epsilon =
      ∫ x in sectionSixFirstLowCentralLargeBelowSourceRegion epsilon,
        sectionSixFirstLowCentralLargeBelowKernel x := by
  unfold sectionSixFirstLowCentralLargeBelowIntegral
  apply setIntegral_congr_set
  exact ae_eq_of_subset_closure
    (sectionSixFirstLowCentralLargeBelowSourceRegion_subset epsilon)
    (sectionSixFirstLowCentralLargeBelowRegion_subset_closure epsilon
      hepsilon hepsilonSmall)
    (sectionSixFirstLowCentralLargeBelowSourceRegion_convex epsilon)

end

end PrimesRestrictedDigits
