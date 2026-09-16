import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalRegions

/-!
# The literal source integral for the low central-large terminal term

The finite terminal region retains four weak walls. This file proves that opening precisely
those walls changes the region only on a null frontier, and hence leaves Maynard's `I_2`
integral unchanged.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 141, Eq. (6.9).
-/

open MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

private abbrev pairFirst : (Real × Real) →ₗ[Real] Real :=
  LinearMap.fst Real Real Real

private abbrev pairSecond : (Real × Real) →ₗ[Real] Real :=
  LinearMap.snd Real Real Real

private theorem sectionSixFirstLowCentralLargeTerminalSourceRegion_convex
    (epsilon : Real) :
    Convex Real
      (sectionSixFirstLowCentralLargeTerminalSourceRegion epsilon) := by
  have h : Convex Real
      ({x | sectionSixThetaGap epsilon < pairFirst x} ∩
        ({x | (pairFirst - pairSecond) x < 0} ∩
          ({x | pairSecond x < sectionSixThetaOne epsilon} ∩
            ({x | sectionSixThetaTwo epsilon <
                (pairSecond + pairFirst) x} ∩
              ({x | (pairSecond + pairFirst) x <
                  1 - sectionSixThetaTwo epsilon} ∩
                ({x | 1 - sectionSixThetaOne epsilon <
                    (pairSecond + (2 : Real) • pairFirst) x} ∩
                  {x | (pairSecond + (2 : Real) • pairFirst) x < 1})))))) :=
    (convex_halfSpace_gt pairFirst.isLinear _).inter
      ((convex_halfSpace_lt (pairFirst - pairSecond).isLinear _).inter
        ((convex_halfSpace_lt pairSecond.isLinear _).inter
          ((convex_halfSpace_gt (pairSecond + pairFirst).isLinear _).inter
            ((convex_halfSpace_lt (pairSecond + pairFirst).isLinear _).inter
              ((convex_halfSpace_gt
                (pairSecond + (2 : Real) • pairFirst).isLinear _).inter
                (convex_halfSpace_lt
                  (pairSecond + (2 : Real) • pairFirst).isLinear _))))))
  convert h using 1
  apply Set.ext
  intro x
  simp only [sectionSixFirstLowCentralLargeTerminalSourceRegion,
    mem_setOf_eq, Set.mem_inter_iff, pairFirst, pairSecond,
    LinearMap.coe_fst, LinearMap.coe_snd, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, by linarith, h3, h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, by linarith, h3, h4, h5, h6, h7⟩

private theorem sectionSixFirstLowCentralLargeTerminalSourceRegion_subset
    (epsilon : Real) :
    sectionSixFirstLowCentralLargeTerminalSourceRegion epsilon ⊆
      sectionSixFirstLowCentralLargeTerminalRegion epsilon := by
  rintro x ⟨hgap, horder, hu, hsumLower, hsumUpper,
    hsquareLower, hsquareUpper⟩
  exact ⟨hgap, horder.le, hu.le, hsumLower, hsumUpper,
    hsquareLower.le, hsquareUpper.le⟩

private noncomputable def approachPair
    (x y : Real × Real) (n : Nat) : Real × Real :=
  let t : Real := 1 / (n + 1)
  (1 - t) • x + t • y

private theorem approachPair_tendsto (x y : Real × Real) :
    Filter.Tendsto (approachPair x y) Filter.atTop (nhds x) := by
  change Filter.Tendsto (fun n : Nat =>
    (1 - (1 : Real) / (n + 1)) • x + ((1 : Real) / (n + 1)) • y)
      Filter.atTop (nhds x)
  have ht : Filter.Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : Filter.Tendsto (fun _ : Nat => (1 : Real))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa using ((hone.sub ht).smul_const x).add (ht.smul_const y)

private theorem subset_closure_of_pair_combinations
    {exact source : Set (Real × Real)} (y : Real × Real)
    (hcombo : ∀ x ∈ exact, ∀ a b : Real,
      0 <= a -> 0 < b -> a + b = 1 -> a • x + b • y ∈ source) :
    exact ⊆ closure source := by
  intro x hx
  rw [mem_closure_iff_seq_limit]
  refine ⟨approachPair x y, ?_, approachPair_tendsto x y⟩
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

private theorem
    sectionSixFirstLowCentralLargeTerminalRegion_subset_closure
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralLargeTerminalRegion epsilon ⊆
      closure
        (sectionSixFirstLowCentralLargeTerminalSourceRegion epsilon) := by
  let y : Real × Real := (4 / 25, 1 / 3)
  have hy : y ∈
      sectionSixFirstLowCentralLargeTerminalSourceRegion epsilon := by
    simp only [sectionSixFirstLowCentralLargeTerminalSourceRegion,
      mem_setOf_eq]
    rw [sectionSixThetaGap_eq]
    simp only [sectionSixThetaOne, sectionSixThetaTwo]
    constructor
    · dsimp [y]
      linarith
    constructor
    · dsimp [y]
      norm_num
    constructor
    · dsimp [y]
      linarith
    constructor
    · dsimp [y]
      linarith
    constructor
    · dsimp [y]
      linarith
    constructor
    · dsimp [y]
      linarith
    · dsimp [y]
      norm_num
  apply subset_closure_of_pair_combinations y
  intro x hx a b ha hb hab
  rcases hx with ⟨hxgap, hxorder, hxupper, hxsumLower, hxsumUpper,
    hxsquareLower, hxsquareUpper⟩
  rcases hy with ⟨hygap, hyorder, hyupper, hysumLower, hysumUpper,
    hysquareLower, hysquareUpper⟩
  change sectionSixThetaGap epsilon < a * x.1 + b * y.1 ∧
    a * x.1 + b * y.1 < a * x.2 + b * y.2 ∧
    a * x.2 + b * y.2 < sectionSixThetaOne epsilon ∧
    sectionSixThetaTwo epsilon <
      a * x.2 + b * y.2 + (a * x.1 + b * y.1) ∧
    a * x.2 + b * y.2 + (a * x.1 + b * y.1) <
      1 - sectionSixThetaTwo epsilon ∧
    1 - sectionSixThetaOne epsilon <
      a * x.2 + b * y.2 + 2 * (a * x.1 + b * y.1) ∧
    a * x.2 + b * y.2 + 2 * (a * x.1 + b * y.1) < 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [combo_lt_combo ha hb hxgap.le hygap]
  · exact combo_lt_combo ha hb hxorder hyorder
  · nlinarith [combo_lt_combo ha hb hxupper hyupper]
  · nlinarith [combo_lt_combo ha hb hxsumLower.le hysumLower]
  · nlinarith [combo_lt_combo ha hb hxsumUpper.le hysumUpper]
  · nlinarith [combo_lt_combo ha hb hxsquareLower hysquareLower]
  · nlinarith [combo_lt_combo ha hb hxsquareUpper hysquareUpper]

local instance : Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

private theorem ae_eq_of_subset_closure
    {source exact : Set (Real × Real)} (hsource : source ⊆ exact)
    (hexact : exact ⊆ closure source) (hconvex : Convex Real source) :
    exact =ᵐ[volume] source := by
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null _ (hconvex.addHaar_frontier volume)
    intro x hx
    rw [frontier]
    exact ⟨hexact hx.1, fun hxi => hx.2 (interior_subset hxi)⟩
  · rw [measure_eq_zero_iff_ae_notMem]
    exact ae_of_all _ fun x hx => hx.2 (hsource hx.1)

theorem sectionSixFirstLowCentralLargeTerminalIntegral_eq_source
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstLowCentralLargeTerminalIntegral epsilon =
      ∫ x in sectionSixFirstLowCentralLargeTerminalSourceRegion epsilon,
        sectionSixFirstLowCentralLargeTerminalKernel x := by
  unfold sectionSixFirstLowCentralLargeTerminalIntegral
  apply setIntegral_congr_set
  exact ae_eq_of_subset_closure
    (sectionSixFirstLowCentralLargeTerminalSourceRegion_subset epsilon)
    (sectionSixFirstLowCentralLargeTerminalRegion_subset_closure epsilon
      hepsilon hepsilonSmall)
    (sectionSixFirstLowCentralLargeTerminalSourceRegion_convex epsilon)

end

end PrimesRestrictedDigits
