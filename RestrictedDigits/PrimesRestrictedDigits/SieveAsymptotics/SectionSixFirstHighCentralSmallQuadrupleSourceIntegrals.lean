import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleRegions

/-!
# The literal source integral for the high central-small quadruple term

The exact finite region retains two weak role walls and the weak half cutoff. This file proves
that opening precisely those walls changes the region only on a null frontier, and hence
leaves Maynard's `I_9` integral unchanged.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 145--146, Eq. (6.16).
-/

open MeasureTheory Set Topology

namespace PrimesRestrictedDigits

noncomputable section

private abbrev quadrupleSourceTriple :
    (((Real × Real) × Real) × Real) →ₗ[Real] ((Real × Real) × Real) :=
  LinearMap.fst Real ((Real × Real) × Real) Real

private abbrev quadrupleSourcePair :
    (((Real × Real) × Real) × Real) →ₗ[Real] (Real × Real) :=
  (LinearMap.fst Real (Real × Real) Real).comp quadrupleSourceTriple

private abbrev quadrupleSourceU :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.fst Real Real Real).comp quadrupleSourcePair

private abbrev quadrupleSourceV :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real Real Real).comp quadrupleSourcePair

private abbrev quadrupleSourceW :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  (LinearMap.snd Real (Real × Real) Real).comp quadrupleSourceTriple

private abbrev quadrupleSourceT :
    (((Real × Real) × Real) × Real) →ₗ[Real] Real :=
  LinearMap.snd Real ((Real × Real) × Real) Real

private def sectionSixFirstHighCentralSmallQuadrupleOpenRegion
    (epsilon : Real) : Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixThetaGap epsilon < x.2 ∧
    x.2 < x.1.2 ∧
    x.1.2 < x.1.1.2 ∧
    sectionSixThetaTwo epsilon < x.1.1.1 ∧
    x.1.1.1 < (1 / 2 : Real) ∧
    x.1.1.1 + 2 * x.1.1.2 < 1 - sectionSixThetaOne epsilon}

private theorem sectionSixFirstHighCentralSmallQuadrupleOpenRegion_convex
    (epsilon : Real) :
    Convex Real
      (sectionSixFirstHighCentralSmallQuadrupleOpenRegion epsilon) := by
  have h :=
    (convex_halfSpace_gt quadrupleSourceT.isLinear
      (sectionSixThetaGap epsilon)).inter
      ((convex_halfSpace_lt
        (quadrupleSourceT - quadrupleSourceW).isLinear 0).inter
        ((convex_halfSpace_lt
          (quadrupleSourceW - quadrupleSourceV).isLinear 0).inter
          ((convex_halfSpace_gt quadrupleSourceU.isLinear
            (sectionSixThetaTwo epsilon)).inter
            ((convex_halfSpace_lt quadrupleSourceU.isLinear (1 / 2)).inter
              (convex_halfSpace_lt
                (quadrupleSourceU + (2 : Real) • quadrupleSourceV).isLinear
                (1 - sectionSixThetaOne epsilon))))))
  simpa [sectionSixFirstHighCentralSmallQuadrupleOpenRegion,
    quadrupleSourceU, quadrupleSourceV, quadrupleSourceW,
    quadrupleSourceT, quadrupleSourcePair, quadrupleSourceTriple,
    Set.inter_def, sub_neg] using h

private theorem
    sectionSixFirstHighCentralSmallQuadrupleSourceRegion_eq_openRegion
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstHighCentralSmallQuadrupleSourceRegion epsilon =
      sectionSixFirstHighCentralSmallQuadrupleOpenRegion epsilon := by
  ext x
  constructor
  · rintro ⟨hgap, htw, hwv, huTheta, huHalf, hsquare, _⟩
    exact ⟨hgap, htw, hwv, huTheta, huHalf, hsquare⟩
  · rintro ⟨hgap, htw, hwv, huTheta, huHalf, hsquare⟩
    have hgapPos : 0 < sectionSixThetaGap epsilon :=
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    have htPos : 0 < x.2 := hgapPos.trans hgap
    have hwPos : 0 < x.1.2 := htPos.trans htw
    have hvPos : 0 < x.1.1.2 := hwPos.trans hwv
    have hvTheta : x.1.1.2 < sectionSixThetaTwo epsilon := by
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
      linarith
    have huvLower : sectionSixThetaTwo epsilon < x.1.1.1 + x.1.1.2 := by
      linarith
    have huwLower : sectionSixThetaTwo epsilon < x.1.1.1 + x.1.2 := by
      linarith
    have hutLower : sectionSixThetaTwo epsilon < x.1.1.1 + x.2 := by
      linarith
    have huvUpper :
        x.1.1.1 + x.1.1.2 < 1 - sectionSixThetaTwo epsilon := by
      rw [sectionSixThetaGap_eq] at hgap
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at hsquare ⊢
      linarith
    have hvwUpper : x.1.1.2 + x.1.2 < sectionSixThetaOne epsilon := by
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
      linarith
    have hvtUpper : x.1.1.2 + x.2 < sectionSixThetaOne epsilon := by
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
      linarith
    have hwtUpper : x.1.2 + x.2 < sectionSixThetaOne epsilon := by
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
      linarith
    have hcapW : x.1.1.1 + x.1.1.2 + 2 * x.1.2 < 1 := by
      simp only [sectionSixThetaOne] at hsquare
      linarith
    have htwoVThetaOne :
        2 * x.1.1.2 < sectionSixThetaOne epsilon := by
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at huTheta hsquare ⊢
      linarith
    have hcapT : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 < 1 := by
      simp only [sectionSixThetaOne] at hsquare htwoVThetaOne
      linarith [htwoVThetaOne]
    refine ⟨hgap, htw, hwv, huTheta, huHalf, hsquare, hcapW, hcapT,
      huvLower, huvUpper, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hmem
      exact (not_lt_of_ge hmem.2) huvLower
    · intro hmem
      exact (not_lt_of_ge hmem.2) huwLower
    · intro hmem
      exact (not_lt_of_ge hmem.2) hutLower
    · intro hmem
      exact (not_lt_of_ge hmem.1) hvwUpper
    · intro hmem
      exact (not_lt_of_ge hmem.1) hvtUpper
    · intro hmem
      exact (not_lt_of_ge hmem.1) hwtUpper

private theorem
    sectionSixFirstHighCentralSmallQuadrupleSourceRegion_subset
    (epsilon : Real) :
    sectionSixFirstHighCentralSmallQuadrupleSourceRegion epsilon ⊆
      sectionSixFirstHighCentralSmallQuadrupleRegion epsilon := by
  rintro x ⟨hgap, htw, hwv, huTheta, huHalf, hsquare, _⟩
  exact ⟨hgap, htw.le, hwv.le, huTheta, huHalf.le, hsquare⟩

private noncomputable def approachFourfold
    (x y : ((Real × Real) × Real) × Real) (n : Nat) :
    ((Real × Real) × Real) × Real :=
  let t : Real := 1 / (n + 1)
  (1 - t) • x + t • y

private theorem approachFourfold_tendsto
    (x y : ((Real × Real) × Real) × Real) :
    Filter.Tendsto (approachFourfold x y) Filter.atTop (nhds x) := by
  change Filter.Tendsto (fun n : Nat =>
    (1 - (1 : Real) / (n + 1)) • x + ((1 : Real) / (n + 1)) • y)
      Filter.atTop (nhds x)
  have ht : Filter.Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : Filter.Tendsto (fun _ : Nat => (1 : Real))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa using ((hone.sub ht).smul_const x).add (ht.smul_const y)

private theorem subset_closure_of_fourfold_combinations
    {exact source : Set (((Real × Real) × Real) × Real)}
    (y : ((Real × Real) × Real) × Real)
    (hcombo : ∀ x ∈ exact, ∀ a b : Real,
      0 <= a -> 0 < b -> a + b = 1 -> a • x + b • y ∈ source) :
    exact ⊆ closure source := by
  intro x hx
  rw [mem_closure_iff_seq_limit]
  refine ⟨approachFourfold x y, ?_, approachFourfold_tendsto x y⟩
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
    sectionSixFirstHighCentralSmallQuadrupleRegion_subset_closure
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstHighCentralSmallQuadrupleRegion epsilon ⊆
      closure
        (sectionSixFirstHighCentralSmallQuadrupleSourceRegion epsilon) := by
  let y : ((Real × Real) × Real) × Real :=
    (((11 / 25, 2 / 25), 3 / 40), 7 / 100)
  have hy : y ∈
      sectionSixFirstHighCentralSmallQuadrupleOpenRegion epsilon := by
    simp only [sectionSixFirstHighCentralSmallQuadrupleOpenRegion,
      mem_setOf_eq]
    rw [sectionSixThetaGap_eq]
    simp only [sectionSixThetaOne, sectionSixThetaTwo]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp [y] <;> norm_num <;> linarith
  rw [sectionSixFirstHighCentralSmallQuadrupleSourceRegion_eq_openRegion
    epsilon hepsilon hepsilonSmall]
  apply subset_closure_of_fourfold_combinations y
  intro x hx a b ha hb hab
  rcases hx with ⟨hxgap, hxtw, hxwv, hxuTheta, hxuHalf, hxsquare⟩
  rcases hy with ⟨hygap, hytw, hywv, hyuTheta, hyuHalf, hysquare⟩
  change sectionSixThetaGap epsilon < a * x.2 + b * y.2 ∧
    a * x.2 + b * y.2 < a * x.1.2 + b * y.1.2 ∧
    a * x.1.2 + b * y.1.2 < a * x.1.1.2 + b * y.1.1.2 ∧
    sectionSixThetaTwo epsilon < a * x.1.1.1 + b * y.1.1.1 ∧
    a * x.1.1.1 + b * y.1.1.1 < 1 / 2 ∧
    a * x.1.1.1 + b * y.1.1.1 +
      2 * (a * x.1.1.2 + b * y.1.1.2) <
        1 - sectionSixThetaOne epsilon
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      sectionSixThetaGap epsilon =
          a * sectionSixThetaGap epsilon +
            b * sectionSixThetaGap epsilon := by
        rw [← add_mul, hab, one_mul]
      _ < a * x.2 + b * y.2 :=
        combo_lt_combo ha hb hxgap.le hygap
  · exact combo_lt_combo ha hb hxtw hytw
  · exact combo_lt_combo ha hb hxwv hywv
  · calc
      sectionSixThetaTwo epsilon =
          a * sectionSixThetaTwo epsilon +
            b * sectionSixThetaTwo epsilon := by
        rw [← add_mul, hab, one_mul]
      _ < a * x.1.1.1 + b * y.1.1.1 :=
        combo_lt_combo ha hb hxuTheta.le hyuTheta
  · calc
      a * x.1.1.1 + b * y.1.1.1 <
          a * (1 / 2) + b * (1 / 2) :=
        combo_lt_combo ha hb hxuHalf hyuHalf
      _ = 1 / 2 := by rw [← add_mul, hab, one_mul]
  · calc
      a * x.1.1.1 + b * y.1.1.1 +
          2 * (a * x.1.1.2 + b * y.1.1.2) =
          a * (x.1.1.1 + 2 * x.1.1.2) +
            b * (y.1.1.1 + 2 * y.1.1.2) := by ring
      _ < a * (1 - sectionSixThetaOne epsilon) +
          b * (1 - sectionSixThetaOne epsilon) :=
        combo_lt_combo ha hb hxsquare.le hysquare
      _ = 1 - sectionSixThetaOne epsilon := by
        rw [← add_mul, hab, one_mul]

private theorem
    sectionSixFirstHighCentralSmallQuadrupleSourceRegion_convex
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Convex Real
      (sectionSixFirstHighCentralSmallQuadrupleSourceRegion epsilon) := by
  rw [sectionSixFirstHighCentralSmallQuadrupleSourceRegion_eq_openRegion
    epsilon hepsilon hepsilonSmall]
  exact sectionSixFirstHighCentralSmallQuadrupleOpenRegion_convex epsilon

local instance sectionSixFirstHighCentralSmallQuadrupleSourcePairHaar :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstHighCentralSmallQuadrupleSourceTripleHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Real × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance sectionSixFirstHighCentralSmallQuadrupleSourceFourfoldHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure (((Real × Real) × Real) × Real)) :=
  Measure.prod.instIsAddHaarMeasure volume volume

private theorem ae_eq_of_subset_closure
    {source exact : Set (((Real × Real) × Real) × Real)}
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

theorem sectionSixFirstHighCentralSmallQuadrupleIntegral_eq_source
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon =
      ∫ x in
          sectionSixFirstHighCentralSmallQuadrupleSourceRegion epsilon,
        sectionSixFirstHighCentralSmallQuadrupleKernel x := by
  unfold sectionSixFirstHighCentralSmallQuadrupleIntegral
  apply setIntegral_congr_set
  exact ae_eq_of_subset_closure
    (sectionSixFirstHighCentralSmallQuadrupleSourceRegion_subset epsilon)
    (sectionSixFirstHighCentralSmallQuadrupleRegion_subset_closure epsilon
      hepsilon hepsilonSmall)
    (sectionSixFirstHighCentralSmallQuadrupleSourceRegion_convex epsilon
      hepsilon hepsilonSmall)

end

end PrimesRestrictedDigits
