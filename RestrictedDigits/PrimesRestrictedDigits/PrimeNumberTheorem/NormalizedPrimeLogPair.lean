import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
/-! # NormalizedPrimeLogPair -/

open Filter MeasureTheory Set Topology
open TopologicalSpace
open scoped BigOperators BoundedContinuousFunction NNReal Topology

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def normalizedPrimeLogPairIndices
    (a b : Real) (X : Nat) (region : Set (Real × Real)) :
    Finset (Nat × Nat) := by
  classical
  let primes := sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b)
  exact (primes.product primes).filter fun pair =>
    (normalizedPrimeLog X pair.1,
      normalizedPrimeLog X pair.2) ∈ region

noncomputable def normalizedPrimeLogPairSum
    (a b : Real) (X : Nat) (region : Set (Real × Real))
    (f : Real × Real -> Real) : Real :=
  ∑ pair ∈ normalizedPrimeLogPairIndices a b X region,
    normalizedPrimeLogWeight X pair.1 *
      normalizedPrimeLogWeight X pair.2 *
        f (normalizedPrimeLog X pair.1,
          normalizedPrimeLog X pair.2)

private theorem normalize_prod_of_nonzero
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    [Nonempty alpha] [Nonempty beta]
    (mu : FiniteMeasure alpha) (nu : FiniteMeasure beta)
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) :
    (mu.prod nu).normalize = mu.normalize.prod nu.normalize := by
  have hprod : mu.prod nu ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff, FiniteMeasure.mass_prod]
    exact mul_ne_zero ((FiniteMeasure.mass_nonzero_iff mu).mpr hmu)
      ((FiniteMeasure.mass_nonzero_iff nu).mpr hnu)
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_prod
  intro s t hs ht
  simp only [ProbabilityMeasure.toMeasure_prod, Measure.prod_prod,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  norm_cast
  rw [(mu.prod nu).normalize_eq_of_nonzero hprod,
    mu.normalize_eq_of_nonzero hmu, nu.normalize_eq_of_nonzero hnu,
    FiniteMeasure.prod_prod, FiniteMeasure.mass_prod]
  field_simp

theorem tendsto_finiteMeasure_prod
    {alpha beta index : Type*}
    [MeasurableSpace alpha] [TopologicalSpace alpha]
    [SecondCountableTopology alpha] [PseudoMetrizableSpace alpha]
    [OpensMeasurableSpace alpha] [Nonempty alpha]
    [MeasurableSpace beta] [TopologicalSpace beta]
    [SecondCountableTopology beta] [PseudoMetrizableSpace beta]
    [OpensMeasurableSpace beta] [Nonempty beta]
    {L : Filter index}
    {mus : index -> FiniteMeasure alpha} {mu : FiniteMeasure alpha}
    {nus : index -> FiniteMeasure beta} {nu : FiniteMeasure beta}
    (hmu : Tendsto mus L (nhds mu)) (hmu0 : mu ≠ 0)
    (hnu : Tendsto nus L (nhds nu)) (hnu0 : nu ≠ 0) :
    Tendsto (fun i => (mus i).prod (nus i)) L (nhds (mu.prod nu)) := by
  have hmuNormalize := FiniteMeasure.tendsto_normalize_of_tendsto hmu hmu0
  have hnuNormalize := FiniteMeasure.tendsto_normalize_of_tendsto hnu hnu0
  have hnormalize : Tendsto
      (fun i => (mus i).normalize.prod (nus i).normalize) L
      (nhds (mu.normalize.prod nu.normalize)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (hmuNormalize.prodMk_nhds hnuNormalize)
  have hmus0 : ∀ᶠ i in L, mus i ≠ 0 := by
    filter_upwards [hmu.mass.eventually (isOpen_compl_singleton.mem_nhds
      ((FiniteMeasure.mass_nonzero_iff mu).mpr hmu0))] with i hi
    exact (FiniteMeasure.mass_nonzero_iff (mus i)).mp hi
  have hnus0 : ∀ᶠ i in L, nus i ≠ 0 := by
    filter_upwards [hnu.mass.eventually (isOpen_compl_singleton.mem_nhds
      ((FiniteMeasure.mass_nonzero_iff nu).mpr hnu0))] with i hi
    exact (FiniteMeasure.mass_nonzero_iff (nus i)).mp hi
  have hnormalize' : Tendsto (fun i => ((mus i).prod (nus i)).normalize) L
      (nhds ((mu.prod nu).normalize)) := by
    have heq : (fun i => ((mus i).prod (nus i)).normalize) =ᶠ[L]
        fun i => (mus i).normalize.prod (nus i).normalize := by
      filter_upwards [hmus0, hnus0] with i hmi hni
      exact normalize_prod_of_nonzero (mus i) (nus i) hmi hni
    have := hnormalize.congr' heq.symm
    simpa [normalize_prod_of_nonzero mu nu hmu0 hnu0] using this
  apply (FiniteMeasure.tendsto_normalize_iff_tendsto
    (show mu.prod nu ≠ 0 by
      rw [← FiniteMeasure.mass_nonzero_iff, FiniteMeasure.mass_prod]
      exact mul_ne_zero ((FiniteMeasure.mass_nonzero_iff mu).mpr hmu0)
        ((FiniteMeasure.mass_nonzero_iff nu).mpr hnu0))).mp
  exact ⟨hnormalize', by simpa using hmu.mass.mul hnu.mass⟩

private noncomputable def weightedFiniteMeasure
    {omega : Type*} [MeasurableSpace omega] [TopologicalSpace omega]
    [OpensMeasurableSpace omega] (mu : FiniteMeasure omega)
    (weight : BoundedContinuousFunction omega NNReal) : FiniteMeasure omega :=
  ⟨(mu : Measure omega).withDensity fun x => (weight x : ENNReal), by
    exact isFiniteMeasure_withDensity
      (weight.lintegral_lt_top_of_nnreal (mu : Measure omega)).ne⟩

private theorem tendsto_weightedFiniteMeasure
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [OpensMeasurableSpace omega]
    {L : Filter index} {mus : index -> FiniteMeasure omega}
    {mu : FiniteMeasure omega} (weight : BoundedContinuousFunction omega NNReal)
    (hmu : Tendsto mus L (nhds mu)) :
    Tendsto (fun i => weightedFiniteMeasure (mus i) weight) L
      (nhds (weightedFiniteMeasure mu weight)) := by
  apply FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
  intro test
  have htest :=
    FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp hmu (weight * test)
  simpa only [weightedFiniteMeasure, FiniteMeasure.toMeasure_mk,
    lintegral_withDensity_eq_lintegral_mul₀
      weight.measurable_coe_ennreal_comp.aemeasurable
      test.measurable_coe_ennreal_comp.aemeasurable,
    BoundedContinuousFunction.coe_mul, Pi.mul_apply, ENNReal.coe_mul] using htest

private theorem tendsto_weightedFiniteMeasure_apply_of_null_frontier
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [OpensMeasurableSpace omega] [HasOuterApproxClosed omega] [Nonempty omega]
    {L : Filter index} {mus : index -> FiniteMeasure omega}
    {mu : FiniteMeasure omega} (weight : BoundedContinuousFunction omega NNReal)
    (hmu : Tendsto mus L (nhds mu)) {event : Set omega}
    (hfrontier : (mu : Measure omega) (frontier event) = 0) :
    Tendsto (fun i => weightedFiniteMeasure (mus i) weight event) L
      (nhds (weightedFiniteMeasure mu weight event)) := by
  let weighted := weightedFiniteMeasure mu weight
  let weighteds := fun i => weightedFiniteMeasure (mus i) weight
  have hweighted : Tendsto weighteds L (nhds weighted) :=
    tendsto_weightedFiniteMeasure weight hmu
  by_cases hweighted0 : weighted = 0
  · have hmass : Tendsto (fun i => (weighteds i).mass) L (nhds 0) := by
      simpa [hweighted0] using hweighted.mass
    have happly : Tendsto (fun i => weighteds i event) L (nhds 0) :=
      tendsto_const_nhds.squeeze hmass (fun _ => bot_le) fun i =>
        (weighteds i).apply_mono (subset_univ event)
    simpa [weighteds, weighted, hweighted0] using happly
  · have hnormalize :=
      FiniteMeasure.tendsto_normalize_of_tendsto hweighted hweighted0
    have hweightedFrontier : (weighted : Measure omega) (frontier event) = 0 :=
      (withDensity_absolutelyContinuous (mu : Measure omega)
        fun x => (weight x : ENNReal)) hfrontier
    have hnormalizeFrontier :
        (weighted.normalize : Measure omega) (frontier event) = 0 := by
      rw [weighted.toMeasure_normalize_eq_of_nonzero hweighted0]
      simp [Measure.smul_apply, hweightedFrontier]
    have hset :=
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hnormalize
        ((ProbabilityMeasure.null_iff_toMeasure_null weighted.normalize
          (frontier event)).mpr hnormalizeFrontier)
    have hmass := hweighted.mass
    simpa only [FiniteMeasure.self_eq_mass_mul_normalize, weighteds, weighted] using
      hmass.mul hset

private theorem coe_weightedFiniteMeasure_apply
    {omega : Type*} [MeasurableSpace omega] [TopologicalSpace omega]
    [OpensMeasurableSpace omega] (mu : FiniteMeasure omega)
    (weight : BoundedContinuousFunction omega NNReal) {event : Set omega}
    (hevent : MeasurableSet event) :
    (weightedFiniteMeasure mu weight event : Real) =
      ∫ x in event, (weight x : Real) ∂(mu : Measure omega) := by
  change (((mu : Measure omega).withDensity
    (fun x => (weight x : ENNReal))) event).toReal = _
  rw [withDensity_apply _ hevent]
  exact weight.toReal_lintegral_coe_eq_integral
    ((mu : Measure omega).restrict event)

theorem tendsto_setIntegral_boundedContinuousFunction_of_null_frontier
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [OpensMeasurableSpace omega] [HasOuterApproxClosed omega] [Nonempty omega]
    {L : Filter index} {mus : index -> FiniteMeasure omega}
    {mu : FiniteMeasure omega} (hmu : Tendsto mus L (nhds mu))
    {event : Set omega} (hevent : MeasurableSet event)
    (hfrontier : (mu : Measure omega) (frontier event) = 0)
    (f : BoundedContinuousFunction omega Real) :
    Tendsto (fun i => ∫ x in event, f x ∂(mus i : Measure omega)) L
      (nhds (∫ x in event, f x ∂(mu : Measure omega))) := by
  have hpos := tendsto_weightedFiniteMeasure_apply_of_null_frontier
    f.nnrealPart hmu hfrontier
  have hneg := tendsto_weightedFiniteMeasure_apply_of_null_frontier
    (-f).nnrealPart hmu hfrontier
  have hposReal := (NNReal.continuous_coe.tendsto
    (weightedFiniteMeasure mu f.nnrealPart event)).comp hpos
  have hnegReal := (NNReal.continuous_coe.tendsto
    (weightedFiniteMeasure mu (-f).nnrealPart event)).comp hneg
  have hdiff := hposReal.sub hnegReal
  simp only [Function.comp_apply,
    coe_weightedFiniteMeasure_apply _ _ hevent] at hdiff
  convert hdiff using 1
  · funext i
    exact f.integral_eq_integral_nnrealPart_sub
      ((mus i : Measure omega).restrict event)
  · rw [f.integral_eq_integral_nnrealPart_sub
      ((mu : Measure omega).restrict event)]

noncomputable def finiteDirac
    {omega : Type*} [MeasurableSpace omega] (x : omega) : FiniteMeasure omega :=
  ⟨Measure.dirac x, inferInstance⟩

theorem integral_finset_smul_finiteDirac
    {omega index : Type*} [MeasurableSpace omega]
    [MeasurableSingletonClass omega]
    (indices : Finset index) (weight : index -> NNReal)
    (point : index -> omega) (g : omega -> Real) :
    ∫ x, g x ∂(∑ i ∈ indices, weight i • finiteDirac (point i) :
      FiniteMeasure omega) =
      ∑ i ∈ indices, (weight i : Real) * g (point i) := by
  rw [FiniteMeasure.toMeasure_sum, integral_finsetSum_measure]
  · simp [finiteDirac, NNReal.smul_def]
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure (by simp)

private theorem setIntegral_finset_smul_finiteDirac_prod
    {omega leftIndex rightIndex : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [SecondCountableTopology omega] [OpensMeasurableSpace omega]
    [MeasurableSingletonClass omega]
    (left : Finset leftIndex) (right : Finset rightIndex)
    (leftWeight : leftIndex -> NNReal) (rightWeight : rightIndex -> NNReal)
    (leftPoint : leftIndex -> omega) (rightPoint : rightIndex -> omega)
    {event : Set (omega × omega)} (hevent : MeasurableSet event)
    (f : BoundedContinuousFunction (omega × omega) Real) :
    ∫ z in event, f z ∂((∑ i ∈ left,
        leftWeight i • finiteDirac (leftPoint i)).prod
      (∑ j ∈ right, rightWeight j • finiteDirac (rightPoint j)) :
        FiniteMeasure (omega × omega)) =
      ∑ i ∈ left, (leftWeight i : Real) *
        ∑ j ∈ right, (rightWeight j : Real) *
          event.indicator f (leftPoint i, rightPoint j) := by
  classical
  let leftMeasure : FiniteMeasure omega :=
    ∑ i ∈ left, leftWeight i • finiteDirac (leftPoint i)
  let rightMeasure : FiniteMeasure omega :=
    ∑ j ∈ right, rightWeight j • finiteDirac (rightPoint j)
  have hintegrable : Integrable (event.indicator f)
      ((leftMeasure.prod rightMeasure : FiniteMeasure (omega × omega)) :
        Measure (omega × omega)) :=
    (f.integrable _).indicator hevent
  rw [← integral_indicator hevent, FiniteMeasure.toMeasure_prod,
    integral_prod _ hintegrable]
  change (∫ x, (∫ y, event.indicator f (x, y) ∂rightMeasure)
    ∂leftMeasure) = _
  rw [integral_finset_smul_finiteDirac]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_smul_finiteDirac]

private theorem filteredPairSum_eq_setIntegral_finset_smul_finiteDirac_prod
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [SecondCountableTopology omega] [OpensMeasurableSpace omega]
    [MeasurableSingletonClass omega]
    (indices : Finset index) (weight : index -> Real)
    (point : index -> omega) {event : Set (omega × omega)}
    [DecidablePred fun pair : index × index =>
      (point pair.1, point pair.2) ∈ event]
    (hevent : MeasurableSet event)
    (hweight : ∀ i ∈ indices, 0 ≤ weight i)
    (f : BoundedContinuousFunction (omega × omega) Real) :
    ∑ pair ∈ (indices.product indices).filter
        (fun pair => (point pair.1, point pair.2) ∈ event),
      weight pair.1 * weight pair.2 * f (point pair.1, point pair.2) =
      ∫ z in event, f z ∂((∑ i ∈ indices,
          Real.toNNReal (weight i) • finiteDirac (point i)).prod
        (∑ j ∈ indices,
          Real.toNNReal (weight j) • finiteDirac (point j)) :
          FiniteMeasure (omega × omega)) := by
  classical
  rw [setIntegral_finset_smul_finiteDirac_prod indices indices
    (fun i => Real.toNNReal (weight i))
    (fun i => Real.toNNReal (weight i)) point point hevent f,
    Finset.sum_filter, Finset.product_eq_sprod]
  calc
    _ = ∑ pair ∈ indices ×ˢ indices,
        weight pair.1 * weight pair.2 *
          event.indicator f (point pair.1, point pair.2) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      by_cases hp : (point pair.1, point pair.2) ∈ event <;>
        simp [hp]
    _ = ∑ i ∈ indices, ∑ j ∈ indices,
        weight i * weight j * event.indicator f (point i, point j) :=
      Finset.sum_product indices indices _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.coe_toNNReal _ (hweight i hi), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.coe_toNNReal _ (hweight j hj)]
      rw [mul_assoc]

private theorem logPrimeWeight_nonneg
    {X p : Nat} (hX : 1 < X) (hp : p.Prime) :
    0 ≤ Real.log (p : Real) / ((p : Real) * Real.log (X : Real)) := by
  have hXReal : (1 : Real) < X := by exact_mod_cast hX
  exact div_nonneg hp.log_pos.le
    (mul_nonneg (Nat.cast_nonneg p) (Real.log_pos hXReal).le)

private theorem normalizedPrimeLogPairSum_eq_setIntegral
    {a b : Real} {length : Nat} (hlength : 1 ≤ length)
    {region : Set (Real × Real)} (hregion : MeasurableSet region)
    (f : BoundedContinuousFunction (Real × Real) Real) :
    normalizedPrimeLogPairSum a b (10 ^ length) region f =
      ∫ x in region, f x
        ∂(normalizedPrimeLogIntervalMeasure a b (10 ^ length) |>.prod
          (normalizedPrimeLogIntervalMeasure a b (10 ^ length)) :
            Measure (Real × Real)) := by
  classical
  let primes := sievePrimeInterval
    (((10 ^ length : Nat) : Real) ^ a)
    (((10 ^ length : Nat) : Real) ^ b)
  have hX : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hweight : ∀ p ∈ primes,
      0 ≤ normalizedPrimeLogWeight (10 ^ length) p := by
    intro p hp
    exact logPrimeWeight_nonneg hX (mem_sievePrimeInterval.mp hp).1
  simpa only [normalizedPrimeLogPairSum,
    normalizedPrimeLogPairIndices,
    normalizedPrimeLogIntervalMeasure, finiteDirac,
    normalizedPrimeLogWeight, primes] using
      filteredPairSum_eq_setIntegral_finset_smul_finiteDirac_prod primes
        (normalizedPrimeLogWeight (10 ^ length))
        (normalizedPrimeLog (10 ^ length)) hregion hweight f

theorem normalizedPrimeLogIntervalVolume_ne_zero
    {a b : Real} (hab : a < b) :
    normalizedPrimeLogIntervalVolume a b ≠ 0 := by
  intro hzero
  have hmeasure := congrArg FiniteMeasure.toMeasure hzero
  change volume.restrict (Ioc a b) = 0 at hmeasure
  have hvalue := congrArg (fun mu : Measure Real => mu (Ioc a b)) hmeasure
  rw [Measure.restrict_apply measurableSet_Ioc, inter_self,
    Real.volume_Ioc] at hvalue
  simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr hab)] at hvalue

private theorem normalizedPrimeLogIntervalVolume_selfProd_toMeasure
    {a b : Real} :
    (normalizedPrimeLogIntervalVolume a b |>.prod
      (normalizedPrimeLogIntervalVolume a b) :
      Measure (Real × Real)) =
      volume.restrict (Ioc a b ×ˢ Ioc a b) := by
  change (volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)) = _
  rw [Measure.prod_restrict,
    ← Measure.volume_eq_prod]

private theorem normalizedPrimeLogIntervalVolume_selfProd_frontier_null
    {a b : Real} {region : Set (Real × Real)}
    (hfrontier : volume (frontier region) = 0) :
    (normalizedPrimeLogIntervalVolume a b |>.prod
      (normalizedPrimeLogIntervalVolume a b) :
      Measure (Real × Real)) (frontier region) = 0 := by
  rw [normalizedPrimeLogIntervalVolume_selfProd_toMeasure,
    Measure.restrict_apply isClosed_frontier.measurableSet]
  exact measure_mono_null inter_subset_left hfrontier

private theorem setIntegral_normalizedPrimeLogIntervalVolume_selfProd_eq
    {a b : Real} {region : Set (Real × Real)}
    (hbox : region ⊆ Ioc a b ×ˢ Ioc a b)
    (f : (Real × Real) -> Real) :
    ∫ x in region, f x
        ∂(normalizedPrimeLogIntervalVolume a b |>.prod
          (normalizedPrimeLogIntervalVolume a b) :
          Measure (Real × Real)) =
      ∫ x in region, f x := by
  rw [normalizedPrimeLogIntervalVolume_selfProd_toMeasure,
    Measure.restrict_restrict_of_subset hbox]

private theorem tendsto_selfProduct_setIntegral_of_null_frontier
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [SecondCountableTopology omega] [PseudoMetrizableSpace omega]
    [OpensMeasurableSpace omega] [Nonempty omega]
    [HasOuterApproxClosed (omega × omega)]
    {L : Filter index} {mus : index -> FiniteMeasure omega}
    {mu : FiniteMeasure omega} (hmu : Tendsto mus L (nhds mu))
    (hmu0 : mu ≠ 0) {event : Set (omega × omega)}
    (hevent : MeasurableSet event)
    (hfrontier : (mu.prod mu : Measure (omega × omega))
      (frontier event) = 0)
    (f : BoundedContinuousFunction (omega × omega) Real) :
    Tendsto (fun i => ∫ x in event, f x
        ∂((mus i).prod (mus i) : Measure (omega × omega))) L
      (nhds (∫ x in event, f x
        ∂(mu.prod mu : Measure (omega × omega)))) := by
  exact tendsto_setIntegral_boundedContinuousFunction_of_null_frontier
    (tendsto_finiteMeasure_prod hmu hmu0 hmu hmu0) hevent hfrontier f

theorem tendsto_normalizedPrimeLogPairSum_powTen
    {a b : Real} (ha : 0 < a) (hab : a < b)
    {region : Set (Real × Real)}
    (hregion : MeasurableSet region)
    (hbox : region ⊆ Set.Ioc a b ×ˢ Set.Ioc a b)
    (hfrontier : volume (frontier region) = 0)
    (f : BoundedContinuousFunction (Real × Real) Real) :
    Tendsto
      (fun length : Nat =>
        normalizedPrimeLogPairSum a b (10 ^ length) region f)
      atTop (nhds (∫ x in region, f x)) := by
  have hintegrals := tendsto_selfProduct_setIntegral_of_null_frontier
    (tendsto_normalizedPrimeLogIntervalMeasure_powTen ha hab)
    (normalizedPrimeLogIntervalVolume_ne_zero hab) hregion
    (normalizedPrimeLogIntervalVolume_selfProd_frontier_null hfrontier) f
  rw [setIntegral_normalizedPrimeLogIntervalVolume_selfProd_eq hbox f]
    at hintegrals
  apply hintegrals.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with length hlength
  exact (normalizedPrimeLogPairSum_eq_setIntegral
    hlength hregion f).symm

end

end PrimesRestrictedDigits
