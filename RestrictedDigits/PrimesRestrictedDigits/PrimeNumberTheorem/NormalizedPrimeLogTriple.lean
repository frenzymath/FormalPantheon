import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogPair

/-!
# Normalized logarithmic prime triples

This file upgrades the scalar prime-log measure limit to filtered triple sums. The
left-associated coordinates `((p, q), r)` match the Section 6 continuation carriers used for
Maynard's `I_3` and `I_4` terms.
-/

open Filter MeasureTheory Set Topology
open TopologicalSpace
open scoped BigOperators BoundedContinuousFunction NNReal Topology

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def normalizedPrimeLogTripleIndices
    (a b : Real) (X : Nat) (region : Set ((Real × Real) × Real)) :
    Finset ((Nat × Nat) × Nat) := by
  classical
  let primes := sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b)
  exact ((primes.product primes).product primes).filter fun triple =>
    ((normalizedPrimeLog X triple.1.1,
      normalizedPrimeLog X triple.1.2),
      normalizedPrimeLog X triple.2) ∈ region

noncomputable def normalizedPrimeLogTripleSum
    (a b : Real) (X : Nat) (region : Set ((Real × Real) × Real))
    (f : ((Real × Real) × Real) -> Real) : Real :=
  ∑ triple ∈ normalizedPrimeLogTripleIndices a b X region,
    normalizedPrimeLogWeight X triple.1.1 *
      normalizedPrimeLogWeight X triple.1.2 *
        normalizedPrimeLogWeight X triple.2 *
          f ((normalizedPrimeLog X triple.1.1,
            normalizedPrimeLog X triple.1.2),
            normalizedPrimeLog X triple.2)

theorem normalizedPrimeLogTripleSum_congr
    (a b : Real) (X : Nat)
    {region : Set ((Real × Real) × Real)}
    {f g : ((Real × Real) × Real) -> Real}
    (hfg : Set.EqOn f g region) :
    normalizedPrimeLogTripleSum a b X region f =
      normalizedPrimeLogTripleSum a b X region g := by
  classical
  unfold normalizedPrimeLogTripleSum
  apply Finset.sum_congr rfl
  intro triple htriple
  have htriple' := htriple
  unfold normalizedPrimeLogTripleIndices at htriple'
  have hregion := (Finset.mem_filter.mp htriple').2
  rw [hfg hregion]

private theorem setIntegral_finset_smul_finiteDirac_triple
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [SecondCountableTopology omega] [OpensMeasurableSpace omega]
    [MeasurableSingletonClass omega]
    (indices : Finset index) (weight : index -> NNReal)
    (point : index -> omega)
    {event : Set ((omega × omega) × omega)} (hevent : MeasurableSet event)
    (f : BoundedContinuousFunction ((omega × omega) × omega) Real) :
    ∫ z in event, f z ∂(((∑ i ∈ indices,
        weight i • finiteDirac (point i)).prod
      (∑ j ∈ indices, weight j • finiteDirac (point j))).prod
      (∑ k ∈ indices, weight k • finiteDirac (point k)) :
        FiniteMeasure ((omega × omega) × omega)) =
      ∑ i ∈ indices, (weight i : Real) *
        ∑ j ∈ indices, (weight j : Real) *
          ∑ k ∈ indices, (weight k : Real) *
            event.indicator f ((point i, point j), point k) := by
  classical
  let atomMeasure : FiniteMeasure omega :=
    ∑ i ∈ indices, weight i • finiteDirac (point i)
  have hintegrable : Integrable (event.indicator f)
      ((((atomMeasure.prod atomMeasure).prod atomMeasure :
          FiniteMeasure ((omega × omega) × omega)) :
        Measure ((omega × omega) × omega))) :=
    (f.integrable _).indicator hevent
  rw [← integral_indicator hevent, FiniteMeasure.toMeasure_prod,
    integral_prod _ hintegrable]
  change (∫ xy, (∫ z, event.indicator f (xy, z) ∂atomMeasure)
      ∂(atomMeasure.prod atomMeasure : FiniteMeasure (omega × omega))) = _
  rw [FiniteMeasure.toMeasure_prod,
    integral_prod _ hintegrable.integral_prod_left]
  change (∫ x, (∫ y, (∫ z, event.indicator f ((x, y), z)
      ∂atomMeasure) ∂atomMeasure) ∂atomMeasure) = _
  rw [integral_finset_smul_finiteDirac]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_smul_finiteDirac]
  apply congrArg ((weight i : Real) * ·)
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finset_smul_finiteDirac]

private theorem filteredTripleSum_eq_setIntegral
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [SecondCountableTopology omega] [OpensMeasurableSpace omega]
    [MeasurableSingletonClass omega]
    (indices : Finset index) (weight : index -> Real)
    (point : index -> omega) {event : Set ((omega × omega) × omega)}
    [DecidablePred fun triple : (index × index) × index =>
      ((point triple.1.1, point triple.1.2), point triple.2) ∈ event]
    (hevent : MeasurableSet event)
    (hweight : ∀ i ∈ indices, 0 ≤ weight i)
    (f : BoundedContinuousFunction ((omega × omega) × omega) Real) :
    ∑ triple ∈ ((indices.product indices).product indices).filter
        (fun triple => ((point triple.1.1, point triple.1.2),
          point triple.2) ∈ event),
      weight triple.1.1 * weight triple.1.2 * weight triple.2 *
        f ((point triple.1.1, point triple.1.2), point triple.2) =
      ∫ z in event, f z ∂(((∑ i ∈ indices,
          Real.toNNReal (weight i) • finiteDirac (point i)).prod
        (∑ j ∈ indices,
          Real.toNNReal (weight j) • finiteDirac (point j))).prod
        (∑ k ∈ indices,
          Real.toNNReal (weight k) • finiteDirac (point k)) :
          FiniteMeasure ((omega × omega) × omega)) := by
  classical
  rw [setIntegral_finset_smul_finiteDirac_triple indices
    (fun i => Real.toNNReal (weight i)) point hevent f,
    Finset.sum_filter, Finset.product_eq_sprod,
    Finset.product_eq_sprod]
  simp_rw [Set.indicator_apply]
  rw [Finset.sum_product, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.coe_toNNReal _ (hweight i hi), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.coe_toNNReal _ (hweight j hj), Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Real.coe_toNNReal _ (hweight k hk)]
  by_cases hmem : ((point i, point j), point k) ∈ event <;>
    simp [hmem, mul_assoc]

private theorem logPrimeWeight_nonneg
    {X p : Nat} (hX : 1 < X) (hp : p.Prime) :
    0 ≤ Real.log (p : Real) / ((p : Real) * Real.log (X : Real)) := by
  have hXReal : (1 : Real) < X := by exact_mod_cast hX
  exact div_nonneg hp.log_pos.le
    (mul_nonneg (Nat.cast_nonneg p) (Real.log_pos hXReal).le)

private theorem normalizedPrimeLogTripleSum_eq_setIntegral
    {a b : Real} {length : Nat} (hlength : 1 ≤ length)
    {region : Set ((Real × Real) × Real)}
    (hregion : MeasurableSet region)
    (f : BoundedContinuousFunction ((Real × Real) × Real) Real) :
    normalizedPrimeLogTripleSum a b (10 ^ length) region f =
      ∫ x in region, f x
        ∂(((normalizedPrimeLogIntervalMeasure a b (10 ^ length)).prod
          (normalizedPrimeLogIntervalMeasure a b (10 ^ length))).prod
          (normalizedPrimeLogIntervalMeasure a b (10 ^ length)) :
            Measure ((Real × Real) × Real)) := by
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
  simpa only [normalizedPrimeLogTripleSum,
    normalizedPrimeLogTripleIndices,
    normalizedPrimeLogIntervalMeasure, finiteDirac,
    normalizedPrimeLogWeight, primes] using
      filteredTripleSum_eq_setIntegral primes
        (normalizedPrimeLogWeight (10 ^ length))
        (normalizedPrimeLog (10 ^ length)) hregion hweight f

private theorem normalizedPrimeLogIntervalVolume_selfTriple_toMeasure
    {a b : Real} :
    (((normalizedPrimeLogIntervalVolume a b).prod
      (normalizedPrimeLogIntervalVolume a b)).prod
      (normalizedPrimeLogIntervalVolume a b) :
      Measure ((Real × Real) × Real)) =
      volume.restrict ((Ioc a b ×ˢ Ioc a b) ×ˢ Ioc a b) := by
  change ((volume.restrict (Ioc a b)).prod
      (volume.restrict (Ioc a b))).prod
      (volume.restrict (Ioc a b)) = _
  rw [Measure.prod_restrict, Measure.prod_restrict,
    ← Measure.volume_eq_prod, ← Measure.volume_eq_prod]

private theorem normalizedPrimeLogIntervalVolume_selfTriple_frontier_null
    {a b : Real} {region : Set ((Real × Real) × Real)}
    (hfrontier : volume (frontier region) = 0) :
    (((normalizedPrimeLogIntervalVolume a b).prod
      (normalizedPrimeLogIntervalVolume a b)).prod
      (normalizedPrimeLogIntervalVolume a b) :
      Measure ((Real × Real) × Real)) (frontier region) = 0 := by
  rw [normalizedPrimeLogIntervalVolume_selfTriple_toMeasure,
    Measure.restrict_apply isClosed_frontier.measurableSet]
  exact measure_mono_null inter_subset_left hfrontier

private theorem setIntegral_normalizedPrimeLogIntervalVolume_selfTriple_eq
    {a b : Real} {region : Set ((Real × Real) × Real)}
    (hbox : region ⊆ (Ioc a b ×ˢ Ioc a b) ×ˢ Ioc a b)
    (f : ((Real × Real) × Real) -> Real) :
    ∫ x in region, f x
        ∂(((normalizedPrimeLogIntervalVolume a b).prod
          (normalizedPrimeLogIntervalVolume a b)).prod
          (normalizedPrimeLogIntervalVolume a b) :
          Measure ((Real × Real) × Real)) =
      ∫ x in region, f x := by
  rw [normalizedPrimeLogIntervalVolume_selfTriple_toMeasure,
    Measure.restrict_restrict_of_subset hbox]

theorem tendsto_normalizedPrimeLogTripleSum_powTen
    {a b : Real} (ha : 0 < a) (hab : a < b)
    {region : Set ((Real × Real) × Real)}
    (hregion : MeasurableSet region)
    (hbox : region ⊆
      (Set.Ioc a b ×ˢ Set.Ioc a b) ×ˢ Set.Ioc a b)
    (hfrontier : volume (frontier region) = 0)
    (f : BoundedContinuousFunction ((Real × Real) × Real) Real) :
    Tendsto
      (fun length : Nat =>
        normalizedPrimeLogTripleSum a b (10 ^ length) region f)
      atTop (nhds (∫ x in region, f x)) := by
  let mus := fun length : Nat =>
    normalizedPrimeLogIntervalMeasure a b (10 ^ length)
  let mu := normalizedPrimeLogIntervalVolume a b
  have hsingle : Tendsto mus atTop (nhds mu) :=
    tendsto_normalizedPrimeLogIntervalMeasure_powTen ha hab
  have hmu0 : mu ≠ 0 := normalizedPrimeLogIntervalVolume_ne_zero hab
  have hpair : Tendsto (fun length => (mus length).prod (mus length))
      atTop (nhds (mu.prod mu)) :=
    tendsto_finiteMeasure_prod hsingle hmu0 hsingle hmu0
  have hpair0 : mu.prod mu ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff, FiniteMeasure.mass_prod]
    exact mul_ne_zero
      ((FiniteMeasure.mass_nonzero_iff mu).mpr hmu0)
      ((FiniteMeasure.mass_nonzero_iff mu).mpr hmu0)
  have htriple : Tendsto
      (fun length => ((mus length).prod (mus length)).prod (mus length))
      atTop (nhds ((mu.prod mu).prod mu)) :=
    tendsto_finiteMeasure_prod hpair hpair0 hsingle hmu0
  have hintegrals :=
    tendsto_setIntegral_boundedContinuousFunction_of_null_frontier
      htriple hregion
        (normalizedPrimeLogIntervalVolume_selfTriple_frontier_null hfrontier) f
  rw [setIntegral_normalizedPrimeLogIntervalVolume_selfTriple_eq hbox f]
    at hintegrals
  apply hintegrals.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with length hlength
  exact (normalizedPrimeLogTripleSum_eq_setIntegral
    hlength hregion f).symm

end

end PrimesRestrictedDigits
