import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogTriple

/-!
# Normalized logarithmic prime fourfolds

This extends the normalized prime-log measure limit to left-associated fourfold sums. The
coordinate order `(((p, q), r), s)` is the role order used by Maynard's `I_9` term.
-/

open Filter MeasureTheory Set Topology
open TopologicalSpace
open scoped BigOperators BoundedContinuousFunction NNReal Topology

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def normalizedPrimeLogFourfoldIndices
    (a b : Real) (X : Nat)
    (region : Set (((Real × Real) × Real) × Real)) :
    Finset (((Nat × Nat) × Nat) × Nat) := by
  classical
  let primes := sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b)
  exact (((primes.product primes).product primes).product primes).filter
    fun quadruple =>
      (((normalizedPrimeLog X quadruple.1.1.1,
          normalizedPrimeLog X quadruple.1.1.2),
        normalizedPrimeLog X quadruple.1.2),
        normalizedPrimeLog X quadruple.2) ∈ region

noncomputable def normalizedPrimeLogFourfoldSum
    (a b : Real) (X : Nat)
    (region : Set (((Real × Real) × Real) × Real))
    (f : (((Real × Real) × Real) × Real) → Real) : Real :=
  ∑ quadruple ∈ normalizedPrimeLogFourfoldIndices a b X region,
    normalizedPrimeLogWeight X quadruple.1.1.1 *
      normalizedPrimeLogWeight X quadruple.1.1.2 *
        normalizedPrimeLogWeight X quadruple.1.2 *
          normalizedPrimeLogWeight X quadruple.2 *
            f (((normalizedPrimeLog X quadruple.1.1.1,
                normalizedPrimeLog X quadruple.1.1.2),
              normalizedPrimeLog X quadruple.1.2),
              normalizedPrimeLog X quadruple.2)

theorem normalizedPrimeLogFourfoldSum_congr
    (a b : Real) (X : Nat)
    {region : Set (((Real × Real) × Real) × Real)}
    {f g : (((Real × Real) × Real) × Real) → Real}
    (hfg : Set.EqOn f g region) :
    normalizedPrimeLogFourfoldSum a b X region f =
      normalizedPrimeLogFourfoldSum a b X region g := by
  classical
  unfold normalizedPrimeLogFourfoldSum
  apply Finset.sum_congr rfl
  intro quadruple hquadruple
  have hquadruple' := hquadruple
  unfold normalizedPrimeLogFourfoldIndices at hquadruple'
  have hregion := (Finset.mem_filter.mp hquadruple').2
  rw [hfg hregion]

private theorem setIntegral_finset_smul_finiteDirac_fourfold
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [SecondCountableTopology omega] [OpensMeasurableSpace omega]
    [MeasurableSingletonClass omega]
    (indices : Finset index) (weight : index → NNReal)
    (point : index → omega)
    {event : Set (((omega × omega) × omega) × omega)}
    (hevent : MeasurableSet event)
    (f : BoundedContinuousFunction (((omega × omega) × omega) × omega) Real) :
    ∫ z in event, f z ∂((((∑ i ∈ indices,
        weight i • finiteDirac (point i)).prod
      (∑ j ∈ indices, weight j • finiteDirac (point j))).prod
      (∑ k ∈ indices, weight k • finiteDirac (point k))).prod
      (∑ l ∈ indices, weight l • finiteDirac (point l)) :
        FiniteMeasure (((omega × omega) × omega) × omega)) =
      ∑ i ∈ indices, (weight i : Real) *
        ∑ j ∈ indices, (weight j : Real) *
          ∑ k ∈ indices, (weight k : Real) *
            ∑ l ∈ indices, (weight l : Real) *
              event.indicator f (((point i, point j), point k), point l) := by
  classical
  let atomMeasure : FiniteMeasure omega :=
    ∑ i ∈ indices, weight i • finiteDirac (point i)
  have hintegrable : Integrable (event.indicator f)
      (((((atomMeasure.prod atomMeasure).prod atomMeasure).prod atomMeasure :
          FiniteMeasure (((omega × omega) × omega) × omega)) :
        Measure (((omega × omega) × omega) × omega))) :=
    (f.integrable _).indicator hevent
  rw [← integral_indicator hevent, FiniteMeasure.toMeasure_prod,
    integral_prod _ hintegrable]
  change (∫ xyz, (∫ t, event.indicator f (xyz, t) ∂atomMeasure)
      ∂((atomMeasure.prod atomMeasure).prod atomMeasure :
        FiniteMeasure ((omega × omega) × omega))) = _
  rw [FiniteMeasure.toMeasure_prod,
    integral_prod _ hintegrable.integral_prod_left]
  change (∫ xy, (∫ z, (∫ t, event.indicator f ((xy, z), t) ∂atomMeasure)
      ∂atomMeasure) ∂(atomMeasure.prod atomMeasure :
        FiniteMeasure (omega × omega))) = _
  rw [FiniteMeasure.toMeasure_prod,
    integral_prod _ hintegrable.integral_prod_left.integral_prod_left]
  change (∫ x, (∫ y, (∫ z, (∫ t,
      event.indicator f (((x, y), z), t) ∂atomMeasure)
      ∂atomMeasure) ∂atomMeasure) ∂atomMeasure) = _
  rw [integral_finset_smul_finiteDirac]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_smul_finiteDirac]
  apply congrArg ((weight i : Real) * ·)
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finset_smul_finiteDirac]
  apply congrArg ((weight j : Real) * ·)
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_finset_smul_finiteDirac]

private theorem filteredFourfoldSum_eq_setIntegral
    {omega index : Type*}
    [MeasurableSpace omega] [TopologicalSpace omega]
    [SecondCountableTopology omega] [OpensMeasurableSpace omega]
    [MeasurableSingletonClass omega]
    (indices : Finset index) (weight : index → Real)
    (point : index → omega)
    {event : Set (((omega × omega) × omega) × omega)}
    [DecidablePred fun quadruple : (((index × index) × index) × index) =>
      (((point quadruple.1.1.1, point quadruple.1.1.2),
        point quadruple.1.2), point quadruple.2) ∈ event]
    (hevent : MeasurableSet event)
    (hweight : ∀ i ∈ indices, 0 ≤ weight i)
    (f : BoundedContinuousFunction (((omega × omega) × omega) × omega) Real) :
    ∑ quadruple ∈ (((indices.product indices).product indices).product indices).filter
        (fun quadruple =>
          (((point quadruple.1.1.1, point quadruple.1.1.2),
            point quadruple.1.2), point quadruple.2) ∈ event),
      weight quadruple.1.1.1 * weight quadruple.1.1.2 *
        weight quadruple.1.2 * weight quadruple.2 *
          f (((point quadruple.1.1.1, point quadruple.1.1.2),
            point quadruple.1.2), point quadruple.2) =
      ∫ z in event, f z ∂((((∑ i ∈ indices,
          Real.toNNReal (weight i) • finiteDirac (point i)).prod
        (∑ j ∈ indices,
          Real.toNNReal (weight j) • finiteDirac (point j))).prod
        (∑ k ∈ indices,
          Real.toNNReal (weight k) • finiteDirac (point k))).prod
        (∑ l ∈ indices,
          Real.toNNReal (weight l) • finiteDirac (point l)) :
          FiniteMeasure (((omega × omega) × omega) × omega)) := by
  classical
  rw [setIntegral_finset_smul_finiteDirac_fourfold indices
    (fun i => Real.toNNReal (weight i)) point hevent f,
    Finset.sum_filter, Finset.product_eq_sprod,
    Finset.product_eq_sprod, Finset.product_eq_sprod]
  simp_rw [Set.indicator_apply]
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.coe_toNNReal _ (hweight i hi), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.coe_toNNReal _ (hweight j hj), Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Real.coe_toNNReal _ (hweight k hk), Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Real.coe_toNNReal _ (hweight l hl)]
  by_cases hmem : (((point i, point j), point k), point l) ∈ event <;>
    simp [hmem, mul_assoc]

private theorem logPrimeWeight_nonneg
    {X p : Nat} (hX : 1 < X) (hp : p.Prime) :
    0 ≤ Real.log (p : Real) / ((p : Real) * Real.log (X : Real)) := by
  have hXReal : (1 : Real) < X := by exact_mod_cast hX
  exact div_nonneg hp.log_pos.le
    (mul_nonneg (Nat.cast_nonneg p) (Real.log_pos hXReal).le)

private theorem normalizedPrimeLogFourfoldSum_eq_setIntegral
    {a b : Real} {length : Nat} (hlength : 1 ≤ length)
    {region : Set (((Real × Real) × Real) × Real)}
    (hregion : MeasurableSet region)
    (f : BoundedContinuousFunction (((Real × Real) × Real) × Real) Real) :
    normalizedPrimeLogFourfoldSum a b (10 ^ length) region f =
      ∫ x in region, f x
        ∂((((normalizedPrimeLogIntervalMeasure a b (10 ^ length)).prod
          (normalizedPrimeLogIntervalMeasure a b (10 ^ length))).prod
          (normalizedPrimeLogIntervalMeasure a b (10 ^ length))).prod
          (normalizedPrimeLogIntervalMeasure a b (10 ^ length)) :
            Measure (((Real × Real) × Real) × Real)) := by
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
  simpa only [normalizedPrimeLogFourfoldSum,
    normalizedPrimeLogFourfoldIndices,
    normalizedPrimeLogIntervalMeasure, finiteDirac,
    normalizedPrimeLogWeight, primes] using
      filteredFourfoldSum_eq_setIntegral primes
        (normalizedPrimeLogWeight (10 ^ length))
        (normalizedPrimeLog (10 ^ length)) hregion hweight f

private theorem normalizedPrimeLogIntervalVolume_selfFourfold_toMeasure
    {a b : Real} :
    ((((normalizedPrimeLogIntervalVolume a b).prod
      (normalizedPrimeLogIntervalVolume a b)).prod
      (normalizedPrimeLogIntervalVolume a b)).prod
      (normalizedPrimeLogIntervalVolume a b) :
      Measure (((Real × Real) × Real) × Real)) =
      volume.restrict
        (((Ioc a b ×ˢ Ioc a b) ×ˢ Ioc a b) ×ˢ Ioc a b) := by
  change (((volume.restrict (Ioc a b)).prod
      (volume.restrict (Ioc a b))).prod
      (volume.restrict (Ioc a b))).prod
      (volume.restrict (Ioc a b)) = _
  rw [Measure.prod_restrict, Measure.prod_restrict, Measure.prod_restrict,
    ← Measure.volume_eq_prod, ← Measure.volume_eq_prod,
    ← Measure.volume_eq_prod]

private theorem normalizedPrimeLogIntervalVolume_selfFourfold_frontier_null
    {a b : Real} {region : Set (((Real × Real) × Real) × Real)}
    (hfrontier : volume (frontier region) = 0) :
    ((((normalizedPrimeLogIntervalVolume a b).prod
      (normalizedPrimeLogIntervalVolume a b)).prod
      (normalizedPrimeLogIntervalVolume a b)).prod
      (normalizedPrimeLogIntervalVolume a b) :
      Measure (((Real × Real) × Real) × Real)) (frontier region) = 0 := by
  rw [normalizedPrimeLogIntervalVolume_selfFourfold_toMeasure,
    Measure.restrict_apply isClosed_frontier.measurableSet]
  exact measure_mono_null inter_subset_left hfrontier

private theorem setIntegral_normalizedPrimeLogIntervalVolume_selfFourfold_eq
    {a b : Real} {region : Set (((Real × Real) × Real) × Real)}
    (hbox : region ⊆
      (((Ioc a b ×ˢ Ioc a b) ×ˢ Ioc a b) ×ˢ Ioc a b))
    (f : (((Real × Real) × Real) × Real) → Real) :
    ∫ x in region, f x
        ∂((((normalizedPrimeLogIntervalVolume a b).prod
          (normalizedPrimeLogIntervalVolume a b)).prod
          (normalizedPrimeLogIntervalVolume a b)).prod
          (normalizedPrimeLogIntervalVolume a b) :
          Measure (((Real × Real) × Real) × Real)) =
      ∫ x in region, f x := by
  rw [normalizedPrimeLogIntervalVolume_selfFourfold_toMeasure,
    Measure.restrict_restrict_of_subset hbox]

theorem tendsto_normalizedPrimeLogFourfoldSum_powTen
    {a b : Real} (ha : 0 < a) (hab : a < b)
    {region : Set (((Real × Real) × Real) × Real)}
    (hregion : MeasurableSet region)
    (hbox : region ⊆
      (((Set.Ioc a b ×ˢ Set.Ioc a b) ×ˢ Set.Ioc a b) ×ˢ Set.Ioc a b))
    (hfrontier : volume (frontier region) = 0)
    (f : BoundedContinuousFunction
      (((Real × Real) × Real) × Real) Real) :
    Tendsto
      (fun length : Nat =>
        normalizedPrimeLogFourfoldSum a b (10 ^ length) region f)
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
  have htriple0 : (mu.prod mu).prod mu ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff, FiniteMeasure.mass_prod]
    exact mul_ne_zero
      ((FiniteMeasure.mass_nonzero_iff (mu.prod mu)).mpr hpair0)
      ((FiniteMeasure.mass_nonzero_iff mu).mpr hmu0)
  have hfourfold : Tendsto
      (fun length => (((mus length).prod (mus length)).prod
        (mus length)).prod (mus length))
      atTop (nhds (((mu.prod mu).prod mu).prod mu)) :=
    tendsto_finiteMeasure_prod htriple htriple0 hsingle hmu0
  have hintegrals :=
    tendsto_setIntegral_boundedContinuousFunction_of_null_frontier
      hfourfold hregion
        (normalizedPrimeLogIntervalVolume_selfFourfold_frontier_null hfrontier) f
  rw [setIntegral_normalizedPrimeLogIntervalVolume_selfFourfold_eq hbox f]
    at hintegrals
  apply hintegrals.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with length hlength
  exact (normalizedPrimeLogFourfoldSum_eq_setIntegral
    hlength hregion f).symm

end

end PrimesRestrictedDigits
