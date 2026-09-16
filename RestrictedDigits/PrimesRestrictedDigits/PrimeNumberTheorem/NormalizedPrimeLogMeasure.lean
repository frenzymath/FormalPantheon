import PrimesRestrictedDigits.PrimeNumberTheorem.NormalizedPrimeLogWeight
import PrimesRestrictedDigits.MajorArcs.ProjectedBox
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Normalized logarithmic prime measures

The scalar prime-weight limit is upgraded to weak convergence of finite
measures by testing all real half-open intervals and normalizing their mass.
-/

open Finset Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def normalizedPrimeLogIntervalMeasure (a b : Real) (X : Nat) : FiniteMeasure Real :=
  ∑ p ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b),
    let atom : FiniteMeasure Real :=
      ⟨Measure.dirac (normalizedPrimeLog X p), inferInstance⟩
    Real.toNNReal (normalizedPrimeLogWeight X p) • atom

noncomputable def normalizedPrimeLogIntervalVolume (a b : Real) : FiniteMeasure Real :=
  ⟨volume.restrict (Ioc a b), inferInstance⟩

private noncomputable def weightError (C alpha beta X : Real) : Real :=
  2 * beta * X ^ (-alpha) +
    (((C / beta) * (Real.log X)⁻¹ * (Real.log X)⁻¹ + beta * X ^ (-beta)) +
      ((C / alpha) * (Real.log X)⁻¹ * (Real.log X)⁻¹ + alpha * X ^ (-alpha)) +
      C * (Real.log X)⁻¹ * Real.log (beta / alpha))

private theorem tendsto_weightError {C alpha beta : Real}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Tendsto (weightError C alpha beta) atTop (nhds 0) := by
  have ha := tendsto_rpow_neg_atTop halpha
  have hb := tendsto_rpow_neg_atTop hbeta
  have hl := Real.tendsto_log_atTop.inv_tendsto_atTop
  unfold weightError
  have h1 := ha.const_mul (2 * beta)
  have h2 := ((hl.const_mul (C / beta)).mul hl).add (hb.const_mul beta)
  have h3 := ((hl.const_mul (C / alpha)).mul hl).add (ha.const_mul alpha)
  have h4 := (hl.const_mul C).mul_const (Real.log (beta / alpha))
  convert h1.add (((h2.add h3).add h4)) using 1
  · funext x
    simp only [div_eq_mul_inv, Pi.inv_apply]
  · simp

private theorem tendsto_realWeight_sieve_rpow {alpha beta : Real}
    (halpha : 0 < alpha) (hab : alpha < beta) :
    Tendsto (fun X : Real => ∑ p ∈ sievePrimeInterval (X ^ alpha) (X ^ beta),
      NormalizedPrimeLogWeight.realWeight X p) atTop (nhds (beta - alpha)) := by
  obtain ⟨C, hC, hPNT⟩ := primeCounting_log_sq_error
  have hbeta : 0 < beta := halpha.trans hab
  have herror := tendsto_weightError (C := C) halpha hbeta
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (g := weightError C alpha beta)
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (1 : Real),
      (tendsto_rpow_atTop halpha).eventually_ge_atTop (Real.exp 1)] with X hX hXa
    have hX0 : 0 < X := zero_lt_one.trans hX
    have hlogX : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
    have hpow : X ^ alpha ≤ X ^ beta :=
      Real.rpow_le_rpow_of_exponent_le hX.le hab.le
    have hraw := NormalizedPrimeLogWeight.sieve_error_le hC hX hXa hpow hPNT
    have htarget : Real.log (X ^ beta / X ^ alpha) / Real.log X =
        beta - alpha := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_rpow hX0, Real.log_rpow hX0]
      field_simp [hlogX]
    rw [htarget] at hraw
    convert hraw using 1
    · exact Real.norm_eq_abs _
    · unfold weightError
      rw [Real.log_rpow hX0, Real.log_rpow hX0,
        Real.rpow_neg hX0.le, Real.rpow_neg hX0.le]
      field_simp [hlogX, halpha.ne', hbeta.ne']
  · exact herror

theorem tendsto_normalizedPrimeLogIntervalWeight_powTen {a b : Real} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun length : Nat => ∑ p ∈ sievePrimeInterval
      (((10 ^ length : Nat) : Real) ^ a) (((10 ^ length : Nat) : Real) ^ b),
      normalizedPrimeLogWeight (10 ^ length) p) atTop (nhds (b - a)) := by
  have hpow : Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (10 : Nat)))
  convert (tendsto_realWeight_sieve_rpow ha hab).comp hpow using 1
  funext length
  simp only [Function.comp_apply, normalizedPrimeLogWeight,
    NormalizedPrimeLogWeight.realWeight]

private theorem measure_apply {a b : Real} {X : Nat} {s : Set Real}
    (hs : MeasurableSet s) :
    ((normalizedPrimeLogIntervalMeasure a b X : FiniteMeasure Real) : Measure Real) s =
      ∑ p ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b),
        Real.toNNReal (normalizedPrimeLogWeight X p) •
          s.indicator (1 : Real → ENNReal) (normalizedPrimeLog X p) := by
  classical
  simp [normalizedPrimeLogIntervalMeasure, hs]

private theorem target_mass {a b : Real} (hab : a ≤ b) :
    (normalizedPrimeLogIntervalVolume a b).mass = Real.toNNReal (b - a) := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab)]
  change (volume.restrict (Ioc a b)).real univ = b - a
  rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

private theorem weight_nonneg {X p : Nat} (hX : 1 < X) (hp : p.Prime) :
    0 ≤ normalizedPrimeLogWeight X p := by
  unfold normalizedPrimeLogWeight
  have hX' : (1 : Real) < X := by exact_mod_cast hX
  have hp' : (1 : Real) ≤ p := by exact_mod_cast hp.one_le
  positivity

private theorem carrier_eq {a b c d : Real} {X : Nat} (hX : 1 < X) :
    (sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b)).filter
        (fun p => normalizedPrimeLog X p ∈ Ioc c d) =
      sievePrimeInterval ((X : Real) ^ max a c) ((X : Real) ^ min b d) := by
  classical
  ext p
  by_cases hp : p.Prime
  · rw [Finset.mem_filter, mem_sievePrimeInterval, mem_sievePrimeInterval,
      ← normalizedPrimeLog_mem_Ioc_iff_rpow hX hp a b,
      ← normalizedPrimeLog_mem_Ioc_iff_rpow hX hp (max a c) (min b d)]
    simp only [hp, true_and, Set.mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  · simp [mem_sievePrimeInterval, hp]

private theorem eval_Ioc_toReal {a b c d : Real} {X : Nat} (hX : 1 < X) :
    (((normalizedPrimeLogIntervalMeasure a b X : FiniteMeasure Real) : Measure Real) (Ioc c d)).toReal =
      ∑ p ∈ sievePrimeInterval ((X : Real) ^ max a c) ((X : Real) ^ min b d),
        normalizedPrimeLogWeight X p := by
  classical
  rw [measure_apply measurableSet_Ioc]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_smul, Set.indicator, Pi.one_apply, NNReal.smul_def,
      smul_eq_mul, apply_ite, ENNReal.toReal_one, ENNReal.toReal_zero, mul_one,
      mul_zero]
    rw [← Finset.sum_filter, carrier_eq hX]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.coe_toNNReal _ (weight_nonneg hX (mem_sievePrimeInterval.mp hp).1)]
  · intro p hp
    by_cases h : normalizedPrimeLog X p ∈ Ioc c d <;>
      simp [Set.indicator, h]

private theorem target_Ioc_toReal (a b c d : Real) :
    (((normalizedPrimeLogIntervalVolume a b : FiniteMeasure Real) : Measure Real) (Ioc c d)).toReal =
      max (min b d - max a c) 0 := by
  rw [show ((normalizedPrimeLogIntervalVolume a b : FiniteMeasure Real) : Measure Real) =
      volume.restrict (Ioc a b) from rfl,
    Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc,
    Real.volume_Ioc, ENNReal.toReal_ofReal']
  rw [max_comm a c, min_comm b d]

private theorem finite_apply_coe (measure : FiniteMeasure Real) (s : Set Real) :
    ((measure s : NNReal) : Real) = ((measure : Measure Real) s).toReal := by
  rw [show ((measure s : NNReal) : Real) =
      ((((measure s : NNReal) : ENNReal)).toReal) by exact (ENNReal.coe_toReal _).symm,
    FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

private theorem mass_coe {a b : Real} {X : Nat} (hX : 1 < X) :
    ((normalizedPrimeLogIntervalMeasure a b X).mass : Real) =
      ∑ p ∈ sievePrimeInterval ((X : Real) ^ a) ((X : Real) ^ b),
        normalizedPrimeLogWeight X p := by
  rw [show ((normalizedPrimeLogIntervalMeasure a b X).mass : Real) =
      ((((normalizedPrimeLogIntervalMeasure a b X).mass : NNReal) : ENNReal).toReal) by
        exact (ENNReal.coe_toReal _).symm,
    FiniteMeasure.ennreal_mass, measure_apply MeasurableSet.univ,
    ENNReal.toReal_sum]
  · simp only [Set.indicator_of_mem (mem_univ _), Pi.one_apply,
      ENNReal.toReal_smul, ENNReal.toReal_one, NNReal.smul_def, smul_eq_mul, mul_one]
    apply Finset.sum_congr rfl
    intro p hp
    exact Real.coe_toNNReal _ (weight_nonneg hX (mem_sievePrimeInterval.mp hp).1)
  · intro p hp
    simp

private theorem tendsto_mass {a b : Real} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun length : Nat => (normalizedPrimeLogIntervalMeasure a b (10 ^ length)).mass) atTop
      (nhds (Real.toNNReal (b - a))) := by
  apply NNReal.tendsto_coe.mp
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)]
  apply (tendsto_normalizedPrimeLogIntervalWeight_powTen ha hab).congr'
  filter_upwards [eventually_ge_atTop 1] with length hlength
  rw [mass_coe]
  exact Nat.one_lt_pow (Nat.ne_of_gt hlength) (by norm_num)

private theorem tendsto_eval_Ioc {a b c d : Real} (ha : 0 < a) :
    Tendsto
      (fun length : Nat =>
        (((normalizedPrimeLogIntervalMeasure a b (10 ^ length) : FiniteMeasure Real) : Measure Real) (Ioc c d)))
      atTop (nhds (((normalizedPrimeLogIntervalVolume a b : FiniteMeasure Real) : Measure Real) (Ioc c d))) := by
  apply (ENNReal.tendsto_toReal_iff
    (fun _ => ne_of_lt (measure_lt_top _ _)) (ne_of_lt (measure_lt_top _ _))).mp
  rw [target_Ioc_toReal]
  by_cases hclamp : max a c < min b d
  · have hpositive : 0 < max a c := ha.trans_le (le_max_left _ _)
    have hsum := tendsto_normalizedPrimeLogIntervalWeight_powTen hpositive hclamp
    rw [max_eq_left (sub_nonneg.mpr hclamp.le)]
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with length hlength
    rw [eval_Ioc_toReal]
    exact Nat.one_lt_pow (Nat.ne_of_gt hlength) (by norm_num)
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hclamp))]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with length hlength
    symm
    have hX : 1 < 10 ^ length :=
      Nat.one_lt_pow (Nat.ne_of_gt hlength) (by norm_num)
    rw [eval_Ioc_toReal hX]
    apply Finset.sum_eq_zero
    intro p hp
    exfalso
    have hm := (mem_sievePrimeInterval.mp hp).2
    have hbase : (1 : Real) ≤ (10 ^ length : Nat) := by exact_mod_cast hX.le
    have hpow := Real.rpow_le_rpow_of_exponent_le
      hbase (le_of_not_gt hclamp)
    linarith

private theorem tendsto_probability_of_tendsto_Ioc
    {ι : Type*} {mus : ι → ProbabilityMeasure Real}
    {target : ProbabilityMeasure Real} {l : Filter ι} [l.IsCountablyGenerated]
    (h : ∀ c d : Real, c < d →
      Tendsto (fun i => mus i (Ioc c d)) l (nhds (target (Ioc c d)))) :
    Tendsto mus l (nhds target) := by
  let S : Set (Set Real) := {s | ∃ c d : Real, c < d ∧ Ioc c d = s}
  have hpi : IsPiSystem S := by
    simpa only [S, id_eq] using
      (isPiSystem_Ioc (id : Real → Real) (id : Real → Real))
  apply hpi.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨c, d, hcd, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hxu
    obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hu x hxu
    let c := x - epsilon / 2
    let d := x + epsilon / 2
    refine ⟨Ioc c d, ⟨c, d, by dsimp [c, d]; linarith, rfl⟩, ?_, ?_⟩
    · apply mem_of_superset (Ioo_mem_nhds (a := c) (b := d)
          (by dsimp [c]; linarith) (by dsimp [d]; linarith))
      exact Ioo_subset_Ioc_self
    · intro y hy
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have hyc : x - epsilon / 2 < y := by simpa [c] using hy.1
      have hyd : y ≤ x + epsilon / 2 := by simpa [d] using hy.2
      exact abs_lt.2 ⟨by linarith, by linarith⟩
  · rintro s ⟨c, d, hcd, rfl⟩
    exact h c d hcd

theorem tendsto_normalizedPrimeLogIntervalMeasure_powTen {a b : Real} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun length : Nat => normalizedPrimeLogIntervalMeasure a b (10 ^ length)) atTop (nhds (normalizedPrimeLogIntervalVolume a b)) := by
  have hmass := tendsto_mass ha hab
  have htargetMass : (normalizedPrimeLogIntervalVolume a b).mass = Real.toNNReal (b - a) := target_mass hab.le
  have hmassPos : 0 < Real.toNNReal (b - a) := Real.toNNReal_pos.2 (sub_pos.2 hab)
  have htargetNonzero : normalizedPrimeLogIntervalVolume a b ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff, htargetMass]
    exact hmassPos.ne'
  have hnormalized : Tendsto (fun length : Nat => (normalizedPrimeLogIntervalMeasure a b (10 ^ length)).normalize)
      atTop (nhds (normalizedPrimeLogIntervalVolume a b).normalize) := by
    apply tendsto_probability_of_tendsto_Ioc
    intro c d hcd
    have heval := tendsto_eval_Ioc (a := a) (b := b) (c := c) (d := d) ha
    apply NNReal.tendsto_coe.mp
    have hevalReal := (ENNReal.tendsto_toReal_iff
      (fun _ => ne_of_lt (measure_lt_top _ _))
      (ne_of_lt (measure_lt_top _ _))).mpr heval
    have hmassReal : Tendsto (fun length : Nat =>
        ((normalizedPrimeLogIntervalMeasure a b (10 ^ length)).mass : Real)) atTop (nhds (b - a)) := by
      simpa [Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)] using
        (NNReal.tendsto_coe.mpr hmass)
    have hratio := hevalReal.div hmassReal (sub_ne_zero.mpr hab.ne')
    have htargetRatio :
        ((normalizedPrimeLogIntervalVolume a b : Measure Real) (Ioc c d)).toReal / (b - a) =
          (((normalizedPrimeLogIntervalVolume a b).normalize (Ioc c d) : NNReal) : Real) := by
      rw [FiniteMeasure.normalize_eq_of_nonzero _ htargetNonzero,
        NNReal.coe_mul, NNReal.coe_inv, finite_apply_coe, htargetMass,
        Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)]
      ring
    rw [← htargetRatio]
    apply hratio.congr'
    have hnonzero : ∀ᶠ length : Nat in atTop, normalizedPrimeLogIntervalMeasure a b (10 ^ length) ≠ 0 :=
      (hmass.eventually_ne hmassPos.ne').mono fun length h =>
        ((normalizedPrimeLogIntervalMeasure a b (10 ^ length)).mass_nonzero_iff).mp h
    filter_upwards [hnonzero] with length hlength
    rw [FiniteMeasure.normalize_eq_of_nonzero _ hlength,
      NNReal.coe_mul, NNReal.coe_inv, finite_apply_coe]
    change ((normalizedPrimeLogIntervalMeasure a b (10 ^ length) : Measure Real) (Ioc c d)).toReal /
        ((normalizedPrimeLogIntervalMeasure a b (10 ^ length)).mass : Real) = _
    rw [div_eq_mul_inv, mul_comm]
  exact (FiniteMeasure.tendsto_normalize_iff_tendsto htargetNonzero).mp
    ⟨hnormalized, by simpa [htargetMass] using hmass⟩

end
end PrimesRestrictedDigits
