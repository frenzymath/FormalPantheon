import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.BasicEstimates.ConvexTrapezoidalUpper
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.SectionSixFirstLowCentralLargeBelowCertificateManifest
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowCertificateConvexity
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowCertificateNodes
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowFiberReduction
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralLargeBelowIntegralBound -/
open MeasureTheory Set
open scoped BigOperators
namespace PrimesRestrictedDigits
noncomputable section
private def belowCertificateDelta : Real := 1 / 1000000
private def belowTrapezoidWeight (N : Nat) (i : Fin (N + 1)) : Real := if i.val = 0 ∨ i.val = N then 1 / 2 else 1
private theorem trapezoidal_integral_twentyEight_eq (f : Real → Real) : trapezoidal_integral f 28 0 1 =
    1 / 28 * ∑ i : Fin 29, belowTrapezoidWeight 28 i * f ((i.val : Real) / 28) := by
  norm_num [trapezoidal_integral, belowTrapezoidWeight, Fin.sum_univ_succ, Finset.sum_range_succ]; ring
private theorem trapezoidal_integral_six_eq (f : Real → Real) : trapezoidal_integral f 6 0 1 =
    1 / 6 * ∑ j : Fin 7, belowTrapezoidWeight 6 j * f ((j.val : Real) / 6) := by
  norm_num [trapezoidal_integral, belowTrapezoidWeight, Fin.sum_univ_succ, Finset.sum_range_succ]; ring
private theorem actual_branch_integral_le_trapezoid (branch : Fin 2) :
    (∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
      sectionSixFirstLowCentralLargeBelowTransformedIntegrand
        Real.log branch x y) ≤
      trapezoidal_integral
        (fun x => trapezoidal_integral
          (sectionSixFirstLowCentralLargeBelowTransformedIntegrand
            Real.log branch x) 6 0 1) 28 0 1 := by
  rcases sectionSixFirstLowCentralLargeBelowTransformedIntegrand_actual_properties branch with
    ⟨hcontinuous, hconvexX, hconvexY⟩
  have hfiber : ∀ x ∈ Icc (0 : Real) 1, IntervalIntegrable
      (sectionSixFirstLowCentralLargeBelowTransformedIntegrand Real.log branch x) volume 0 1 := by
    intro x hx
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact hcontinuous.comp (Continuous.prodMk_right x).continuousOn (fun y hy => ⟨hx, hy⟩)
  have hjoint : IntegrableOn (fun z : Real × Real =>
      sectionSixFirstLowCentralLargeBelowTransformedIntegrand Real.log branch z.1 z.2)
      (Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) :=
    hcontinuous.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hnested : IntervalIntegrable
      (fun x => ∫ y in (0 : Real)..1,
        sectionSixFirstLowCentralLargeBelowTransformedIntegrand
          Real.log branch x y) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2
    apply integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
      (Icc (0 : Real) 1) (fun _ : Real => 0) (fun _ => 1)
      (fun z : Real × Real =>
        sectionSixFirstLowCentralLargeBelowTransformedIntegrand
          Real.log branch z.1 z.2)
      measurableSet_Icc measurable_const measurable_const
      (fun _ _ => zero_le_one)
    rw [show closedIccFiberCell (Icc (0 : Real) 1) (fun _ : Real => 0) (fun _ => 1) = Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1 by rfl, ← Measure.volume_eq_prod]
    exact hjoint
  exact iteratedIntervalIntegral_le_tensorTrapezoidalIntegral_of_separatelyConvexOn zero_le_one
    zero_le_one (by norm_num) (by norm_num) hconvexX hconvexY hfiber hnested
private theorem log_le_cayley_five {r : Real} (hr : 1 ≤ r) :
    Real.log r ≤ cayleyLogSeriesUpper ((r - 1) / (r + 1)) 5 := by
  have hden : 0 < r + 1 := by linarith
  have hx : 0 ≤ (r - 1) / (r + 1) := div_nonneg (sub_nonneg.mpr hr) hden.le
  have hxOne : (r - 1) / (r + 1) < 1 := by
    rw [div_lt_one hden]
    linarith
  have hreconstruct :
      (1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1)) = r := by
    field_simp [hden.ne']
    ring
  have hlog := log_cayley_le_cayleyLogSeriesUpper hx hxOne 5
  rw [hreconstruct] at hlog
  exact hlog
private theorem transformed_actual_le_cayley (branch : Fin 2) {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    sectionSixFirstLowCentralLargeBelowTransformedIntegrand Real.log branch x y ≤
      sectionSixFirstLowCentralLargeBelowTransformedIntegrand
        (fun r => cayleyLogSeriesUpper ((r - 1) / (r + 1)) 5) branch x y := by
  let X : Real := (40003 / 500000) * x
  let u : Real := 69999 / 250000 + X
  have hX : X ∈ Icc (0 : Real) (40003 / 500000) := by
    dsimp [X]
    constructor
    · exact mul_nonneg (by norm_num) hx.1
    · nlinarith [hx.2]
  have hu : 0 < u := by dsimp [u]; nlinarith [hX.1]
  have hA : 0 < (319999 / 500000 : Real) - u := by
    dsimp [u]
    norm_num at hX ⊢
    linarith
  have hu' : (69999 / 250000 : Real) + 40003 / 500000 * x = u := by dsimp [u, X]
  by_cases hbranch : branch = (0 : Fin 2)
  · subst branch
    let k : Real := (2 - y) / 4
    let v : Real := 180001 / 500000 / 2 - k * X
    let rest : Real := 1 - u - v
    let ratio : Real := 2 * (180001 / 500000 - v) / (319999 / 500000 - u)
    have hk : k ∈ Icc (1 / 4 : Real) (1 / 2) := by dsimp [k]; constructor <;> linarith [hy.1, hy.2]
    have hk0 : 0 ≤ k := by linarith [hk.1]
    have hkX : k * X ≤ (1 / 2 : Real) * (40003 / 500000) :=
      mul_le_mul hk.2 hX.2 hX.1 (by norm_num)
    have hv : 0 < v := by dsimp [v]; norm_num at hkX ⊢; linarith
    have hthetaV : 0 < (180001 / 500000 : Real) - v := by dsimp [v]; nlinarith [mul_nonneg hk0 hX.1]
    have hrest : 0 < rest := by dsimp [rest]; norm_num at hA hthetaV ⊢; linarith
    have hratio : 1 ≤ ratio := by
      dsimp [ratio]
      rw [le_div_iff₀ hA]
      dsimp [u, v]
      have hdiff : 2 * (180001 / 500000 - (180001 / 500000 / 2 - k * X)) - 1 * (319999 / 500000 - (69999 / 250000 + X)) = (2 * k + 1) * X := by ring
      rw [← sub_nonneg, hdiff]
      exact mul_nonneg (by linarith [hk0]) hX.1
    have hlog := log_le_cayley_five hratio; have hden : 0 < u * v * rest := mul_pos (mul_pos hu hv) hrest
    have hv' : (180001 / 500000 : Real) / 2 - 40003 / 500000 * x * (2 - y) / 4 = v := by dsimp [v, k, X]; ring
    have hrest' : 1 - (69999 / 250000 + 40003 / 500000 * x) - (180001 / 500000 / 2 - 40003 / 500000 * x * (2 - y) / 4) = rest := by change 1 - (69999 / 250000 + 40003 / 500000 * x) - (180001 / 500000 / 2 - 40003 / 500000 * x * (2 - y) / 4) = 1 - u - v; rw [hu', hv']
    have hratio' : 2 * ((180001 / 500000 : Real) - (180001 / 500000 / 2 - 40003 / 500000 * x * (2 - y) / 4)) / ((319999 / 500000 : Real) - (69999 / 250000 + 40003 / 500000 * x)) = ratio := by change 2 * ((180001 / 500000 : Real) - (180001 / 500000 / 2 - 40003 / 500000 * x * (2 - y) / 4)) / ((319999 / 500000 : Real) - (69999 / 250000 + 40003 / 500000 * x)) = 2 * (180001 / 500000 - v) / (319999 / 500000 - u); rw [hu', hv']
    have hactual : sectionSixFirstLowCentralLargeBelowTransformedIntegrand Real.log (0 : Fin 2) x y = x * (Real.log ratio / (u * v * rest) + (564663 / 1000000 : Real) / (u * v) * (1 / v - 3 / rest)) := by simp only [sectionSixFirstLowCentralLargeBelowTransformedIntegrand, if_pos]; rw [hrest', hratio', hu', hv']; ring
    have hcayley : sectionSixFirstLowCentralLargeBelowTransformedIntegrand (fun r => cayleyLogSeriesUpper ((r - 1) / (r + 1)) 5) (0 : Fin 2) x y = x * (cayleyLogSeriesUpper ((ratio - 1) / (ratio + 1)) 5 / (u * v * rest) + (564663 / 1000000 : Real) / (u * v) * (1 / v - 3 / rest)) := by simp only [sectionSixFirstLowCentralLargeBelowTransformedIntegrand, if_pos]; rw [hrest', hratio', hu', hv']; ring
    rw [hactual, hcayley]
    exact mul_le_mul_of_nonneg_left (add_le_add_left ((div_le_div_iff_of_pos_right hden).2 hlog) ((564663 / 1000000 : Real) / (u * v) * (1 / v - 3 / rest))) hx.1
  · have hbranch1 : branch = (1 : Fin 2) := by
      fin_cases branch
      · exact (hbranch rfl).elim
      · rfl
    subst branch
    let k : Real := (1 - y) / 4
    let v : Real := 180001 / 500000 / 2 - k * X
    let rest : Real := 1 - u - v
    let q : Real := 1 - u - 2 * v
    let ratio : Real :=
      (180001 / 500000 - v) * q / (v * (319999 / 500000 - u))
    have hk : k ∈ Icc (0 : Real) (1 / 4) := by dsimp [k]; constructor <;> linarith [hy.1, hy.2]
    have hkX : k * X ≤ (1 / 4 : Real) * (40003 / 500000) :=
      mul_le_mul hk.2 hX.2 hX.1 (by norm_num)
    have hv : 0 < v := by dsimp [v]; norm_num at hkX ⊢; linarith
    have hthetaV : 0 < (180001 / 500000 : Real) - v := by dsimp [v]; nlinarith [mul_nonneg hk.1 hX.1]
    have hrest : 0 < rest := by dsimp [rest]; norm_num at hA hthetaV ⊢; linarith
    have hfactor : 0 ≤ 1 - 2 * k ∧ 1 - 2 * k ≤ 1 := by constructor <;> linarith [hk.1, hk.2]
    have hfactorX : (1 - 2 * k) * X ≤ (40003 / 500000 : Real) := by
      nlinarith [mul_le_mul hfactor.2 hX.2 hX.1 (by norm_num)]
    have hq : 0 < q := by
      dsimp [q, u, v]
      norm_num at hfactorX ⊢
      linarith
    have hratio : 1 ≤ ratio := by
      dsimp [ratio]
      rw [le_div_iff₀ (mul_pos hv hA)]
      have hid :
          (180001 / 500000 - v) * q - v * (319999 / 500000 - u) =
            2 * k * X * rest := by
        dsimp [q, rest, u, v]
        ring
      rw [← sub_nonneg]
      have hdiff : 0 ≤ (180001 / 500000 - v) * q - v * (319999 / 500000 - u) := by rw [hid]; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk.1) hX.1) hrest.le
      simpa only [one_mul] using hdiff
    have hlog := log_le_cayley_five hratio; have hden : 0 < u * v * rest := mul_pos (mul_pos hu hv) hrest
    have hv' : (180001 / 500000 : Real) / 2 - 40003 / 500000 * x * (1 - y) / 4 = v := by dsimp [v, k, X]; ring
    have hrest' : 1 - (69999 / 250000 + 40003 / 500000 * x) - (180001 / 500000 / 2 - 40003 / 500000 * x * (1 - y) / 4) = rest := by change 1 - (69999 / 250000 + 40003 / 500000 * x) - (180001 / 500000 / 2 - 40003 / 500000 * x * (1 - y) / 4) = 1 - u - v; rw [hu', hv']
    have hratio' : ((180001 / 500000 : Real) - (180001 / 500000 / 2 - 40003 / 500000 * x * (1 - y) / 4)) * (1 - (69999 / 250000 + 40003 / 500000 * x) - 2 * (180001 / 500000 / 2 - 40003 / 500000 * x * (1 - y) / 4)) / ((180001 / 500000 / 2 - 40003 / 500000 * x * (1 - y) / 4) * ((319999 / 500000 : Real) - (69999 / 250000 + 40003 / 500000 * x))) = ratio := by change ((180001 / 500000 : Real) - (180001 / 500000 / 2 - 40003 / 500000 * x * (1 - y) / 4)) * (1 - (69999 / 250000 + 40003 / 500000 * x) - 2 * (180001 / 500000 / 2 - 40003 / 500000 * x * (1 - y) / 4)) / ((180001 / 500000 / 2 - 40003 / 500000 * x * (1 - y) / 4) * ((319999 / 500000 : Real) - (69999 / 250000 + 40003 / 500000 * x))) = (180001 / 500000 - v) * q / (v * (319999 / 500000 - u)); rw [hu', hv']
    have hactual : sectionSixFirstLowCentralLargeBelowTransformedIntegrand Real.log (1 : Fin 2) x y = x * (Real.log ratio / (u * v * rest) + 0) := by simp only [sectionSixFirstLowCentralLargeBelowTransformedIntegrand, if_neg hbranch]; rw [hrest', hratio', hu', hv']; ring
    have hcayley : sectionSixFirstLowCentralLargeBelowTransformedIntegrand (fun r => cayleyLogSeriesUpper ((r - 1) / (r + 1)) 5) (1 : Fin 2) x y = x * (cayleyLogSeriesUpper ((ratio - 1) / (ratio + 1)) 5 / (u * v * rest) + 0) := by simp only [sectionSixFirstLowCentralLargeBelowTransformedIntegrand, if_neg hbranch]; rw [hrest', hratio', hu', hv']; ring
    rw [hactual, hcayley]
    exact mul_le_mul_of_nonneg_left (add_le_add_left ((div_le_div_iff_of_pos_right hden).2 hlog) (0 : Real)) hx.1
private theorem scaled_trapezoid_sum_le_node_sum :
    (40003 / 500000 : Real) ^ 2 / 4 *
        ∑ branch : Fin 2,
          trapezoidal_integral
            (fun x => trapezoidal_integral
              (sectionSixFirstLowCentralLargeBelowTransformedIntegrand
                Real.log branch x) 6 0 1) 28 0 1 ≤
      ∑ index : Fin 2 × Fin 29 × Fin 7,
        sectionSixFirstLowCentralLargeBelowCertificateNode index := by
  simp_rw [trapezoidal_integral_twentyEight_eq,
    trapezoidal_integral_six_eq]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro branch _
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold sectionSixFirstLowCentralLargeBelowCertificateNode
  have hi : (i.val : Real) / 28 ∈ Icc (0 : Real) 1 := by
    constructor
    · positivity
    · rw [div_le_one (by norm_num)]
      exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
  have hj : (j.val : Real) / 6 ∈ Icc (0 : Real) 1 := by
    constructor
    · positivity
    · rw [div_le_one (by norm_num)]
      exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)
  have hpoint := transformed_actual_le_cayley branch hi hj
  have hwi : 0 ≤ belowTrapezoidWeight 28 i := by
    simp only [belowTrapezoidWeight]
    split_ifs <;> norm_num
  have hwj : 0 ≤ belowTrapezoidWeight 6 j := by
    simp only [belowTrapezoidWeight]
    split_ifs <;> norm_num
  have hscale : 0 ≤ (40003 / 500000 : Real) ^ 2 / (4 * 28 * 6) := by positivity
  dsimp only
  simp only [belowTrapezoidWeight]
  have hweighted := mul_le_mul_of_nonneg_left hpoint (mul_nonneg (mul_nonneg hscale hwi) hwj)
  calc
    _ = (40003 / 500000 : Real) ^ 2 / (4 * 28 * 6) * belowTrapezoidWeight 28 i * belowTrapezoidWeight 6 j *
        sectionSixFirstLowCentralLargeBelowTransformedIntegrand Real.log branch ((i.val : Real) / 28) ((j.val : Real) / 6) := by
      simp only [belowTrapezoidWeight]; ring_nf
    _ ≤ (40003 / 500000 : Real) ^ 2 / (4 * 28 * 6) * belowTrapezoidWeight 28 i * belowTrapezoidWeight 6 j * sectionSixFirstLowCentralLargeBelowTransformedIntegrand (fun ratio => cayleyLogSeriesUpper ((ratio - 1) / (ratio + 1)) 5) branch ((i.val : Real) / 28) ((j.val : Real) / 6) := hweighted
    _ = _ := by simp only [belowTrapezoidWeight]
theorem
    sectionSixFirstLowCentralLargeBelowIntegral_certificateDelta_le_node_sum :
    sectionSixFirstLowCentralLargeBelowIntegral (1 / 1000000) <=
      ∑ index : Fin 2 × Fin 29 × Fin 7,
        sectionSixFirstLowCentralLargeBelowCertificateNode index := by
  calc
    _ ≤ (40003 / 500000 : Real) ^ 2 / 4 *
        ∑ branch : Fin 2,
          ∫ x in (0 : Real)..1, ∫ y in (0 : Real)..1,
            sectionSixFirstLowCentralLargeBelowTransformedIntegrand
              Real.log branch x y :=
      sectionSixFirstLowCentralLargeBelowIntegral_certificateDelta_le_transformedIntegral
    _ ≤ (40003 / 500000 : Real) ^ 2 / 4 *
        ∑ branch : Fin 2,
          trapezoidal_integral
            (fun x => trapezoidal_integral
              (sectionSixFirstLowCentralLargeBelowTransformedIntegrand
                Real.log branch x) 6 0 1) 28 0 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun branch _ => actual_branch_integral_le_trapezoid branch
    _ ≤ _ := scaled_trapezoid_sum_le_node_sum
private theorem kernel_integrableOn_delta : IntegrableOn sectionSixFirstLowCentralLargeBelowKernel
    (sectionSixFirstLowCentralLargeBelowRegion belowCertificateDelta) := by
  let extension := sectionSixFirstLowCentralLargeBelowKernelExtension
    belowCertificateDelta (by norm_num [belowCertificateDelta])
      (by norm_num [belowCertificateDelta])
  have hext : IntegrableOn (fun z => extension z)
      ((Icc (sectionSixThetaGap belowCertificateDelta) (1 / 2) ×ˢ
        Icc (sectionSixThetaGap belowCertificateDelta) (1 / 2)) ×ˢ
          Icc (sectionSixThetaGap belowCertificateDelta) (1 / 2)) :=
    extension.continuous.continuousOn.integrableOn_compact
      ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  have hsubset : sectionSixFirstLowCentralLargeBelowRegion belowCertificateDelta ⊆
      ((Icc (sectionSixThetaGap belowCertificateDelta) (1 / 2) ×ˢ
        Icc (sectionSixThetaGap belowCertificateDelta) (1 / 2)) ×ˢ
          Icc (sectionSixThetaGap belowCertificateDelta) (1 / 2)) := by
    intro z hz
    rcases sectionSixFirstLowCentralLargeBelowRegion_subset_logBox
      belowCertificateDelta (by norm_num [belowCertificateDelta])
        (by norm_num [belowCertificateDelta]) hz with ⟨⟨hu, hv⟩, hw⟩
    exact ⟨⟨⟨hu.1.le, hu.2⟩, ⟨hv.1.le, hv.2⟩⟩, ⟨hw.1.le, hw.2⟩⟩
  apply (hext.mono_set hsubset).congr_fun
  · simpa [extension] using
      sectionSixFirstLowCentralLargeBelowKernelExtension_eq_on_region
        belowCertificateDelta (by norm_num [belowCertificateDelta])
          (by norm_num [belowCertificateDelta])
  · exact measurableSet_sectionSixFirstLowCentralLargeBelowRegion belowCertificateDelta
private theorem kernel_nonneg_on_delta {z : (Real × Real) × Real}
    (hz : z ∈ sectionSixFirstLowCentralLargeBelowRegion belowCertificateDelta) :
    0 ≤ sectionSixFirstLowCentralLargeBelowKernel z := by
  rcases hz with ⟨hgap, horder, _, _, _, _, _, hvw, hcap, _⟩
  have hgapPos : 0 < sectionSixThetaGap belowCertificateDelta :=
    (sectionSix_parameter_bounds (by norm_num [belowCertificateDelta])
      (by norm_num [belowCertificateDelta])).1
  have hv : 0 < z.1.2 := hgapPos.trans hgap
  have hu : 0 < z.1.1 := hv.trans_le horder
  have hw : 0 < z.2 := hv.trans hvw
  have harg : 1 ≤ (1 - z.1.1 - z.1.2 - z.2) / z.2 := by
    rw [le_div_iff₀ hw]
    linarith
  have homega := (buchstabFunction_mem_Icc harg).1
  unfold sectionSixFirstLowCentralLargeBelowKernel
  exact div_nonneg (by linarith [homega])
    (mul_nonneg (mul_nonneg hu.le hv.le) (sq_nonneg _))
theorem sectionSixFirstLowCentralLargeBelowIntegral_lt
    {epsilon : Real}
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstLowCentralLargeBelowIntegral epsilon <
      (57 : Real) / 4000 := by
  have hdelta : sectionSixFirstLowCentralLargeBelowIntegral belowCertificateDelta <
      (57 : Real) / 4000 :=
    (sectionSixFirstLowCentralLargeBelowIntegral_certificateDelta_le_node_sum.trans_lt
      sectionSixFirstLowCentralLargeBelowCertificate_node_sum_lt).trans
        (by norm_num)
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (sectionSixFirstLowCentralLargeBelowRegion belowCertificateDelta)]
      sectionSixFirstLowCentralLargeBelowKernel :=
    ae_restrict_of_forall_mem
      (measurableSet_sectionSixFirstLowCentralLargeBelowRegion belowCertificateDelta)
      (fun z hz => kernel_nonneg_on_delta hz)
  unfold sectionSixFirstLowCentralLargeBelowIntegral
  exact (setIntegral_mono_set kernel_integrableOn_delta hnonneg
    (Filter.Eventually.of_forall
      (sectionSixFirstLowCentralLargeBelowRegion_mono
        (by simpa [belowCertificateDelta] using hepsilonUpper)))).trans_lt hdelta
end
end PrimesRestrictedDigits
