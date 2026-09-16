import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9TailIntegration
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateManifest
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralSmallQuadrupleI9TailOuterBound -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def i9toH (z : Real) : Real :=
  Real.log (z / sectionSixFirstHighCentralSmallI9Gamma) /
      sectionSixFirstHighCentralSmallI9Gamma +
    1 / z - 1 / sectionSixFirstHighCentralSmallI9Gamma

private def i9toF (z : Real) : Real :=
  Real.log (z / sectionSixFirstHighCentralSmallI9Gamma) ^ 2 /
      (2 * sectionSixFirstHighCentralSmallI9Gamma) +
    1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / z -
      Real.log (z / sectionSixFirstHighCentralSmallI9Gamma) /
        sectionSixFirstHighCentralSmallI9Gamma

private theorem i9to_H_integral {v : Real}
    (hgv : sectionSixFirstHighCentralSmallI9Gamma ≤ v) :
    (∫ w in sectionSixFirstHighCentralSmallI9Gamma..v,
      (1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / w) / w) =
      i9toH v := by
  let g : Real := sectionSixFirstHighCentralSmallI9Gamma
  let F : Real → Real := fun z =>
    Real.log (z / g) / g + 1 / z - 1 / g
  have hg : 0 < g := sectionSixFirstHighCentralSmallI9_constants.1
  have hv : 0 < v := hg.trans_le hgv
  have hderiv : ∀ z ∈ uIcc g v,
      HasDerivAt F ((1 / g - 1 / z) / z) z := by
    intro z hz
    rw [uIcc_of_le hgv] at hz
    have hzpos : 0 < z := hg.trans_le hz.1
    have hlog := (Real.hasDerivAt_log (div_pos hzpos hg).ne').comp z
      ((hasDerivAt_id z).div_const g)
    have h := ((hlog.div_const g).add
      ((hasDerivAt_id z).inv hzpos.ne')).sub
        (hasDerivAt_const z (1 / g))
    change HasDerivAt F _ z
    convert h using 1 <;> try rfl
    · funext s
      simp only [F, Function.comp_apply, id_eq, Pi.add_apply, Pi.sub_apply,
        Pi.inv_apply, one_div]
    · change (1 / g - 1 / z) / z =
        (z / g)⁻¹ * (1 / g) / g + -1 / z ^ 2 - 0
      field_simp [hzpos.ne', hg.ne']; ring
  have hint : IntervalIntegrable
      (fun z => (1 / g - 1 / z) / z)
      volume g v := by
    apply ContinuousOn.intervalIntegrable
    intro z hz
    rw [uIcc_of_le hgv] at hz
    have hzpos : 0 < z := hg.trans_le hz.1
    fun_prop (disch := positivity)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hzero : F g = 0 := by
    simp [F, hg.ne']
  simpa [i9toH, F, g, hzero] using h

private theorem i9to_w_primitive {u v : Real}
    (hu : 0 < u) (hv : 0 < v)
    (hgv : sectionSixFirstHighCentralSmallI9Gamma ≤ v) :
    (∫ w in sectionSixFirstHighCentralSmallI9Gamma..v,
      ∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
        sectionSixFirstHighCentralSmallI9TailKernel (((u, v), w), t)) =
      sectionSixFirstHighCentralSmallI9TailConstant / (u * v) * i9toH v := by
  have hg := sectionSixFirstHighCentralSmallI9_constants.1
  have hpoint : ∀ w ∈ uIcc
      sectionSixFirstHighCentralSmallI9Gamma v,
      (∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
        sectionSixFirstHighCentralSmallI9TailKernel (((u, v), w), t)) =
        sectionSixFirstHighCentralSmallI9TailConstant / (u * v) *
          ((1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / w) / w) := by
    intro w hw
    rw [uIcc_of_le hgv] at hw
    have hwpos : 0 < w := hg.trans_le hw.1
    rw [sectionSixFirstHighCentralSmallI9Tail_t_primitive hu hv hwpos hw.1]
    field_simp [hu.ne', hv.ne', hwpos.ne', hg.ne']
  calc
    _ = ∫ w in sectionSixFirstHighCentralSmallI9Gamma..v,
        sectionSixFirstHighCentralSmallI9TailConstant / (u * v) *
          ((1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / w) / w) := by
      apply intervalIntegral.integral_congr
      intro w hw
      exact hpoint w hw
    _ = sectionSixFirstHighCentralSmallI9TailConstant / (u * v) * i9toH v := by
      rw [intervalIntegral.integral_const_mul, i9to_H_integral hgv]

private theorem i9to_F_integral {V : Real}
    (hgv : sectionSixFirstHighCentralSmallI9Gamma ≤ V) :
    (∫ v in sectionSixFirstHighCentralSmallI9Gamma..V,
      i9toH v / v) =
      i9toF V := by
  let g : Real := sectionSixFirstHighCentralSmallI9Gamma
  let G : Real → Real := fun z =>
    Real.log (z / g) ^ 2 / (2 * g) + 1 / g - 1 / z -
      Real.log (z / g) / g
  have hg : 0 < g := sectionSixFirstHighCentralSmallI9_constants.1
  have hV : 0 < V := hg.trans_le hgv
  have hderiv : ∀ z ∈ uIcc g V,
      HasDerivAt G (i9toH z / z) z := by
    intro z hz
    rw [uIcc_of_le hgv] at hz
    have hzpos : 0 < z := hg.trans_le hz.1
    have hlog := (Real.hasDerivAt_log (div_pos hzpos hg).ne').comp z
      ((hasDerivAt_id z).div_const g)
    have hsq := hlog.mul hlog
    have hfirst := hsq.div_const (2 * g)
    have hneg := ((hasDerivAt_id z).inv hzpos.ne').neg
    have hlast := (hlog.div_const g).neg
    have hsum := hfirst.add (hasDerivAt_const z (1 / g))
    have hsum' := hsum.add hneg
    have hall := hsum'.add hlast
    change HasDerivAt G (i9toH z / z) z
    convert hall using 1 <;> try rfl
    · funext s
      simp [G, pow_two, sub_eq_add_neg]
    · simp [i9toH, Function.comp_apply, id_eq, one_div, sub_eq_add_neg]
      dsimp [g] at *
      field_simp [hzpos.ne', hg.ne']
      ring
  have hint : IntervalIntegrable (fun z => i9toH z / z) volume g V := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro z hz
    rw [uIcc_of_le hgv] at hz
    have hzpos : 0 < z := hg.trans_le hz.1
    have harg : ContinuousAt (fun s : Real => s / g) z := by
      exact continuousAt_id.div continuousAt_const (by positivity)
    have hlog : ContinuousAt (fun s : Real => Real.log (s / g)) z := by
      exact harg.log (div_pos hzpos hg).ne'
    have hinv : ContinuousAt (fun s : Real => 1 / s) z :=
      continuousAt_const.div continuousAt_id hzpos.ne'
    change ContinuousAt (fun s : Real => i9toH s / s) z
    exact (((hlog.div continuousAt_const (by positivity)).add
      hinv).sub continuousAt_const).div continuousAt_id hzpos.ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hzero : G g = 0 := by
    simp [G, hg.ne']
  simpa [G, i9toF, i9toH, g, hzero] using h

theorem sectionSixFirstHighCentralSmallI9TailOuterInner_eq_majorant
    {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralSmallI9CertificateOuter) :
    sectionSixFirstHighCentralSmallI9TailOuterInner u =
      sectionSixFirstHighCentralSmallI9TailOuterMajorant u := by
  have huPos : 0 < u :=
    (by
      have hbeta : 0 < sectionSixFirstHighCentralSmallI9Beta := by
        norm_num [sectionSixFirstHighCentralSmallI9Beta]
      exact hbeta.trans_le hu.1)
  have hV := sectionSixFirstHighCentralSmallI9_vupper_facts hu
  have hVLower : sectionSixFirstHighCentralSmallI9Gamma ≤
      sectionSixFirstHighCentralSmallI9VUpper u := hV.2.1
  have hVPos : 0 < sectionSixFirstHighCentralSmallI9VUpper u :=
    sectionSixFirstHighCentralSmallI9_constants.1.trans_le hVLower
  unfold sectionSixFirstHighCentralSmallI9TailOuterInner
  calc
    _ = ∫ v in sectionSixFirstHighCentralSmallI9Gamma..
          sectionSixFirstHighCentralSmallI9VUpper u,
        sectionSixFirstHighCentralSmallI9TailConstant / u *
          (i9toH v / v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hVLower] at hv
      have hvLower : sectionSixFirstHighCentralSmallI9Gamma ≤ v := hv.1
      have hvPos : 0 < v :=
        sectionSixFirstHighCentralSmallI9_constants.1.trans_le hvLower
      have hprim := i9to_w_primitive (u := u) (v := v)
        huPos hvPos hvLower
      calc
        _ = sectionSixFirstHighCentralSmallI9TailConstant / (u * v) *
              i9toH v := hprim
        _ = sectionSixFirstHighCentralSmallI9TailConstant / u *
              (i9toH v / v) := by
          field_simp [huPos.ne', hvPos.ne']
    _ = sectionSixFirstHighCentralSmallI9TailConstant / u *
          i9toF (sectionSixFirstHighCentralSmallI9VUpper u) := by
      rw [intervalIntegral.integral_const_mul, i9to_F_integral hVLower]
    _ = sectionSixFirstHighCentralSmallI9TailOuterMajorant u := by
      simp [i9toF, sectionSixFirstHighCentralSmallI9TailOuterMajorant,
        sectionSixFirstHighCentralSmallI9TailOuterF]

private theorem i9to_outer_integrable :
    IntegrableOn sectionSixFirstHighCentralSmallI9TailOuterInner
      sectionSixFirstHighCentralSmallI9CertificateOuter := by
  have hcont : ContinuousOn
      sectionSixFirstHighCentralSmallI9TailOuterMajorant
      (Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2 : Real)) := by
    unfold sectionSixFirstHighCentralSmallI9TailOuterMajorant
    apply ContinuousOn.mul
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro u hu
        have hb : 0 < sectionSixFirstHighCentralSmallI9Beta := by
          norm_num [sectionSixFirstHighCentralSmallI9Beta]
        exact ne_of_gt (hb.trans_le hu.1)
    · unfold sectionSixFirstHighCentralSmallI9TailOuterF
      have hgamma : 0 < sectionSixFirstHighCentralSmallI9Gamma :=
        sectionSixFirstHighCentralSmallI9_constants.1
      have hvpos : ∀ u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
          (1 / 2 : Real),
          0 < sectionSixFirstHighCentralSmallI9VUpper u := by
        intro u hu
        exact (sectionSixFirstHighCentralSmallI9_vupper_facts hu).1
      have hvne : ∀ u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
          (1 / 2 : Real),
          sectionSixFirstHighCentralSmallI9VUpper u ≠ 0 := by
        intro u hu
        exact ne_of_gt (hvpos u hu)
      have hargne : ∀ u ∈ Icc sectionSixFirstHighCentralSmallI9Beta
          (1 / 2 : Real),
          sectionSixFirstHighCentralSmallI9VUpper u /
            sectionSixFirstHighCentralSmallI9Gamma ≠ 0 := by
        intro u hu
        exact div_ne_zero (hvne u hu) (ne_of_gt hgamma)
      have hvcont : ContinuousOn sectionSixFirstHighCentralSmallI9VUpper
          (Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2 : Real)) := by
        unfold sectionSixFirstHighCentralSmallI9VUpper
        fun_prop
      have hratio : ContinuousOn (fun u : Real =>
          sectionSixFirstHighCentralSmallI9VUpper u /
            sectionSixFirstHighCentralSmallI9Gamma)
          (Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2 : Real)) := by
        exact hvcont.div continuousOn_const (fun _ _ => ne_of_gt hgamma)
      have hlog := hratio.log hargne
      fun_prop (disch := positivity)
  exact ContinuousOn.integrableOn_compact isCompact_Icc
    (hcont.congr (fun u hu =>
      sectionSixFirstHighCentralSmallI9TailOuterInner_eq_majorant hu))

theorem sectionSixFirstHighCentralSmallI9TailOuterIntegral_le_weightSum :
    (∫ u in sectionSixFirstHighCentralSmallI9CertificateOuter,
      sectionSixFirstHighCentralSmallI9TailOuterInner u) ≤
      ∑ index : Fin 32 × Fin 64,
        (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).weight := by
  let inner := sectionSixFirstHighCentralSmallI9TailOuterInner
  have houter : MeasurableSet
      sectionSixFirstHighCentralSmallI9CertificateOuter := by
    change MeasurableSet (Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2))
    exact measurableSet_Icc
  have hintegrable : IntegrableOn inner
      sectionSixFirstHighCentralSmallI9CertificateOuter := by
    exact i9to_outer_integrable
  calc
    _ ≤ ∑ index ∈ (Finset.univ : Finset (Fin 32 × Fin 64)),
        volume.real
            (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).region *
          (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).cellUpper :=
      setIntegral_le_finset_measureReal_mul_of_cover volume Finset.univ _ _
        inner _ houter
        (fun _ _ => measurableSet_Icc)
        (fun _ _ => isCompact_Icc.measure_ne_top)
        hintegrable
        (fun index _ => sectionSixFirstHighCentralSmallI9_cell_upper_nonneg index)
        sectionSixFirstHighCentralSmallI9_outer_covered
        (fun index _ u hu => by
          have hEq := sectionSixFirstHighCentralSmallI9TailOuterInner_eq_majorant
            (u := u) hu.1
          dsimp [inner]
          rw [hEq]
          exact sectionSixFirstHighCentralSmallI9_inner_le_cellUpper
            index hu.1 hu.2)
    _ = ∑ index : Fin 32 × Fin 64,
        (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).weight := by
      apply Finset.sum_congr rfl
      intro index _
      exact highCentralSmallCertificateCell_measure_mul_upper_eq_weight index

end
end PrimesRestrictedDigits
