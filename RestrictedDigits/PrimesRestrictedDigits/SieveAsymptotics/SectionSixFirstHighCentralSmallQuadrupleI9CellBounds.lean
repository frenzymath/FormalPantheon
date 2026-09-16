import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateCells
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralSmallQuadrupleI9CellBounds -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-! The closed outer interval and the pointwise payload bridge for I9. -/

def sectionSixFirstHighCentralSmallI9CertificateOuter : Set Real :=
  Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2)

private theorem i9_certificate_outer_facts {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralSmallI9CertificateOuter) :
    0 < u ∧ sectionSixFirstHighCentralSmallI9Gamma ≤
      sectionSixFirstHighCentralSmallI9VUpper u ∧
      sectionSixFirstHighCentralSmallI9VUpper u ≤ (1 / 2 : Real) := by
  change u ∈ Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2) at hu
  have h := sectionSixFirstHighCentralSmallI9_vupper_facts hu
  exact ⟨by
    have hbeta : 0 < sectionSixFirstHighCentralSmallI9Beta := by
      norm_num [sectionSixFirstHighCentralSmallI9Beta]
    exact hbeta.trans_le hu.1,
    h.2.1, h.2.2⟩

theorem sectionSixFirstHighCentralSmallI9_outer_covered :
    sectionSixFirstHighCentralSmallI9CertificateOuter ⊆
      ⋃ index ∈ (Finset.univ : Finset (Fin 32 × Fin 64)),
        (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).region := by
  intro u hu
  change u ∈ Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2) at hu
  have hAB : sectionSixFirstHighCentralSmallI9Beta < (1 / 2 : Real) := by
    norm_num [sectionSixFirstHighCentralSmallI9Beta]
  rcases exists_uniformRealGrid_cell
      (a := sectionSixFirstHighCentralSmallI9Beta) (b := (1 / 2 : Real))
      (n := 2048) (x := u) (by norm_num) hAB hu.1 hu.2 with ⟨flat, hflat⟩
  let index : Fin 32 × Fin 64 := finProdFinEquiv.symm flat
  refine Set.mem_iUnion.2 ⟨index, Set.mem_iUnion.2 ⟨Finset.mem_univ index, ?_⟩⟩
  have hindex : finProdFinEquiv index = flat := by
    exact (@finProdFinEquiv 32 64).apply_symm_apply flat
  change uniformRealGridLower
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta (1 / 2)
      (finProdFinEquiv index) ≤ u ∧
    u ≤ uniformRealGridUpper
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta (1 / 2)
      (finProdFinEquiv index)
  rw [hindex]
  simpa [sectionSixFirstHighCentralSmallI9Beta,
    sectionSixFirstHighCentralSmallQuadrupleCertificateBeta] using hflat

private theorem i9_cell_grid_bounds (index : Fin 32 × Fin 64) :
    let cell := sectionSixFirstHighCentralSmallQuadrupleCertificateCell index
    cell.uLower ≤ cell.uUpper ∧ 0 < cell.uLower ∧
      cell.uUpper ≤ (1 / 2 : Real) := by
  exact highCentralSmallCertificateCell_bounds index

private theorem i9_log_lower_le_log {q : Real} (hq : 1 ≤ q) :
    sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower q ≤ Real.log q := by
  let x : Real := (q - 1) / (q + 1)
  have hq1 : 0 < q + 1 := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (by linarith) hq1.le
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one hq1]
    linarith
  have hratio : (1 + x) / (1 - x) = q := by
    dsimp [x]
    field_simp
    ring
  have hlow := Real.sum_range_le_log_div hx0 hx1 10
  change 2 * ∑ i ∈ Finset.range 10,
      x ^ (2 * i + 1) / (2 * i + 1) ≤ Real.log q
  calc
    _ ≤ Real.log ((1 + x) / (1 - x)) := by linarith
    _ = Real.log q := by rw [hratio]

private theorem i9_log_upper_log {q : Real} (hq : 1 ≤ q) :
    Real.log q ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper q := by
  let x : Real := (q - 1) / (q + 1)
  have hq1 : 0 < q + 1 := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (by linarith) hq1.le
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one hq1]
    linarith
  have hratio : (1 + x) / (1 - x) = q := by
    dsimp [x]
    field_simp
    ring
  have hupp := log_cayley_le_cayleyLogSeriesUpper hx0 hx1 10
  change Real.log q ≤ cayleyLogSeriesUpper x 10
  rw [← hratio]
  exact hupp

private def i9FiberF (z : Real) : Real :=
  Real.log (z / sectionSixFirstHighCentralSmallI9Gamma) ^ 2 /
      (2 * sectionSixFirstHighCentralSmallI9Gamma) +
    1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / z -
      Real.log (z / sectionSixFirstHighCentralSmallI9Gamma) /
        sectionSixFirstHighCentralSmallI9Gamma

private theorem i9FiberF_mono {x y : Real}
    (hx : sectionSixFirstHighCentralSmallI9Gamma ≤ x)
    (hxy : x ≤ y) : i9FiberF x ≤ i9FiberF y := by
  let g : Real := sectionSixFirstHighCentralSmallI9Gamma
  let f : Real → Real := fun z => i9FiberF z
  have hg : 0 < g := by
    exact sectionSixFirstHighCentralSmallI9_constants.1
  have hcont : ContinuousOn f (Icc x y) := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hg (hx.trans hz.1)
    have hratio : 0 < z / g := div_pos hzpos hg
    have harg : ContinuousAt (fun s : Real => s / g) z := by
      exact continuousAt_id.div continuousAt_const (by positivity)
    have hlog : ContinuousAt (fun s : Real => Real.log (s / g)) z := by
      exact harg.log hratio.ne'
    have hinv : ContinuousAt (fun s : Real => 1 / s) z :=
      continuousAt_const.div continuousAt_id hzpos.ne'
    change ContinuousAt (fun s : Real =>
      Real.log (s / g) ^ 2 / (2 * g) + 1 / g - 1 / s -
        Real.log (s / g) / g) z
    exact (((hlog.pow 2).div continuousAt_const (by positivity)).add
      continuousAt_const).sub hinv |>.sub
        (hlog.div continuousAt_const (by positivity))
  have hderiv : ∀ z ∈ interior (Icc x y),
      HasDerivWithinAt f
        ((Real.log (z / g) - 1 + g / z) / (g * z))
        (interior (Icc x y)) z := by
    intro z hz
    have hzmem : z ∈ Icc x y := interior_subset hz
    have hzpos : 0 < z := lt_of_lt_of_le hg (hx.trans hzmem.1)
    have hratio : 0 < z / g := div_pos hzpos hg
    have harg : HasDerivAt (fun s : Real => s / g) (1 / g) z := by
      simpa only [id_eq] using (hasDerivAt_id z).div_const g
    have hlog : HasDerivAt (fun s : Real => Real.log (s / g))
        ((z / g)⁻¹ * (1 / g)) z := by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_log hratio.ne').comp z harg
    have hsq := hlog.mul hlog
    have hfirst := hsq.div_const (2 * g)
    have hneg := ((hasDerivAt_id z).inv hzpos.ne').neg
    have hlast := (hlog.div_const g).neg
    have hsum := hfirst.add (hasDerivAt_const z (1 / g))
    have hsum' := hsum.add hneg
    have hall := hsum'.add hlast
    change HasDerivWithinAt i9FiberF
      ((Real.log (z / g) - 1 + g / z) / (g * z))
      (interior (Icc x y)) z
    convert hall.hasDerivWithinAt using 1
    all_goals try rfl
    all_goals try (funext s; dsimp [i9FiberF]; ring)
    all_goals (simp [id_eq]; field_simp; ring_nf)
  have hderiv_nonneg : ∀ z ∈ interior (Icc x y),
      0 ≤ (Real.log (z / g) - 1 + g / z) / (g * z) := by
    intro z hz
    have hzmem : z ∈ Icc x y := interior_subset hz
    have hzpos : 0 < z := lt_of_lt_of_le hg (hx.trans hzmem.1)
    have hratio : 0 < z / g := div_pos hzpos hg
    have hloginv := Real.log_le_sub_one_of_pos (inv_pos.mpr hratio)
    have hlogrel : 1 - g / z ≤ Real.log (z / g) := by
      have hloginv' : -Real.log (z / g) ≤ g / z - 1 := by
        calc
          -Real.log (z / g) = Real.log ((z / g)⁻¹) := by
            rw [Real.log_inv]
          _ ≤ (z / g)⁻¹ - 1 := hloginv
          _ = g / z - 1 := by field_simp [hzpos.ne', hg.ne']
      linarith
    have hnum : 0 ≤ Real.log (z / g) - 1 + g / z := by linarith
    exact div_nonneg hnum (by positivity)
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
    hcont hderiv hderiv_nonneg
  have := hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  simpa [f, i9FiberF] using this

theorem sectionSixFirstHighCentralSmallI9_tail_outer_majorant_le_cellUpper
    (index : Fin 32 × Fin 64) {u : Real}
    (huOuter : u ∈ sectionSixFirstHighCentralSmallI9CertificateOuter)
    (huCell : u ∈
      (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).region) :
    sectionSixFirstHighCentralSmallI9TailOuterMajorant u ≤
      (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).cellUpper := by
  let cell := sectionSixFirstHighCentralSmallQuadrupleCertificateCell index
  have hb := i9_cell_grid_bounds index
  change u ∈ Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2) at huOuter
  change cell.uLower ≤ u ∧ u ≤ cell.uUpper at huCell
  have huPos : 0 < u := by
    have hbeta : 0 < sectionSixFirstHighCentralSmallI9Beta := by
      norm_num [sectionSixFirstHighCentralSmallI9Beta]
    exact hbeta.trans_le huOuter.1
  have hLPos : 0 < cell.uLower := hb.2.1
  have hV := (sectionSixFirstHighCentralSmallI9_vupper_facts huOuter)
  have hVcell : sectionSixFirstHighCentralSmallI9VUpper u ≤
      (sectionSixFirstHighCentralSmallI9CarrierCap - cell.uLower) / 2 := by
    dsimp [sectionSixFirstHighCentralSmallI9VUpper]
    linarith
  have hF := i9FiberF_mono hV.2.1 hVcell
  have hlogL := i9_log_lower_le_log (q :=
    (sectionSixFirstHighCentralSmallI9CarrierCap - cell.uLower) / 2 /
      sectionSixFirstHighCentralSmallI9Gamma) (by
        have := hV.2.1
        dsimp [sectionSixFirstHighCentralSmallI9VUpper] at this ⊢
        have hg := sectionSixFirstHighCentralSmallI9_constants.1
        apply (le_div_iff₀ hg).2
        linarith)
  have hlogU := i9_log_upper_log (q :=
    (sectionSixFirstHighCentralSmallI9CarrierCap - cell.uLower) / 2 /
      sectionSixFirstHighCentralSmallI9Gamma) (by
        have := hV.2.1
        dsimp [sectionSixFirstHighCentralSmallI9VUpper] at this ⊢
        have hg := sectionSixFirstHighCentralSmallI9_constants.1
        apply (le_div_iff₀ hg).2
        linarith)
  have hlog0 : 0 ≤ Real.log ((sectionSixFirstHighCentralSmallI9CarrierCap -
      cell.uLower) / 2 / sectionSixFirstHighCentralSmallI9Gamma) :=
    Real.log_nonneg (by
      have := hV.2.1
      dsimp [sectionSixFirstHighCentralSmallI9VUpper] at this ⊢
      have hg := sectionSixFirstHighCentralSmallI9_constants.1
      exact (le_div_iff₀ hg).2 (by linarith))
  have hupper0 : 0 ≤ sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper
      ((sectionSixFirstHighCentralSmallI9CarrierCap - cell.uLower) / 2 /
        sectionSixFirstHighCentralSmallI9Gamma) := hlog0.trans hlogU
  have hcell : cell.cellUpper =
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail *
        (sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper
            ((sectionSixFirstHighCentralSmallI9CarrierCap - cell.uLower) / 2 /
              sectionSixFirstHighCentralSmallI9Gamma) ^ 2 /
          (2 * sectionSixFirstHighCentralSmallQuadrupleCertificateGap) +
        1 / sectionSixFirstHighCentralSmallQuadrupleCertificateGap -
        1 / ((sectionSixFirstHighCentralSmallI9CarrierCap - cell.uLower) / 2) -
        sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower
            ((sectionSixFirstHighCentralSmallI9CarrierCap - cell.uLower) / 2 /
              sectionSixFirstHighCentralSmallI9Gamma) /
          sectionSixFirstHighCentralSmallQuadrupleCertificateGap) / cell.uLower := by
    simp [cell, sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      sectionSixFirstHighCentralSmallI9CarrierCap,
      sectionSixFirstHighCentralSmallI9Gamma,
      sectionSixFirstHighCentralSmallQuadrupleCertificateC,
      sectionSixFirstHighCentralSmallQuadrupleCertificateGap]
  let endpoint : Real :=
    (sectionSixFirstHighCentralSmallI9CarrierCap - cell.uLower) / 2
  let ratio : Real := endpoint / sectionSixFirstHighCentralSmallI9Gamma
  have hratio0 : 0 ≤ Real.log ratio := by
    dsimp [ratio, endpoint]
    exact hlog0
  have hsq : Real.log ratio ^ 2 ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper ratio ^ 2 := by
    exact (sq_le_sq₀ hratio0 hupper0).2 hlogU
  have hlogDiv :
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower ratio /
          sectionSixFirstHighCentralSmallI9Gamma ≤
        Real.log ratio / sectionSixFirstHighCentralSmallI9Gamma :=
    div_le_div_of_nonneg_right hlogL
      (le_of_lt sectionSixFirstHighCentralSmallI9_constants.1)
  have hFendpoint : i9FiberF endpoint ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper ratio ^ 2 /
          (2 * sectionSixFirstHighCentralSmallI9Gamma) +
        1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / endpoint -
          sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower ratio /
            sectionSixFirstHighCentralSmallI9Gamma := by
    dsimp [i9FiberF, ratio] at *
    have hsquare := div_le_div_of_nonneg_right hsq
      (by
        have hg := sectionSixFirstHighCentralSmallI9_constants.1
        exact mul_nonneg (by norm_num) hg.le :
          0 ≤ 2 * sectionSixFirstHighCentralSmallI9Gamma)
    linarith [hsquare, hlogDiv]
  have hFbound : sectionSixFirstHighCentralSmallI9TailOuterF u ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper ratio ^ 2 /
          (2 * sectionSixFirstHighCentralSmallI9Gamma) +
        1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / endpoint -
          sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower ratio /
            sectionSixFirstHighCentralSmallI9Gamma := by
    have hchain := hF.trans hFendpoint
    simpa [i9FiberF, sectionSixFirstHighCentralSmallI9TailOuterF,
      endpoint, ratio] using hchain
  have hpref : sectionSixFirstHighCentralSmallI9TailConstant / u ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail / cell.uLower := by
    have hD2 : sectionSixFirstHighCentralSmallI9TailConstant =
        sectionSixFirstHighCentralSmallQuadrupleCertificateTail := by
      norm_num [sectionSixFirstHighCentralSmallI9TailConstant,
        sectionSixFirstHighCentralSmallQuadrupleCertificateTail]
    rw [hD2]
    apply (div_le_div_iff₀ huPos hLPos).2
    have htail : 0 ≤
        sectionSixFirstHighCentralSmallQuadrupleCertificateTail := by
      norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateTail]
    exact mul_le_mul_of_nonneg_left huCell.1 htail
  have hF0 : 0 ≤ sectionSixFirstHighCentralSmallI9TailOuterF u := by
    -- F is monotone from the zero endpoint F(gamma)=0.
    have := i9FiberF_mono (x := sectionSixFirstHighCentralSmallI9Gamma)
      (y := sectionSixFirstHighCentralSmallI9VUpper u)
      (le_rfl) hV.2.1
    simpa [i9FiberF, sectionSixFirstHighCentralSmallI9TailOuterF] using this
  rw [hcell]
  have hFbound0 : 0 ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper ratio ^ 2 /
          (2 * sectionSixFirstHighCentralSmallI9Gamma) +
        1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / endpoint -
          sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower ratio /
            sectionSixFirstHighCentralSmallI9Gamma :=
    le_trans hF0 hFbound
  have htail : 0 ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail := by
    norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateTail]
  have hpref0 : 0 ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateTail / cell.uLower := by
    exact div_nonneg htail hLPos.le
  exact le_trans (mul_le_mul hpref hFbound hF0 hpref0) (by
    dsimp [endpoint, ratio]
    apply le_of_eq
    simp only [sectionSixFirstHighCentralSmallQuadrupleCertificateGap,
      sectionSixFirstHighCentralSmallI9Gamma,
      sectionSixFirstHighCentralSmallI9CarrierCap]
    field_simp)

theorem sectionSixFirstHighCentralSmallI9_cell_upper_nonneg
    (index : Fin 32 × Fin 64) :
    0 ≤ (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).cellUpper := by
  let cell := sectionSixFirstHighCentralSmallQuadrupleCertificateCell index
  have hb := i9_cell_grid_bounds index
  have hgrid := uniformRealGrid_bounds (n := 2048)
      (a := sectionSixFirstHighCentralSmallQuadrupleCertificateBeta)
      (b := (1 / 2 : Real)) (by norm_num)
      (by norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateBeta])
      (finProdFinEquiv index)
  have hbeta : sectionSixFirstHighCentralSmallI9Beta ≤ cell.uLower := by
    change (212499999 / 500000000 : Real) ≤ cell.uLower
    simpa [cell, sectionSixFirstHighCentralSmallQuadrupleCertificateCell,
      sectionSixFirstHighCentralSmallQuadrupleCertificateBeta] using hgrid.1
  have houter : cell.uLower ∈
      sectionSixFirstHighCentralSmallI9CertificateOuter := by
    change sectionSixFirstHighCentralSmallI9Beta ≤ cell.uLower ∧
      cell.uLower ≤ (1 / 2 : Real)
    exact ⟨hbeta, hb.1.trans hb.2.2⟩
  have hcellmem : cell.uLower ∈ cell.region := by
    change cell.uLower ≤ cell.uLower ∧ cell.uLower ≤ cell.uUpper
    exact ⟨le_rfl, hb.1⟩
  have hmajor := sectionSixFirstHighCentralSmallI9_tail_outer_majorant_le_cellUpper
    index houter hcellmem
  have hFzero : 0 ≤ sectionSixFirstHighCentralSmallI9TailOuterF cell.uLower := by
    have hv := sectionSixFirstHighCentralSmallI9_vupper_facts houter
    have hm := i9FiberF_mono (x := sectionSixFirstHighCentralSmallI9Gamma)
      (y := sectionSixFirstHighCentralSmallI9VUpper cell.uLower) le_rfl hv.2.1
    have hz : i9FiberF sectionSixFirstHighCentralSmallI9Gamma = 0 := by
      norm_num [i9FiberF, sectionSixFirstHighCentralSmallI9Gamma]
    have hm0 : 0 ≤ i9FiberF
        (sectionSixFirstHighCentralSmallI9VUpper cell.uLower) := by
      simpa [hz] using hm
    simpa [i9FiberF, sectionSixFirstHighCentralSmallI9TailOuterF] using hm0
  have hmajor0 : 0 ≤
      sectionSixFirstHighCentralSmallI9TailOuterMajorant cell.uLower := by
    unfold sectionSixFirstHighCentralSmallI9TailOuterMajorant
    exact mul_nonneg
      (div_nonneg (by norm_num [sectionSixFirstHighCentralSmallI9TailConstant])
        hb.2.1.le) hFzero
  exact hmajor0.trans hmajor

theorem sectionSixFirstHighCentralSmallI9_inner_le_cellUpper
    (index : Fin 32 × Fin 64) {u : Real}
    (huOuter : u ∈ sectionSixFirstHighCentralSmallI9CertificateOuter)
    (huCell : u ∈
      (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).region) :
    sectionSixFirstHighCentralSmallI9TailOuterMajorant u ≤
      (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).cellUpper :=
  sectionSixFirstHighCentralSmallI9_tail_outer_majorant_le_cellUpper index huOuter huCell

end
end PrimesRestrictedDigits
