import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarCertificateCells
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarFiberMajorants
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarCellAnalytic
/-! # SectionSixFirstHighFarCellBounds -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section
private theorem highFar_cell_grid_bounds (index : Fin 2 × Fin 160) :
    let cell := sectionSixFirstHighFarCertificateCell index
    cell.uLower ≤ cell.uUpper ∧ 0 < cell.uLower ∧
      cell.uUpper ≤ (1 / 2 : Real) := by
  exact highFarCertificateCell_bounds index

private theorem highFar_branch0_ratio_bounds (index : Fin 2 × Fin 160)
    (hbranch : index.1 = 0)
    {u : Real} (huOuter : u ∈ sectionSixFirstHighFarCertificateOuter index.1)
    (huCell : u ∈ (sectionSixFirstHighFarCertificateCell index).region) :
    1 ≤ (180001 / 500000 : Real) /
        (319999 / 500000 - u) ∧
      (180001 / 500000 : Real) / (319999 / 500000 - u) ≤
        (180001 / 500000 : Real) /
          (319999 / 500000 -
            (sectionSixFirstHighFarCertificateCell index).uUpper) := by
  rcases index with ⟨branch, i⟩
  simp only at hbranch
  fin_cases branch
  · change (212499 / 500000 : Real) ≤ u ∧ u ≤ 459997 / 1000000 at huOuter
    have hb := uniformRealGrid_bounds (n := 160)
      (a := (212499 : Real) / 500000) (b := 459997 / 1000000)
      (by norm_num) (by norm_num) i
    simp [SectionSixFirstHighFarCertificateCell.region,
      sectionSixFirstHighFarCertificateCell] at huCell ⊢
    have hden : 0 < (319999 / 500000 : Real) - u := by
      norm_num at huOuter ⊢
      linarith [huOuter.2]
    have hdenU : 0 < (319999 / 500000 : Real) -
        uniformRealGridUpper (212499 / 500000) (459997 / 1000000) i := by
      norm_num at hb ⊢
      linarith [hb.2.2]
    constructor
    · apply (le_div_iff₀ hden).2
      norm_num at huOuter ⊢
      linarith [huOuter.1]
    · apply (div_le_div_iff₀ hden hdenU).2
      nlinarith [huCell.2]
  · simp at hbranch

private theorem highFar_branch1_tail_factor_bounds (index : Fin 2 × Fin 160)
    (hbranch : index.1 = 1)
    {u : Real} (huOuter : u ∈ sectionSixFirstHighFarCertificateOuter index.1)
    (huCell : u ∈ (sectionSixFirstHighFarCertificateCell index).region) :
    (564663 / 1000000 : Real) *
          (1 + 2 * u - 3 * (319999 / 500000)) /
          (u * (319999 / 500000 - u) * (1 - u)) ≤
      (564663 / 1000000 : Real) *
          (1 + 2 * (sectionSixFirstHighFarCertificateCell index).uUpper -
            3 * (319999 / 500000)) /
          ((sectionSixFirstHighFarCertificateCell index).uLower *
            (319999 / 500000 -
              (sectionSixFirstHighFarCertificateCell index).uUpper) *
            (1 - (sectionSixFirstHighFarCertificateCell index).uUpper)) := by
  rcases index with ⟨branch, i⟩
  simp only at hbranch
  fin_cases branch
  · simp at hbranch
  · change (459997 / 1000000 : Real) ≤ u ∧ u ≤ 1 / 2 at huOuter
    have hb := uniformRealGrid_bounds (n := 160)
      (a := (459997 : Real) / 1000000) (b := 1 / 2)
      (by norm_num) (by norm_num) i
    simp [SectionSixFirstHighFarCertificateCell.region,
      sectionSixFirstHighFarCertificateCell] at huCell ⊢
    let uL := uniformRealGridLower (459997 / 1000000 : Real) (1 / 2) i
    let uU := uniformRealGridUpper (459997 / 1000000 : Real) (1 / 2) i
    have huL : uL ≤ u := by simpa [uL] using huCell.1
    have huU : u ≤ uU := by simpa [uU] using huCell.2
    have hUL : 0 < uL := by dsimp [uL]; norm_num at hb ⊢; linarith [hb.1]
    have hUA : 0 < (319999 / 500000 : Real) - uU := by
      dsimp [uU]
      norm_num at hb ⊢
      linarith [hb.2.2]
    have hUone : 0 < 1 - uU := by dsimp [uU]; norm_num at hb ⊢; linarith [hb.2.2]
    have hA : 0 ≤ (319999 / 500000 : Real) - uU := hUA.le
    have hOne : 0 ≤ 1 - uU := hUone.le
    have huPos : 0 < u := lt_of_lt_of_le hUL huL
    have hAcomp : (319999 / 500000 : Real) - uU ≤
        (319999 / 500000 : Real) - u := by linarith
    have hOnecomp : 1 - uU ≤ 1 - u := by linarith
    have hAu : 0 ≤ (319999 / 500000 : Real) - u := hA.trans hAcomp
    have huOne : 0 ≤ 1 - u := hOne.trans hOnecomp
    have hN : 0 ≤ 1 + 2 * u - 3 * (319999 / 500000) := by
      norm_num at huOuter ⊢
      linarith [huOuter.1]
    have hNU : 1 + 2 * u - 3 * (319999 / 500000) ≤
        1 + 2 * uU - 3 * (319999 / 500000) := by linarith
    have hD0 : 0 < uL * (319999 / 500000 - uU) * (1 - uU) :=
      mul_pos (mul_pos hUL hUA) hUone
    have hD : uL * (319999 / 500000 - uU) * (1 - uU) ≤
        u * (319999 / 500000 - u) * (1 - u) := by
      have h1 : uL * (319999 / 500000 - uU) ≤
          u * (319999 / 500000 - u) := by
        calc
          uL * (319999 / 500000 - uU) ≤
              u * (319999 / 500000 - uU) :=
            mul_le_mul_of_nonneg_right huL hA
          _ ≤ u * (319999 / 500000 - u) :=
            mul_le_mul_of_nonneg_left hAcomp huPos.le
      exact mul_le_mul h1 hOnecomp hOne (mul_nonneg huPos.le hAu)
    have hfrac :
        (1 + 2 * u - 3 * (319999 / 500000)) /
            (u * (319999 / 500000 - u) * (1 - u)) ≤
          (1 + 2 * uU - 3 * (319999 / 500000)) /
            (uL * (319999 / 500000 - uU) * (1 - uU)) := by
      calc
        _ ≤ (1 + 2 * uU - 3 * (319999 / 500000)) /
            (u * (319999 / 500000 - u) * (1 - u)) :=
          div_le_div_of_nonneg_right hNU
            (mul_nonneg (mul_nonneg huPos.le hAu) huOne)
        _ ≤ _ := div_le_div_of_nonneg_left
          (by linarith [hN, hNU]) hD0 hD
    calc
      _ = (564663 / 1000000 : Real) *
          ((1 + 2 * u - 3 * (319999 / 500000)) /
            (u * (319999 / 500000 - u) * (1 - u))) := by ring
      _ ≤ (564663 / 1000000 : Real) *
          ((1 + 2 * uU - 3 * (319999 / 500000)) /
            (uL * (319999 / 500000 - uU) * (1 - uU))) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = _ := by
        dsimp [uL, uU]
        ring_nf


theorem highFar_cell_upper_nonneg (index : Fin 2 × Fin 160) :
    0 ≤ (sectionSixFirstHighFarCertificateCell index).cellUpper := by
  rcases index with ⟨branch, i⟩
  fin_cases branch
  · simp [sectionSixFirstHighFarCertificateCell]
    have hb := uniformRealGrid_bounds (n := 160)
      (a := (212499 : Real) / 500000) (b := 459997 / 1000000)
      (by norm_num) (by norm_num) i
    have hr : 1 ≤ (180001 / 500000 : Real) /
        (319999 / 500000 - uniformRealGridUpper
          (212499 / 500000) (459997 / 1000000) i) := by
      norm_num at hb ⊢
      have hden : 0 < (319999 / 500000 : Real) -
          uniformRealGridUpper (212499 / 500000) (459997 / 1000000) i := by
        linarith [hb.2.2]
      apply (le_div_iff₀ hden).2
      linarith [hden]
    have hx : 0 ≤ ((180001 / 500000 : Real) /
        (319999 / 500000 - uniformRealGridUpper
          (212499 / 500000) (459997 / 1000000) i) - 1) /
        ((180001 / 500000 : Real) /
          (319999 / 500000 - uniformRealGridUpper
            (212499 / 500000) (459997 / 1000000) i) + 1) := by
      have hden : 0 < (180001 / 500000 : Real) /
          (319999 / 500000 - uniformRealGridUpper
            (212499 / 500000) (459997 / 1000000) i) + 1 := by
        linarith
      exact div_nonneg (by linarith) hden.le
    have hlow : 0 < uniformRealGridLower
        (212499 / 500000) (459997 / 1000000) i := by
      norm_num at hb ⊢
      linarith [hb.1]
    have hone : 0 < 1 - uniformRealGridLower
        (212499 / 500000) (459997 / 1000000) i := by
      norm_num at hb ⊢
      linarith [hb.2.1]
    have hpre : 0 ≤
        (1 - uniformRealGridLower
          (212499 / 500000) (459997 / 1000000) i)⁻¹ *
          (uniformRealGridLower (212499 / 500000)
            (459997 / 1000000) i)⁻¹ := by
      exact mul_nonneg (inv_nonneg.mpr hone.le) (inv_nonneg.mpr hlow.le)
    have hser : 0 ≤ cayleyLogSeriesUpper
        (((180001 / 500000 : Real) /
          (319999 / 500000 - uniformRealGridUpper
            (212499 / 500000) (459997 / 1000000) i) - 1) /
          ((180001 / 500000 : Real) /
              (319999 / 500000 - uniformRealGridUpper
              (212499 / 500000) (459997 / 1000000) i) + 1)) 5 := by
      have hratioPos : 0 ≤ (180001 / 500000 : Real) /
          (319999 / 500000 - uniformRealGridUpper
            (212499 / 500000) (459997 / 1000000) i) :=
        zero_le_one.trans hr
      have hratioDen : 0 < (180001 / 500000 : Real) /
          (319999 / 500000 - uniformRealGridUpper
            (212499 / 500000) (459997 / 1000000) i) + 1 := by linarith
      have hx : 0 ≤
          (((180001 / 500000 : Real) /
            (319999 / 500000 - uniformRealGridUpper
              (212499 / 500000) (459997 / 1000000) i) - 1) /
            ((180001 / 500000 : Real) /
              (319999 / 500000 - uniformRealGridUpper
                (212499 / 500000) (459997 / 1000000) i) + 1)) :=
        div_nonneg (by linarith) hratioDen.le
      have hxlt :
          (((180001 / 500000 : Real) /
            (319999 / 500000 - uniformRealGridUpper
              (212499 / 500000) (459997 / 1000000) i) - 1) /
            ((180001 / 500000 : Real) /
              (319999 / 500000 - uniformRealGridUpper
                (212499 / 500000) (459997 / 1000000) i) + 1)) < 1 := by
        rw [div_lt_one hratioDen]
        linarith
      have hden : 0 < 1 -
          (((180001 / 500000 : Real) /
            (319999 / 500000 - uniformRealGridUpper
              (212499 / 500000) (459997 / 1000000) i) - 1) /
            ((180001 / 500000 : Real) /
              (319999 / 500000 - uniformRealGridUpper
                (212499 / 500000) (459997 / 1000000) i) + 1)) ^ 2 := by
        nlinarith [sq_nonneg (((180001 / 500000 : Real) /
          (319999 / 500000 - uniformRealGridUpper
            (212499 / 500000) (459997 / 1000000) i) - 1) /
          ((180001 / 500000 : Real) /
            (319999 / 500000 - uniformRealGridUpper
              (212499 / 500000) (459997 / 1000000) i) + 1))]
      unfold cayleyLogSeriesUpper
      positivity
    exact mul_nonneg hpre hser
  · simp [sectionSixFirstHighFarCertificateCell]
    have hb := uniformRealGrid_bounds (n := 160)
      (a := (459997 : Real) / 1000000) (b := 1 / 2)
      (by norm_num) (by norm_num) i
    have htail : 0 ≤
        (564663 / 1000000 : Real) *
          (1 + 2 * uniformRealGridUpper
              (459997 / 1000000) (1 / 2) i - 3 * (319999 / 500000)) /
          (uniformRealGridLower (459997 / 1000000) (1 / 2) i *
            (319999 / 500000 - uniformRealGridUpper
              (459997 / 1000000) (1 / 2) i) *
            (1 - uniformRealGridUpper
              (459997 / 1000000) (1 / 2) i)) := by
      have hN : 0 ≤ 1 + 2 * uniformRealGridUpper
          (459997 / 1000000) (1 / 2) i - 3 * (319999 / 500000) := by
        norm_num at hb ⊢
        linarith [hb.2.1]
      have hden : 0 < uniformRealGridLower
          (459997 / 1000000) (1 / 2) i *
          (319999 / 500000 - uniformRealGridUpper
            (459997 / 1000000) (1 / 2) i) *
          (1 - uniformRealGridUpper
            (459997 / 1000000) (1 / 2) i) := by
        apply mul_pos
        · apply mul_pos
          · norm_num at hb ⊢
            linarith [hb.1]
          · norm_num at hb ⊢
            linarith [hb.2.2]
        · norm_num at hb ⊢
          linarith [hb.2.2]
      exact div_nonneg (mul_nonneg (by norm_num) hN) hden.le
    have hlow : 0 < uniformRealGridLower
        (459997 / 1000000) (1 / 2) i := by
      norm_num at hb ⊢
      linarith [hb.1]
    have hone : 0 < 1 - uniformRealGridLower
        (459997 / 1000000) (1 / 2) i := by
      norm_num at hb ⊢
      linarith [hb.2.1]
    have hpre : 0 ≤
        (1 - uniformRealGridLower (459997 / 1000000) (1 / 2) i)⁻¹ *
          (uniformRealGridLower (459997 / 1000000) (1 / 2) i)⁻¹ := by
      exact mul_nonneg (inv_nonneg.mpr hone.le) (inv_nonneg.mpr hlow.le)
    have hlog : 0 ≤ cayleyLogSeriesUpper (1 / 3 : Real) 5 := by
      unfold cayleyLogSeriesUpper
      positivity
    simpa [one_div] using (add_nonneg (mul_nonneg hpre hlog) htail)

private theorem highFar_prefactor_le_cell (index : Fin 2 × Fin 160)
    {u : Real} (huOuter : u ∈ sectionSixFirstHighFarCertificateOuter index.1)
    (huCell : u ∈ (sectionSixFirstHighFarCertificateCell index).region) :
    1 / (u * (1 - u)) ≤
      1 / ((sectionSixFirstHighFarCertificateCell index).uLower *
        (1 - (sectionSixFirstHighFarCertificateCell index).uLower)) := by
  let cell := sectionSixFirstHighFarCertificateCell index
  have hb : cell.uLower ≤ cell.uUpper ∧ 0 < cell.uLower ∧
      cell.uUpper ≤ (1 / 2 : Real) := by
    simpa [cell] using highFarCertificateCell_bounds index
  have huLowerPos : 0 < cell.uLower := hb.2.1
  have hcellOne : cell.uLower < 1 := by linarith [hb.2.2]
  have huHalf : u ≤ (1 / 2 : Real) := by
    rcases index with ⟨branch, i⟩
    fin_cases branch
    · change (212499 / 500000 : Real) ≤ u ∧ u ≤ 459997 / 1000000 at huOuter
      norm_num at huOuter ⊢
      linarith [huOuter.2]
    · change (459997 / 1000000 : Real) ≤ u ∧ u ≤ 1 / 2 at huOuter
      exact huOuter.2
  have hden : 0 < cell.uLower * (1 - cell.uLower) :=
    mul_pos huLowerPos (sub_pos.mpr hcellOne)
  apply one_div_le_one_div_of_le hden
  rcases huCell with ⟨huLow, huUp⟩
  have hdiff : 0 ≤ (u - cell.uLower) * (1 - u - cell.uLower) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr huLow
    · linarith [huHalf, huLowerPos]
  nlinarith

theorem highFar_inner_le_cellUpper (index : Fin 2 × Fin 160) {u : Real}
    (huOuter : u ∈ sectionSixFirstHighFarCertificateOuter index.1)
    (huCell : u ∈ (sectionSixFirstHighFarCertificateCell index).region) :
    (∫ v in sectionSixFirstHighFarCertificateLower u..
        sectionSixFirstHighFarCertificateUpper u,
      sectionSixFirstHighFarCertificateTransposedKernel (u, v)) ≤
      (sectionSixFirstHighFarCertificateCell index).cellUpper := by
  let cell := sectionSixFirstHighFarCertificateCell index
  have hpref := highFar_prefactor_le_cell index huOuter huCell
  rcases index with ⟨branch, i⟩
  fin_cases branch
  · have hratio := highFar_branch0_ratio_bounds (0, i) rfl huOuter huCell
    rw [sectionSixFirstHighFarCertificateBranch0_inner_eq huOuter]
    have hlog := highFar_log_ratio_le_endpoint hratio.1 hratio.2
    have hlogNonneg : 0 ≤ Real.log
        ((180001 / 500000 : Real) /
          (319999 / 500000 - u)) := Real.log_nonneg hratio.1
    have hcellOne : cell.uLower < 1 := by
      have hb : cell.uUpper ≤ (1 / 2 : Real) := by
        simpa [cell] using (highFarCertificateCell_bounds (0, i)).2.2
      have hcu : cell.uLower ≤ cell.uUpper := by
        simpa [cell] using (highFarCertificateCell_bounds (0, i)).1
      linarith
    have hcellLowerPos : 0 < cell.uLower := by
      simpa [cell] using (highFarCertificateCell_bounds (0, i)).2.1
    have hbound := mul_le_mul hpref hlog hlogNonneg
      (one_div_nonneg.mpr (mul_nonneg hcellLowerPos.le
        (sub_nonneg.mpr hcellOne.le)))
    norm_num [sectionSixFirstHighFarCertificateAlpha,
      sectionSixFirstHighFarCertificateA] at hbound
    have hAlpha : sectionSixFirstHighFarCertificateAlpha =
        (180001 / 500000 : Real) := by rfl
    have hA : sectionSixFirstHighFarCertificateA =
        (319999 / 500000 : Real) := by rfl
    rw [hAlpha, hA]
    simpa [cell, sectionSixFirstHighFarCertificateCell,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hbound
  · have hu1 : u ∈ Icc (459997 / 1000000 : Real) (1 / 2) := by
      change (459997 / 1000000 : Real) ≤ u ∧ u ≤ 1 / 2 at huOuter
      exact huOuter
    have ho := highFar_outer_facts 1 huOuter
    have hfull := highFar_inner_intervalIntegrable 1 huOuter
    let l : Real := sectionSixFirstHighFarCertificateLower u
    let m : Real := (1 - u) / 3
    let h : Real := sectionSixFirstHighFarCertificateUpper u
    have hlm : l ≤ m := by
      change (319999 / 500000 : Real) - u ≤ (1 - u) / 3
      norm_num at hu1 ⊢
      linarith [hu1.1]
    have hmh : m ≤ h := by
      change (1 - u) / 3 ≤ (1 - u) / 2
      have hB : 0 ≤ 1 - u := by linarith [hu1.2]
      nlinarith
    have hleft : IntervalIntegrable
        (fun v => sectionSixFirstHighFarCertificateTransposedKernel (u, v))
        volume l m := by
      apply hfull.mono_set
      rw [uIcc_of_le ho.2.2.1]
      rw [uIcc_of_le hlm]
      exact Icc_subset_Icc le_rfl (by linarith [hlm])
    have hright : IntervalIntegrable
        (fun v => sectionSixFirstHighFarCertificateTransposedKernel (u, v))
        volume m h := by
      apply hfull.mono_set
      rw [uIcc_of_le ho.2.2.1]
      rw [uIcc_of_le hmh]
      exact Icc_subset_Icc (by linarith [hmh]) le_rfl
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    have htail := sectionSixFirstHighFarCertificateTail_le huOuter
    have hstrip := sectionSixFirstHighFarCertificateUpperStrip_eq hu1
    have htailEq :
        sectionSixFirstHighFarCertificateEnvelope / u *
            (1 / l - 3 / (1 - u)) =
          (564663 / 1000000 : Real) *
            (1 + 2 * u - 3 * (319999 / 500000)) /
              (u * l * (1 - u)) := by
      change (564663 / 1000000 : Real) / u *
          (1 / ((319999 / 500000 : Real) - u) - 3 / (1 - u)) =
        (564663 / 1000000 : Real) *
          (1 + 2 * u - 3 * (319999 / 500000)) /
            (u * ((319999 / 500000 : Real) - u) * (1 - u))
      have hlPos : 0 < (319999 / 500000 : Real) - u := by
        norm_num at hu1 ⊢
        linarith [hu1.2]
      have hscaled : (319999 : Real) - u * 500000 ≠ 0 := by
        nlinarith [hlPos]
      field_simp [ho.1.ne', hlPos.ne', (by linarith [hu1.2] :
        (1 : Real) - u ≠ 0), hscaled]
      ring_nf
    have htail' := highFar_branch1_tail_factor_bounds (1, i) rfl huOuter huCell
    have hstrip' :
        Real.log 2 / (u * (1 - u)) ≤
          1 / (cell.uLower * (1 - cell.uLower)) *
            cayleyLogSeriesUpper (1 / 3 : Real) 5 := by
      have hlog2 := highFar_log_two_upper
      have hlog2Nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hcellBounds : cell.uLower ≤ cell.uUpper ∧ 0 < cell.uLower ∧
          cell.uUpper ≤ (1 / 2 : Real) := by
        simpa [cell] using highFarCertificateCell_bounds (1, i)
      have hcellPrefNonneg : 0 ≤
          1 / (cell.uLower * (1 - cell.uLower)) :=
        one_div_nonneg.mpr (mul_nonneg hcellBounds.2.1.le
          (by linarith [hcellBounds.2.2]))
      have hprod := mul_le_mul hpref hlog2 hlog2Nonneg hcellPrefNonneg
      calc
        _ = 1 / (u * (1 - u)) * Real.log 2 := by ring
        _ ≤ 1 / (cell.uLower * (1 - cell.uLower)) *
            cayleyLogSeriesUpper (1 / 3 : Real) 5 := hprod
        _ = _ := by ring
    have htailBound :
          (∫ v in l..m,
          sectionSixFirstHighFarCertificateTransposedKernel (u, v)) ≤
          (564663 / 1000000 : Real) *
            (1 + 2 * cell.uUpper - 3 * (319999 / 500000)) /
              (cell.uLower *
                (319999 / 500000 - cell.uUpper) *
                (1 - cell.uUpper)) := by
      calc
        _ ≤ sectionSixFirstHighFarCertificateEnvelope / u *
            (1 / l - 3 / (1 - u)) := by
          simpa [l, m] using htail
        _ = (564663 / 1000000 : Real) *
            (1 + 2 * u - 3 * (319999 / 500000)) /
              (u * l * (1 - u)) := htailEq
        _ ≤ _ := by
          have hlEq : l = (319999 / 500000 : Real) - u := by
            rfl
          rw [hlEq]
          exact htail'
    have hstripBound :
        (∫ v in m..h,
          sectionSixFirstHighFarCertificateTransposedKernel (u, v)) ≤
          1 / (cell.uLower * (1 - cell.uLower)) *
            cayleyLogSeriesUpper (1 / 3 : Real) 5 := by
      calc
        _ = Real.log 2 / (u * (1 - u)) := by simpa [m, h] using hstrip
        _ ≤ _ := hstrip'
    calc
      _ = (∫ v in l..m,
          sectionSixFirstHighFarCertificateTransposedKernel (u, v)) +
          ∫ v in m..h,
            sectionSixFirstHighFarCertificateTransposedKernel (u, v) := hadd.symm
      _ ≤ (564663 / 1000000 : Real) *
            (1 + 2 * cell.uUpper - 3 * (319999 / 500000)) /
          (cell.uLower *
                (319999 / 500000 - cell.uUpper) *
                (1 - cell.uUpper)) +
          1 / (cell.uLower * (1 - cell.uLower)) *
            cayleyLogSeriesUpper (1 / 3 : Real) 5 :=
        add_le_add htailBound hstripBound
      _ = cell.cellUpper := by
        simp [cell, sectionSixFirstHighFarCertificateCell]
        ring


end
end PrimesRestrictedDigits
