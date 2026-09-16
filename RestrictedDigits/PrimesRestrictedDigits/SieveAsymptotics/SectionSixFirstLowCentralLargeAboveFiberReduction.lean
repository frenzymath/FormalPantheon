import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabInverseFiberIntegral
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveRegions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Physical fiber reduction for the low central-large above band

This file covers Maynard's closed `I_4` carrier by five physical cells, evaluates the
inverse-only Buchstab fiber exactly, and expresses the result as the sum of reduced
two-dimensional cell integrals.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.11).
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def aboveDelta : Real := 1 / 1000000
private def aboveAlpha : Real := 180001 / 500000
private def aboveBeta : Real := 212499 / 500000
private def aboveGamma : Real := 287501 / 500000
private def aboveSigma : Real := 319999 / 500000
private def aboveD : Real := 37501 / 250000
private def aboveH : Real := 43 / 200
private def aboveUZero : Real := 470003 / 1500000

private def aboveIsA (cell : Fin 5) : Prop := cell.val < 2

private instance (cell : Fin 5) : Decidable (aboveIsA cell) :=
  inferInstanceAs (Decidable (cell.val < 2))

private def aboveULower (cell : Fin 5) : Real :=
  match cell.val with
  | 0 => aboveH
  | 1 => aboveUZero
  | 2 => aboveSigma / 3
  | 3 => aboveH
  | _ => 1 / 4

private def aboveUUpper (cell : Fin 5) : Real :=
  match cell.val with
  | 0 => aboveUZero
  | 1 => aboveAlpha
  | 2 => aboveH
  | 3 => 1 / 4
  | _ => aboveAlpha

private def aboveVLower (cell : Fin 5) (u : Real) : Real :=
  match cell.val with
  | 0 => (aboveSigma - u) / 2
  | 1 => u - aboveD
  | 2 => (aboveSigma - u) / 2
  | _ => aboveBeta / 2

private def aboveVUpper (cell : Fin 5) (u : Real) : Real :=
  match cell.val with
  | 0 => aboveBeta / 2
  | 1 => aboveBeta / 2
  | 2 => u
  | 3 => u
  | _ => (1 - u) / 3

private def aboveOuter (cell : Fin 5) : Set Real :=
  Icc (aboveULower cell) (aboveUUpper cell)

private def aboveUVFiber (cell : Fin 5) : Set (Real × Real) :=
  closedIccFiberCell (aboveOuter cell) (aboveVLower cell) (aboveVUpper cell)

private def aboveWLower (cell : Fin 5) (z : Real × Real) : Real :=
  if aboveIsA cell then aboveBeta - z.2 else z.2

private def aboveWUpper (z : Real × Real) : Real :=
  (1 - z.1 - z.2) / 2

private def aboveTripleFiber (cell : Fin 5) : Set ((Real × Real) × Real) :=
  closedIccFiberCell (aboveUVFiber cell) (aboveWLower cell) aboveWUpper

private noncomputable def aboveRatio (cell : Fin 5) (u v : Real) : Real :=
  if aboveIsA cell then
    (aboveGamma - u) / (aboveBeta - v)
  else
    (1 - u - 2 * v) / v

private noncomputable def aboveMajorant (cell : Fin 5) (u v : Real) : Real :=
  Real.log (aboveRatio cell u v) / (u * v * (1 - u - v))

private theorem above_mem_iUnion (cell : Fin 5)
    {z : ((Real × Real) × Real)} (hz : z ∈ aboveTripleFiber cell) :
    z ∈ ⋃ i ∈ (Finset.univ : Finset (Fin 5)), aboveTripleFiber i := by
  exact Set.mem_iUnion.2
    ⟨cell, Set.mem_iUnion.2 ⟨Finset.mem_univ cell, hz⟩⟩

private theorem aboveUVFiber_facts (cell : Fin 5) {u v : Real}
    (hz : (u, v) ∈ aboveUVFiber cell) :
    0 < u ∧ 0 < v ∧
      1 / 10 ≤ u ∧ 1 / 10 ≤ v ∧
      u ≤ 1 / 2 ∧ v ≤ 1 / 2 ∧
      1 / 10 ≤ aboveWLower cell (u, v) ∧
      aboveWLower cell (u, v) ≤ aboveWUpper (u, v) ∧
      2 * aboveWUpper (u, v) ≤ 1 - u - v ∧
      1 - u - v ≤ 3 * aboveWLower cell (u, v) := by
  fin_cases cell <;>
    change u ∈ Icc _ _ ∧ v ∈ Icc _ _ at hz <;>
    rcases hz with ⟨hu, hv⟩ <;>
    norm_num [aboveULower, aboveUUpper, aboveVLower, aboveVUpper,
      aboveWLower, aboveWUpper, aboveIsA, aboveAlpha, aboveBeta,
      aboveSigma, aboveD, aboveH, aboveUZero] at hu hv ⊢ <;>
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
      by nlinarith, by nlinarith, by nlinarith, by nlinarith,
      by nlinarith, by nlinarith⟩

private theorem aboveUVFiber_ordered (cell : Fin 5) {u : Real}
    (hu : u ∈ aboveOuter cell) :
    aboveVLower cell u ≤ aboveVUpper cell u := by
  fin_cases cell <;>
    norm_num [aboveOuter, aboveULower, aboveUUpper, aboveVLower,
      aboveVUpper, aboveAlpha, aboveBeta, aboveSigma, aboveD, aboveH,
      aboveUZero] at hu ⊢ <;>
    exact (by linarith)

private theorem aboveVLower_measurable (cell : Fin 5) :
    Measurable (aboveVLower cell) := by
  fin_cases cell
  · change Measurable (fun u : Real => (aboveSigma - u) / 2); fun_prop
  · change Measurable (fun u : Real => u - aboveD); fun_prop
  · change Measurable (fun u : Real => (aboveSigma - u) / 2); fun_prop
  · change Measurable (fun _ : Real => aboveBeta / 2); fun_prop
  · change Measurable (fun _ : Real => aboveBeta / 2); fun_prop

private theorem aboveVUpper_measurable (cell : Fin 5) :
    Measurable (aboveVUpper cell) := by
  fin_cases cell
  · change Measurable (fun _ : Real => aboveBeta / 2); fun_prop
  · change Measurable (fun _ : Real => aboveBeta / 2); fun_prop
  · change Measurable (fun u : Real => u); fun_prop
  · change Measurable (fun u : Real => u); fun_prop
  · change Measurable (fun u : Real => (1 - u) / 3); fun_prop

private theorem aboveUVFiber_measurable (cell : Fin 5) :
    MeasurableSet (aboveUVFiber cell) :=
  measurableSet_closedIccFiberCell measurableSet_Icc
    (aboveVLower_measurable cell) (aboveVUpper_measurable cell)

private theorem aboveWLower_measurable (cell : Fin 5) :
    Measurable (aboveWLower cell) := by
  fin_cases cell
  · change Measurable (fun z : Real × Real => aboveBeta - z.2); fun_prop
  · change Measurable (fun z : Real × Real => aboveBeta - z.2); fun_prop
  · change Measurable (fun z : Real × Real => z.2); fun_prop
  · change Measurable (fun z : Real × Real => z.2); fun_prop
  · change Measurable (fun z : Real × Real => z.2); fun_prop

private theorem aboveWUpper_measurable : Measurable aboveWUpper := by
  change Measurable (fun z : Real × Real => (1 - z.1 - z.2) / 2)
  fun_prop

private theorem aboveTripleFiber_measurable (cell : Fin 5) :
    MeasurableSet (aboveTripleFiber cell) :=
  measurableSet_closedIccFiberCell (aboveUVFiber_measurable cell)
    (aboveWLower_measurable cell) aboveWUpper_measurable

private theorem above_target_covered :
    sectionSixFirstLowCentralLargeAboveRegion aboveDelta ⊆
      ⋃ cell ∈ (Finset.univ : Finset (Fin 5)), aboveTripleFiber cell := by
  rintro ⟨⟨u, v⟩, w⟩ hx
  rcases hx with ⟨_hgap, horder, hu, _hsumLower, _hsumUpper,
    hsquareLower, _hsquareUpper, hvw, hcap, habove⟩
  have huAlpha : u ≤ aboveAlpha := by
    norm_num [aboveDelta, aboveAlpha, sectionSixThetaOne] at hu ⊢
    exact hu
  have hwUpper : w ≤ aboveWUpper (u, v) := by
    simp only [aboveWUpper]
    linarith
  by_cases hA : v ≤ aboveBeta / 2
  · have huH : aboveH ≤ u := by
      norm_num [aboveDelta, aboveAlpha, aboveBeta, aboveSigma, aboveH,
        sectionSixThetaOne] at hsquareLower hA ⊢
      linarith
    have hwLower : aboveBeta - v ≤ w := by
      norm_num [aboveDelta, aboveBeta, sectionSixThetaTwo] at habove ⊢
      linarith
    by_cases huZero : u ≤ aboveUZero
    · apply above_mem_iUnion 0
      exact ⟨⟨⟨huH, huZero⟩, ⟨by
        norm_num [aboveDelta, aboveVLower, aboveSigma, sectionSixThetaOne]
          at hsquareLower ⊢
        linarith, hA⟩⟩, ⟨hwLower, hwUpper⟩⟩
    · apply above_mem_iUnion 1
      exact ⟨⟨⟨(lt_of_not_ge huZero).le, huAlpha⟩, ⟨by
        norm_num [aboveDelta, aboveVLower, aboveBeta, aboveD,
          sectionSixThetaTwo] at habove hcap ⊢
        linarith, hA⟩⟩, ⟨hwLower, hwUpper⟩⟩
  · have hB : aboveBeta / 2 ≤ v := (lt_of_not_ge hA).le
    have huThird : aboveSigma / 3 ≤ u := by
      norm_num [aboveDelta, aboveAlpha, aboveSigma,
        sectionSixThetaOne] at hsquareLower ⊢
      nlinarith
    have hwLower : v ≤ w := hvw.le
    by_cases huH : u ≤ aboveH
    · apply above_mem_iUnion 2
      exact ⟨⟨⟨huThird, huH⟩, ⟨by
        norm_num [aboveDelta, aboveVLower, aboveSigma, sectionSixThetaOne]
          at hsquareLower ⊢
        linarith, horder⟩⟩, ⟨hwLower, hwUpper⟩⟩
    · by_cases huQuarter : u ≤ 1 / 4
      · apply above_mem_iUnion 3
        exact ⟨⟨⟨(lt_of_not_ge huH).le, huQuarter⟩,
          ⟨hB, horder⟩⟩, ⟨hwLower, hwUpper⟩⟩
      · apply above_mem_iUnion 4
        exact ⟨⟨⟨(lt_of_not_ge huQuarter).le, huAlpha⟩, ⟨hB, by
          norm_num [aboveVUpper]
          linarith⟩⟩, ⟨hwLower, hwUpper⟩⟩

private def aboveBox : Set ((Real × Real) × Real) :=
  (Icc (1 / 10) (1 / 2) ×ˢ Icc (1 / 10) (1 / 2)) ×ˢ
    Icc (1 / 10) (1 / 2)

private theorem aboveTripleFiber_subset_box (cell : Fin 5) :
    aboveTripleFiber cell ⊆ aboveBox := by
  rintro ⟨⟨u, v⟩, w⟩ hz
  rcases hz with ⟨huv, hw⟩
  have hf := aboveUVFiber_facts cell huv
  change ((u ∈ Icc (1 / 10) (1 / 2) ∧
    v ∈ Icc (1 / 10) (1 / 2)) ∧ w ∈ Icc (1 / 10) (1 / 2))
  exact ⟨⟨⟨hf.2.2.1, hf.2.2.2.2.1⟩,
    ⟨hf.2.2.2.1, hf.2.2.2.2.2.1⟩⟩,
    ⟨hf.2.2.2.2.2.2.1.trans hw.1, by
      have := hw.2
      simp only [aboveWUpper] at this
      linarith [hf.1, hf.2.1]⟩⟩

private theorem aboveTripleFiber_cap (cell : Fin 5)
    {z : ((Real × Real) × Real)} (hz : z ∈ aboveTripleFiber cell) :
    z.1.1 + z.1.2 + 2 * z.2 ≤ 1 := by
  have hw := hz.2.2
  simp only [aboveWUpper] at hw
  linarith

private theorem aboveTripleFiber_integrable (cell : Fin 5) :
    IntegrableOn sectionSixFirstLowCentralLargeAboveKernel
      (aboveTripleFiber cell) := by
  let extension := sectionSixFirstLowCentralLargeBelowKernelExtension aboveDelta
    (by norm_num [aboveDelta]) (by norm_num [aboveDelta])
  have hext : IntegrableOn (fun z => extension z) aboveBox :=
    extension.continuous.continuousOn.integrableOn_compact
      ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  apply (hext.mono_set (aboveTripleFiber_subset_box cell)).congr_fun
  · intro z hz
    rcases aboveTripleFiber_subset_box cell hz with ⟨⟨hu, hv⟩, hw⟩
    simpa only [sectionSixFirstLowCentralLargeAboveKernel] using
      sectionSixFirstLowCentralLargeKernelExtension_eq
        aboveDelta (by norm_num [aboveDelta]) (by norm_num [aboveDelta])
        (by
          norm_num [aboveDelta, sectionSixThetaGap, sectionSixThetaOne,
            sectionSixThetaTwo] at hu ⊢
          exact ⟨by linarith [hu.1], hu.2⟩)
        (by
          norm_num [aboveDelta, sectionSixThetaGap, sectionSixThetaOne,
            sectionSixThetaTwo] at hv ⊢
          exact ⟨by linarith [hv.1], hv.2⟩)
        (by
          norm_num [aboveDelta, sectionSixThetaGap, sectionSixThetaOne,
            sectionSixThetaTwo] at hw ⊢
          exact ⟨by linarith [hw.1], hw.2⟩)
        (aboveTripleFiber_cap cell hz)
  · exact aboveTripleFiber_measurable cell

private theorem aboveTripleFiber_nonneg (cell : Fin 5)
    {z : ((Real × Real) × Real)} (hz : z ∈ aboveTripleFiber cell) :
    0 ≤ sectionSixFirstLowCentralLargeAboveKernel z := by
  have hf := aboveUVFiber_facts cell hz.1
  have hw : 0 < z.2 := lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 10)
    (hf.2.2.2.2.2.2.1.trans hz.2.1)
  have harg : 1 ≤ (1 - z.1.1 - z.1.2 - z.2) / z.2 := by
    rw [le_div_iff₀ hw]
    linarith [aboveTripleFiber_cap cell hz]
  have homega := (buchstabFunction_mem_Icc harg).1
  simp only [sectionSixFirstLowCentralLargeAboveKernel,
    sectionSixFirstLowCentralLargeBelowKernel]
  exact div_nonneg (by linarith [homega])
    (mul_nonneg (mul_nonneg hf.1.le hf.2.1.le) (sq_nonneg _))

private theorem above_wFiber_eq (cell : Fin 5) {u v : Real}
    (hz : (u, v) ∈ aboveUVFiber cell) :
    (∫ w in aboveWLower cell (u, v)..aboveWUpper (u, v),
      sectionSixFirstLowCentralLargeAboveKernel ((u, v), w)) =
      aboveMajorant cell u v := by
  have hf := aboveUVFiber_facts cell hz
  let B := 1 - u - v
  let L := aboveWLower cell (u, v)
  let H := aboveWUpper (u, v)
  have hL : 0 < L :=
    lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 10)
      hf.2.2.2.2.2.2.1
  have hLH : L ≤ H := hf.2.2.2.2.2.2.2.1
  have hB : 0 < B := by
    dsimp only [B, H] at hLH ⊢
    linarith
  have hH : H = B / 2 := by
    dsimp only [H, B, aboveWUpper]
  have hHPos : 0 < H := hL.trans_le hLH
  have hHNe : H ≠ 0 := hHPos.ne'
  have hBH : B - H = H := by
    rw [hH]
    ring
  have heq := integral_sectionSixBuchstabInverseBranch_eq
    (u := u) (v := v) (w := 1) (B := B) (l := L) (h := H)
    hf.1 hf.2.1 (by norm_num) hL hLH
    hf.2.2.2.2.2.2.2.2.1
    hf.2.2.2.2.2.2.2.2.2
  change (∫ w in L..H,
    buchstabFunction ((B - w) / w) / (u * v * w ^ 2)) = _
  have heq' :
      (∫ w in L..H,
        buchstabFunction ((B - w) / w) / (u * v * w ^ 2)) =
        1 / (u * v * B) *
          Real.log (H * (B - L) / (L * (B - H))) := by
    simpa only [mul_one] using heq
  rw [heq']
  have harg : H * (B - L) / (L * (B - H)) = aboveRatio cell u v := by
    have hcollapse : H * (B - L) / (L * (B - H)) = (B - L) / L := by
      rw [hBH]
      field_simp [hL.ne', hHNe]
    calc
      _ = (B - L) / L := hcollapse
      _ = aboveRatio cell u v := by
        fin_cases cell <;>
          norm_num [L, B, aboveWLower, aboveRatio, aboveIsA,
            aboveBeta, aboveGamma] <;>
          ring
  rw [harg]
  simp only [aboveMajorant]
  dsimp only [B]
  ring

private theorem aboveMajorant_integrable (cell : Fin 5) :
    IntegrableOn (fun z : Real × Real => aboveMajorant cell z.1 z.2)
      (aboveUVFiber cell) := by
  have hk := aboveTripleFiber_integrable cell
  have hinner :=
    integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
      (aboveUVFiber cell) (aboveWLower cell) aboveWUpper
      sectionSixFirstLowCentralLargeAboveKernel
      (aboveUVFiber_measurable cell) (aboveWLower_measurable cell)
      aboveWUpper_measurable
      (fun z hz => (aboveUVFiber_facts cell hz).2.2.2.2.2.2.2.1)
      (by rw [← Measure.volume_eq_prod]; exact hk)
  apply hinner.congr_fun
  · intro z hz
    exact above_wFiber_eq cell hz
  · exact aboveUVFiber_measurable cell

private theorem above_branch_setIntegral_eq (cell : Fin 5) :
    (∫ z in aboveTripleFiber cell,
      sectionSixFirstLowCentralLargeAboveKernel z) =
      ∫ z in aboveUVFiber cell, aboveMajorant cell z.1 z.2 := by
  have hk := aboveTripleFiber_integrable cell
  have hinner :=
    integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
      (aboveUVFiber cell) (aboveWLower cell) aboveWUpper
      sectionSixFirstLowCentralLargeAboveKernel
      (aboveUVFiber_measurable cell) (aboveWLower_measurable cell)
      aboveWUpper_measurable
      (fun z hz => (aboveUVFiber_facts cell hz).2.2.2.2.2.2.2.1)
      (by rw [← Measure.volume_eq_prod]; exact hk)
  unfold aboveTripleFiber
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
      (aboveUVFiber_measurable cell) (aboveWLower_measurable cell)
      aboveWUpper_measurable
      (fun z hz => (aboveUVFiber_facts cell hz).2.2.2.2.2.2.2.1)
      (by rw [← Measure.volume_eq_prod]; exact hk)]
  exact setIntegral_congr_fun (aboveUVFiber_measurable cell)
    (fun z hz => above_wFiber_eq cell hz)

private theorem above_u_order (cell : Fin 5) :
    aboveULower cell ≤ aboveUUpper cell := by
  fin_cases cell <;>
    norm_num [aboveULower, aboveUUpper, aboveAlpha, aboveSigma, aboveH,
      aboveUZero]

private theorem above_physical_setIntegral_eq (cell : Fin 5) :
    (∫ z in aboveUVFiber cell, aboveMajorant cell z.1 z.2) =
      sectionSixFirstLowCentralLargeAboveReducedCellIntegral Real.log cell := by
  have hm := aboveMajorant_integrable cell
  unfold aboveUVFiber aboveOuter
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated _ _ _ _ measurableSet_Icc
      (aboveVLower_measurable cell) (aboveVUpper_measurable cell)
      (fun u hu => aboveUVFiber_ordered cell hu)
      (by rw [← Measure.volume_eq_prod]; exact hm)]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (above_u_order cell)]
  simp only [sectionSixFirstLowCentralLargeAboveReducedCellIntegral,
    aboveULower, aboveUUpper, aboveVLower, aboveVUpper, aboveMajorant,
    aboveRatio, aboveIsA, aboveAlpha, aboveBeta, aboveGamma, aboveSigma,
    aboveD, aboveH, aboveUZero]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  rfl

private theorem above_integral_le_reduced_cells :
    sectionSixFirstLowCentralLargeAboveIntegral aboveDelta ≤
      ∑ cell : Fin 5,
        sectionSixFirstLowCentralLargeAboveReducedCellIntegral Real.log cell := by
  change (∫ z in sectionSixFirstLowCentralLargeAboveRegion aboveDelta,
    sectionSixFirstLowCentralLargeAboveKernel z) ≤ _
  calc
    _ ≤ ∑ cell ∈ (Finset.univ : Finset (Fin 5)),
        ∫ z in aboveTripleFiber cell,
          sectionSixFirstLowCentralLargeAboveKernel z :=
      setIntegral_le_finset_setIntegral_of_cover volume Finset.univ _ _ _
        (measurableSet_sectionSixFirstLowCentralLargeAboveRegion aboveDelta)
        (fun cell _ => aboveTripleFiber_measurable cell)
        (fun cell _ => aboveTripleFiber_integrable cell)
        (fun cell _ z hz => aboveTripleFiber_nonneg cell hz)
        above_target_covered
    _ = ∑ cell : Fin 5,
        sectionSixFirstLowCentralLargeAboveReducedCellIntegral
          Real.log cell := by
      apply Finset.sum_congr rfl
      intro cell _
      exact (above_branch_setIntegral_eq cell).trans
        (above_physical_setIntegral_eq cell)

theorem
    sectionSixFirstLowCentralLargeAboveIntegral_certificateDelta_le_reducedCellIntegral :
    sectionSixFirstLowCentralLargeAboveIntegral (1 / 1000000) <=
      ∑ cell : Fin 5,
        sectionSixFirstLowCentralLargeAboveReducedCellIntegral Real.log cell := by
  change sectionSixFirstLowCentralLargeAboveIntegral aboveDelta ≤ _
  exact above_integral_le_reduced_cells

end

end PrimesRestrictedDigits
