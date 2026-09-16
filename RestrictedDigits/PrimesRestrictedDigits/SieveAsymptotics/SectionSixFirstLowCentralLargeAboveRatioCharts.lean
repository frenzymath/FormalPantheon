import PrimesRestrictedDigits.BasicEstimates.IntervalIntegralRatioSubstitution
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveFiberReduction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The five reciprocal-affine charts for the upper `I_4` certificate. They reparameterize the
reduced cells from the Section 6 region calculation onto the unit square.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.11).
-/

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

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

private noncomputable def aboveRatio (cell : Fin 5) (u v : Real) : Real :=
  if aboveIsA cell then
    (aboveGamma - u) / (aboveBeta - v)
  else
    (1 - u - 2 * v) / v

private noncomputable def aboveMajorant (cell : Fin 5) (u v : Real) : Real :=
  Real.log (aboveRatio cell u v) / (u * v * (1 - u - v))

private noncomputable def aboveReduced
    (logFunction : Real -> Real) (cell : Fin 5) (u r : Real) : Real :=
  if aboveIsA cell then
    logFunction r / (u * (r + 1) * (u + aboveBeta * r - aboveGamma))
  else
    logFunction r / (u * (1 - u) * (r + 1))

private def aboveRLower (cell : Fin 5) (u : Real) : Real :=
  if aboveIsA cell then
    (aboveGamma - u) / (aboveBeta - aboveVLower cell u)
  else
    (1 - u) / aboveVUpper cell u - 2

private def aboveRUpper (cell : Fin 5) (u : Real) : Real :=
  if aboveIsA cell then
    (aboveGamma - u) / (aboveBeta - aboveVUpper cell u)
  else
    (1 - u) / aboveVLower cell u - 2

private def abovePhysicalU (cell : Fin 5) (x : Real) : Real :=
  aboveULower cell + (aboveUUpper cell - aboveULower cell) * x

private def aboveChartR (cell : Fin 5) (x y : Real) : Real :=
  let u := abovePhysicalU cell x
  aboveRLower cell u + (aboveRUpper cell u - aboveRLower cell u) * y

private theorem above_reduced_cell_eq (cell : Fin 5) :
    sectionSixFirstLowCentralLargeAboveReducedCellIntegral Real.log cell =
      ∫ u in aboveULower cell..aboveUUpper cell,
        ∫ v in aboveVLower cell u..aboveVUpper cell u,
          aboveMajorant cell u v := by
  rfl

private theorem above_transformed_eq (cell : Fin 5) (x y : Real) :
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        Real.log cell x y =
      (aboveUUpper cell - aboveULower cell) *
        (aboveRUpper cell (abovePhysicalU cell x) -
          aboveRLower cell (abovePhysicalU cell x)) *
        aboveReduced Real.log cell (abovePhysicalU cell x)
          (aboveChartR cell x y) := by
  rfl

private theorem above_u_order (cell : Fin 5) :
    aboveULower cell <= aboveUUpper cell := by
  fin_cases cell <;>
    norm_num [aboveULower, aboveUUpper, aboveAlpha, aboveSigma, aboveH,
      aboveUZero]

private theorem above_v_order (cell : Fin 5) {u : Real}
    (hu : u ∈ aboveOuter cell) :
    aboveVLower cell u <= aboveVUpper cell u := by
  fin_cases cell <;>
    norm_num [aboveOuter, aboveULower, aboveUUpper, aboveVLower,
      aboveVUpper, aboveAlpha, aboveBeta, aboveSigma, aboveD, aboveH,
      aboveUZero] at hu ⊢ <;>
    linarith

private theorem above_cell_facts (cell : Fin 5) {u v : Real}
    (hu : u ∈ aboveOuter cell)
    (hv : v ∈ uIcc (aboveVLower cell u) (aboveVUpper cell u)) :
    0 < u ∧ 0 < v ∧ 0 < 1 - u - v ∧
      0 < aboveGamma - u ∧ 0 < aboveBeta - v ∧
      0 < 1 - u - 2 * v := by
  rw [uIcc_of_le (above_v_order cell hu)] at hv
  fin_cases cell <;>
    change u ∈ Icc _ _ at hu <;>
    change v ∈ Icc _ _ at hv <;>
    norm_num [aboveULower, aboveUUpper, aboveVLower, aboveVUpper,
      aboveAlpha, aboveBeta, aboveGamma, aboveSigma, aboveD, aboveH,
      aboveUZero] at hu hv ⊢ <;>
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
      by nlinarith, by nlinarith⟩

private theorem above_a_ratio_integral {u l h : Real}
    (hu : 0 < u) (hgu : 0 < aboveGamma - u)
    (hfacts : ∀ v ∈ uIcc l h,
      0 < v ∧ 0 < 1 - u - v ∧ 0 < aboveBeta - v) :
    (∫ v in l..h,
      Real.log ((aboveGamma - u) / (aboveBeta - v)) /
        (u * v * (1 - u - v))) =
      ∫ r in
        (aboveGamma - u) / (aboveBeta - l)..
          (aboveGamma - u) / (aboveBeta - h),
        Real.log r /
          (u * (r + 1) * (u + aboveBeta * r - aboveGamma)) := by
  let g := fun r : Real => Real.log r /
    (u * (r + 1) * (u + aboveBeta * r - aboveGamma))
  have hg : ContinuousOn g
      ((fun v : Real => (aboveGamma - u) / (aboveBeta - v)) ''
        uIcc l h) := by
    apply continuousOn_of_forall_continuousAt
    rintro _ ⟨v, hv, rfl⟩
    rcases hfacts v hv with ⟨hv0, hB, hbv⟩
    have hr : 0 < (aboveGamma - u) / (aboveBeta - v) := by
      positivity
    have hlast : 0 < u + aboveBeta *
        ((aboveGamma - u) / (aboveBeta - v)) - aboveGamma := by
      rw [show u + aboveBeta * ((aboveGamma - u) / (aboveBeta - v)) -
          aboveGamma = (aboveGamma - u) * v / (aboveBeta - v) by
        field_simp [hbv.ne']
        norm_num [aboveBeta, aboveGamma]
        ring]
      positivity
    dsimp only [g]
    fun_prop (disch := positivity)
  have hsubst := intervalIntegral_const_div_const_sub
    (c := aboveGamma - u) (d := aboveBeta) (g := g)
    (fun v hv => (hfacts v hv).2.2.ne') hg
  calc
    _ = ∫ v in l..h,
        g ((aboveGamma - u) / (aboveBeta - v)) *
          ((aboveGamma - u) / (aboveBeta - v) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rcases hfacts v hv with ⟨hv0, hB, hbv⟩
      have hr1 :
          (aboveGamma - u) / (aboveBeta - v) + 1 =
            (1 - u - v) / (aboveBeta - v) := by
        field_simp [hbv.ne']
        norm_num [aboveBeta, aboveGamma]
        ring
      have hlast :
          u + aboveBeta * ((aboveGamma - u) / (aboveBeta - v)) -
              aboveGamma =
            (aboveGamma - u) * v / (aboveBeta - v) := by
        field_simp [hbv.ne']
        norm_num [aboveBeta, aboveGamma]
        ring
      have hjac :
          (u * ((aboveGamma - u) / (aboveBeta - v) + 1) *
              (u + aboveBeta * ((aboveGamma - u) / (aboveBeta - v)) -
                aboveGamma))⁻¹ *
              ((aboveGamma - u) / (aboveBeta - v) ^ 2) =
            (u * v * (1 - u - v))⁻¹ := by
        rw [hr1, hlast]
        field_simp [hu.ne', hv0.ne', hB.ne', hgu.ne', hbv.ne']
      dsimp only [g]
      calc
        Real.log ((aboveGamma - u) / (aboveBeta - v)) /
            (u * v * (1 - u - v)) =
          Real.log ((aboveGamma - u) / (aboveBeta - v)) *
            (u * v * (1 - u - v))⁻¹ := by rw [div_eq_mul_inv]
        _ = Real.log ((aboveGamma - u) / (aboveBeta - v)) *
            ((u * ((aboveGamma - u) / (aboveBeta - v) + 1) *
                (u + aboveBeta * ((aboveGamma - u) / (aboveBeta - v)) -
                  aboveGamma))⁻¹ *
              ((aboveGamma - u) / (aboveBeta - v) ^ 2)) := by
          rw [hjac]
        _ = Real.log ((aboveGamma - u) / (aboveBeta - v)) /
              (u * ((aboveGamma - u) / (aboveBeta - v) + 1) *
                (u + aboveBeta * ((aboveGamma - u) / (aboveBeta - v)) -
                  aboveGamma)) *
              ((aboveGamma - u) / (aboveBeta - v) ^ 2) := by
          rw [div_eq_mul_inv]
          ring
    _ = _ := hsubst

private theorem above_b_ratio_integral {u l h : Real}
    (hu : 0 < u)
    (hfacts : ∀ v ∈ uIcc l h,
      0 < v ∧ 0 < 1 - u - v ∧ 0 < 1 - u - 2 * v) :
    (∫ v in l..h,
      Real.log ((1 - u - 2 * v) / v) / (u * v * (1 - u - v))) =
      ∫ r in (1 - u) / h - 2..(1 - u) / l - 2,
        Real.log r / (u * (1 - u) * (r + 1)) := by
  let g := fun r : Real => Real.log r / (u * (1 - u) * (r + 1))
  have hg : ContinuousOn g
      ((fun v : Real => (1 - u) / v - 2) '' uIcc l h) := by
    apply continuousOn_of_forall_continuousAt
    rintro _ ⟨v, hv, rfl⟩
    rcases hfacts v hv with ⟨hv0, hB, hnum⟩
    have hcu : 0 < 1 - u := by linarith
    have hr : 0 < (1 - u) / v - 2 := by
      rw [show (1 - u) / v - 2 = (1 - u - 2 * v) / v by
        field_simp [hv0.ne']]
      positivity
    have hr1 : 0 < (1 - u) / v - 2 + 1 := by
      rw [show (1 - u) / v - 2 + 1 = (1 - u - v) / v by
        field_simp [hv0.ne']
        ring]
      positivity
    dsimp only [g]
    fun_prop (disch := positivity)
  have hsubst := intervalIntegral_const_div_sub_const
    (c := 1 - u) (k := 2) (g := g)
    (fun v hv => (hfacts v hv).1.ne') hg
  calc
    _ = ∫ v in l..h,
        g ((1 - u) / v - 2) * ((1 - u) / v ^ 2) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rcases hfacts v hv with ⟨hv0, hB, hnum⟩
      have hcu : 0 < 1 - u := by linarith
      dsimp only [g]
      field_simp [hu.ne', hv0.ne', hB.ne', hnum.ne', hcu.ne']
      ring
    _ = _ := hsubst

private theorem above_vIntegral_eq_rIntegral (cell : Fin 5) {u : Real}
    (hu : u ∈ aboveOuter cell) :
    (∫ v in aboveVLower cell u..aboveVUpper cell u,
      aboveMajorant cell u v) =
      ∫ r in aboveRLower cell u..aboveRUpper cell u,
        aboveReduced Real.log cell u r := by
  have huf : 0 < u ∧ 0 < aboveGamma - u := by
    fin_cases cell <;>
      norm_num [aboveOuter, aboveULower, aboveUUpper, aboveGamma,
        aboveAlpha, aboveSigma, aboveH, aboveUZero] at hu ⊢ <;>
      exact ⟨by linarith, by linarith⟩
  fin_cases cell
  · simpa [aboveMajorant, aboveRatio, aboveReduced, aboveRLower,
      aboveRUpper, aboveIsA] using
      (above_a_ratio_integral huf.1 huf.2 (fun v hv =>
        let hf := above_cell_facts (0 : Fin 5) hu hv
        ⟨hf.2.1, hf.2.2.1, hf.2.2.2.2.1⟩))
  · simpa [aboveMajorant, aboveRatio, aboveReduced, aboveRLower,
      aboveRUpper, aboveIsA] using
      (above_a_ratio_integral huf.1 huf.2 (fun v hv =>
        let hf := above_cell_facts (1 : Fin 5) hu hv
        ⟨hf.2.1, hf.2.2.1, hf.2.2.2.2.1⟩))
  · simpa [aboveMajorant, aboveRatio, aboveReduced, aboveRLower,
      aboveRUpper, aboveIsA] using
      (above_b_ratio_integral huf.1 (fun v hv =>
        let hf := above_cell_facts (2 : Fin 5) hu hv
        ⟨hf.2.1, hf.2.2.1, hf.2.2.2.2.2⟩))
  · simpa [aboveMajorant, aboveRatio, aboveReduced, aboveRLower,
      aboveRUpper, aboveIsA] using
      (above_b_ratio_integral huf.1 (fun v hv =>
        let hf := above_cell_facts (3 : Fin 5) hu hv
        ⟨hf.2.1, hf.2.2.1, hf.2.2.2.2.2⟩))
  · simpa [aboveMajorant, aboveRatio, aboveReduced, aboveRLower,
      aboveRUpper, aboveIsA] using
      (above_b_ratio_integral huf.1 (fun v hv =>
        let hf := above_cell_facts (4 : Fin 5) hu hv
        ⟨hf.2.1, hf.2.2.1, hf.2.2.2.2.2⟩))

private theorem above_inner_chart (cell : Fin 5) {u : Real}
    (hu : u ∈ aboveOuter cell) :
    (∫ v in aboveVLower cell u..aboveVUpper cell u,
      aboveMajorant cell u v) =
      (aboveRUpper cell u - aboveRLower cell u) *
        ∫ y in (0 : Real)..1,
          aboveReduced Real.log cell u
            (aboveRLower cell u +
              (aboveRUpper cell u - aboveRLower cell u) * y) := by
  rw [above_vIntegral_eq_rIntegral cell hu]
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : Real)) (b := 1)
    (fun r => aboveReduced Real.log cell u r)
    (aboveRUpper cell u - aboveRLower cell u) (aboveRLower cell u)
  symm
  calc
    _ = ∫ r in
        aboveRLower cell u +
            (aboveRUpper cell u - aboveRLower cell u) * 0..
          aboveRLower cell u +
            (aboveRUpper cell u - aboveRLower cell u) * 1,
        aboveReduced Real.log cell u r := by
      simpa only [smul_eq_mul] using hchange
    _ = _ := by ring

private theorem abovePhysicalU_mem (cell : Fin 5) {x : Real}
    (hx : x ∈ uIcc (0 : Real) 1) :
    abovePhysicalU cell x ∈ aboveOuter cell := by
  rw [uIcc_of_le zero_le_one] at hx
  fin_cases cell <;>
    norm_num [abovePhysicalU, aboveOuter, aboveULower, aboveUUpper,
      aboveAlpha, aboveSigma, aboveH, aboveUZero] at hx ⊢ <;>
    exact ⟨by nlinarith, by nlinarith⟩

private theorem above_reduced_cell_chart (cell : Fin 5) :
    sectionSixFirstLowCentralLargeAboveReducedCellIntegral Real.log cell =
      ∫ x in (0 : Real)..1,
        ∫ y in (0 : Real)..1,
          sectionSixFirstLowCentralLargeAboveTransformedIntegrand
            Real.log cell x y := by
  rw [above_reduced_cell_eq]
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : Real)) (b := 1)
    (fun u => ∫ v in aboveVLower cell u..aboveVUpper cell u,
      aboveMajorant cell u v)
    (aboveUUpper cell - aboveULower cell) (aboveULower cell)
  calc
    _ = (aboveUUpper cell - aboveULower cell) *
        ∫ x in (0 : Real)..1,
          ∫ v in aboveVLower cell (abovePhysicalU cell x)..
            aboveVUpper cell (abovePhysicalU cell x),
            aboveMajorant cell (abovePhysicalU cell x) v := by
      symm
      simpa [smul_eq_mul, abovePhysicalU] using hchange
    _ = ∫ x in (0 : Real)..1,
        (aboveUUpper cell - aboveULower cell) *
          (∫ v in aboveVLower cell (abovePhysicalU cell x)..
            aboveVUpper cell (abovePhysicalU cell x),
            aboveMajorant cell (abovePhysicalU cell x) v) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [above_inner_chart cell (abovePhysicalU_mem cell hx)]
      let U := aboveUUpper cell - aboveULower cell
      let R := aboveRUpper cell (abovePhysicalU cell x) -
        aboveRLower cell (abovePhysicalU cell x)
      let F := fun y : Real => aboveReduced Real.log cell
        (abovePhysicalU cell x)
        (aboveRLower cell (abovePhysicalU cell x) + R * y)
      change U * (R * (∫ y in (0 : Real)..1, F y)) =
        ∫ y in (0 : Real)..1,
          sectionSixFirstLowCentralLargeAboveTransformedIntegrand
            Real.log cell x y
      calc
        _ = U * (∫ y in (0 : Real)..1, R * F y) := by
          rw [← intervalIntegral.integral_const_mul]
        _ = ∫ y in (0 : Real)..1, U * (R * F y) := by
          rw [← intervalIntegral.integral_const_mul]
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro y _
          rw [above_transformed_eq]
          simp only [U, R, F, aboveChartR, mul_assoc]

theorem
    sectionSixFirstLowCentralLargeAboveIntegral_certificateDelta_le_transformedIntegral :
    sectionSixFirstLowCentralLargeAboveIntegral (1 / 1000000) <=
      ∑ cell : Fin 5,
        ∫ x in (0 : Real)..1,
          ∫ y in (0 : Real)..1,
            sectionSixFirstLowCentralLargeAboveTransformedIntegrand
              Real.log cell x y := by
  exact
    sectionSixFirstLowCentralLargeAboveIntegral_certificateDelta_le_reducedCellIntegral.trans_eq
      (Finset.sum_congr rfl (fun cell _ => above_reduced_cell_chart cell))

end

end PrimesRestrictedDigits
