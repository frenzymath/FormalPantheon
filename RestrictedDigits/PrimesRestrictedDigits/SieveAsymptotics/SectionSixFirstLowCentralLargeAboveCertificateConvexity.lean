import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
Tight upper `I_4` chart properties; source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142,
Eq. (6.11).
-/
open MeasureTheory Set
namespace PrimesRestrictedDigits
noncomputable section
private def aboveBeta : Real := 212499 / 500000
private def aboveGamma : Real := 287501 / 500000
private def aboveULower (cell : Fin 5) : Real :=
  match cell.val with
  | 0 => 43 / 200
  | 1 => 470003 / 1500000
  | 2 => (319999 / 500000) / 3
  | 3 => 43 / 200
  | _ => 1 / 4
private def aboveUUpper (cell : Fin 5) : Real :=
  match cell.val with
  | 0 => 470003 / 1500000
  | 1 => 180001 / 500000
  | 2 => 43 / 200
  | 3 => 1 / 4
  | _ => 180001 / 500000
private def aboveVLower (cell : Fin 5) (u : Real) : Real :=
  match cell.val with
  | 0 => (319999 / 500000 - u) / 2
  | 1 => u - 37501 / 250000
  | 2 => (319999 / 500000 - u) / 2
  | _ => aboveBeta / 2
private def aboveVUpper (cell : Fin 5) (u : Real) : Real :=
  match cell.val with
  | 0 => aboveBeta / 2
  | 1 => aboveBeta / 2
  | 2 => u
  | 3 => u
  | _ => (1 - u) / 3
private def abovePhysicalU (cell : Fin 5) (x : Real) : Real :=
  aboveULower cell + (aboveUUpper cell - aboveULower cell) * x
private def aboveRLower (cell : Fin 5) (u : Real) : Real :=
  if cell.val < 2 then
    (aboveGamma - u) / (aboveBeta - aboveVLower cell u)
  else
    (1 - u) / aboveVUpper cell u - 2
private def aboveRUpper (cell : Fin 5) (u : Real) : Real :=
  if cell.val < 2 then
    (aboveGamma - u) / (aboveBeta - aboveVUpper cell u)
  else
    (1 - u) / aboveVLower cell u - 2
private def aboveChartR (cell : Fin 5) (x y : Real) : Real :=
  let u := abovePhysicalU cell x
  aboveRLower cell u + (aboveRUpper cell u - aboveRLower cell u) * y
private def aboveChartBase (cell : Fin 5) (x : Real) : Real :=
  let u := abovePhysicalU cell x
  (aboveUUpper cell - aboveULower cell) *
    (aboveRUpper cell u - aboveRLower cell u)
private def aboveChartDenominator (cell : Fin 5) (x y : Real) : Real :=
  let u := abovePhysicalU cell x
  let r := aboveChartR cell x y
  if cell.val < 2 then
    u * (r + 1) * (u + aboveBeta * r - aboveGamma)
  else
    u * (1 - u) * (r + 1)
private def aboveTightLog (r : Real) : Real :=
  let z := (r - 1) / (r + 1)
  2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
private def aboveSquare : Set (Real × Real) :=
  Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1
private theorem abovePhysicalU_mem (cell : Fin 5) {x : Real}
    (hx : x ∈ Icc (0 : Real) 1) :
    abovePhysicalU cell x ∈ Icc (aboveULower cell) (aboveUUpper cell) := by
  rcases hx with ⟨hx0, hx1⟩
  fin_cases cell <;>
    norm_num [abovePhysicalU, aboveULower, aboveUUpper] at hx0 hx1 ⊢ <;>
    constructor <;> nlinarith
private theorem aboveRatio_mem {n d : Real} (hd : 0 < d)
    (hlo : d <= n) (hhi : n <= (360002 / 212499) * d) :
    n / d ∈ Icc (1 : Real) (360002 / 212499) := by
  exact ⟨(le_div_iff₀ hd).2 (by simpa using hlo), (div_le_iff₀ hd).2 hhi⟩
private theorem aboveRatioSubTwo_mem {n d : Real} (hd : 0 < d)
    (hlo : 3 * d <= n)
    (hhi : n <= (360002 / 212499 + 2) * d) :
    n / d - 2 ∈ Icc (1 : Real) (360002 / 212499) := by
  have hlo' := (le_div_iff₀ hd).2 hlo
  have hhi' := (div_le_iff₀ hd).2 hhi
  exact ⟨by linarith, by linarith⟩
private theorem aboveChartFacts (cell : Fin 5) {x : Real}
    (hx : x ∈ Icc (0 : Real) 1) :
    let u := abovePhysicalU cell x
    u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) ∧
      aboveRLower cell u ∈ Icc (1 : Real) (360002 / 212499) ∧
      aboveRUpper cell u ∈ Icc (1 : Real) (360002 / 212499) ∧
      aboveRLower cell u <= aboveRUpper cell u ∧
      0 <= aboveUUpper cell - aboveULower cell := by
  let u := abovePhysicalU cell x
  have hu := abovePhysicalU_mem cell hx
  change u ∈ _ ∧ aboveRLower cell u ∈ _ ∧ aboveRUpper cell u ∈ _ ∧ _ ∧ _
  change u ∈ Icc (aboveULower cell) (aboveUUpper cell) at hu
  rcases hu with ⟨hu0, hu1⟩
  fin_cases cell
  all_goals norm_num [aboveULower, aboveUUpper] at hu0 hu1
  · change u ∈ _ ∧ aboveRLower (0 : Fin 5) u ∈ _ ∧ aboveRUpper (0 : Fin 5) u ∈ _ ∧ _ ∧ _
    have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) :=
      ⟨by norm_num; nlinarith, by norm_num; nlinarith⟩
    have hl : aboveRLower 0 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply aboveRatio_mem <;>
        norm_num [aboveRLower, aboveVLower, aboveBeta, aboveGamma] at hu0 hu1 ⊢ <;>
        nlinarith
    have hh : aboveRUpper 0 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply aboveRatio_mem <;>
        norm_num [aboveRUpper, aboveVUpper, aboveBeta, aboveGamma] at hu0 hu1 ⊢ <;>
        nlinarith
    have ho : aboveRLower 0 u <= aboveRUpper 0 u := by
      apply div_le_div_of_nonneg_left
      all_goals
        norm_num [aboveRLower, aboveRUpper, aboveVLower, aboveVUpper,
          aboveBeta, aboveGamma] at hu0 hu1 ⊢ <;> nlinarith
    exact ⟨hubroad, hl, hh, ho, by norm_num [aboveULower, aboveUUpper]⟩
  · change u ∈ _ ∧ aboveRLower (1 : Fin 5) u ∈ _ ∧ aboveRUpper (1 : Fin 5) u ∈ _ ∧ _ ∧ _
    have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) :=
      ⟨by norm_num; nlinarith, hu1⟩
    have hd : 0 < aboveGamma - u := by norm_num [aboveGamma]; nlinarith
    have hl : aboveRLower 1 u = 1 := by
      change (aboveGamma - u) / (aboveBeta - (u - 37501 / 250000)) = 1
      rw [show aboveBeta - (u - 37501 / 250000) = aboveGamma - u by
        norm_num [aboveBeta, aboveGamma]; ring]
      exact div_self hd.ne'
    have hh : aboveRUpper 1 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply aboveRatio_mem <;>
        norm_num [aboveRUpper, aboveVUpper, aboveBeta, aboveGamma] at hu0 hu1 ⊢ <;>
        nlinarith
    have hlmem : aboveRLower 1 u ∈ Icc (1 : Real) (360002 / 212499) := by
      rw [hl]; norm_num
    have ho : aboveRLower 1 u <= aboveRUpper 1 u := by
      rw [hl]; exact hh.1
    exact ⟨hubroad, hlmem, hh, ho, by norm_num [aboveULower, aboveUUpper]⟩
  · change u ∈ _ ∧ aboveRLower (2 : Fin 5) u ∈ _ ∧ aboveRUpper (2 : Fin 5) u ∈ _ ∧ _ ∧ _
    have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) :=
      ⟨hu0, by norm_num; nlinarith⟩
    have hl : aboveRLower 2 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply aboveRatioSubTwo_mem <;>
        norm_num [aboveRLower, aboveVUpper] at hu0 hu1 ⊢ <;> nlinarith
    have hh : aboveRUpper 2 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply aboveRatioSubTwo_mem <;>
        norm_num [aboveRUpper, aboveVLower, aboveBeta] at hu0 hu1 ⊢ <;> nlinarith
    have ho : aboveRLower 2 u <= aboveRUpper 2 u := by
      change (1 - u) / u - 2 <=
        (1 - u) / ((319999 / 500000 - u) / 2) - 2
      have hn : 0 <= 1 - u := by nlinarith
      exact sub_le_sub_right (div_le_div_of_nonneg_left hn
        (by norm_num; nlinarith) (by norm_num; nlinarith)) 2
    exact ⟨hubroad, hl, hh, ho, by norm_num [aboveULower, aboveUUpper]⟩
  · change u ∈ _ ∧ aboveRLower (3 : Fin 5) u ∈ _ ∧ aboveRUpper (3 : Fin 5) u ∈ _ ∧ _ ∧ _
    have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) := by
      constructor <;> norm_num <;> nlinarith
    have hl : aboveRLower 3 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply aboveRatioSubTwo_mem <;>
        norm_num [aboveRLower, aboveVUpper] at hu0 hu1 ⊢ <;> nlinarith
    have hh : aboveRUpper 3 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply aboveRatioSubTwo_mem <;>
        norm_num [aboveRUpper, aboveVLower, aboveBeta] at hu0 hu1 ⊢ <;> nlinarith
    have ho : aboveRLower 3 u <= aboveRUpper 3 u := by
      change (1 - u) / u - 2 <=
        (1 - u) / ((212499 / 500000) / 2) - 2
      have hn : 0 <= 1 - u := by nlinarith
      exact sub_le_sub_right (div_le_div_of_nonneg_left hn (by norm_num)
        (by norm_num; nlinarith)) 2
    exact ⟨hubroad, hl, hh, ho, by norm_num [aboveULower, aboveUUpper]⟩
  · change u ∈ _ ∧ aboveRLower (4 : Fin 5) u ∈ _ ∧ aboveRUpper (4 : Fin 5) u ∈ _ ∧ _ ∧ _
    have hubroad : u ∈ Icc (319999 / 1500000 : Real) (180001 / 500000) :=
      ⟨by norm_num; nlinarith, hu1⟩
    have huOne : 0 < 1 - u := by norm_num; nlinarith
    have hl : aboveRLower 4 u = 1 := by
      norm_num [aboveRLower, aboveVUpper]
      field_simp [huOne.ne']
      norm_num
    have hh : aboveRUpper 4 u ∈ Icc (1 : Real) (360002 / 212499) := by
      apply aboveRatioSubTwo_mem <;>
        norm_num [aboveRUpper, aboveVLower, aboveBeta] at hu0 hu1 ⊢ <;> nlinarith
    have hlmem : aboveRLower 4 u ∈ Icc (1 : Real) (360002 / 212499) := by
      rw [hl]; norm_num
    have ho : aboveRLower 4 u <= aboveRUpper 4 u := by
      rw [hl]; exact hh.1
    exact ⟨hubroad, hlmem, hh, ho, by norm_num [aboveULower, aboveUUpper]⟩
private theorem aboveChartR_mem (cell : Fin 5) {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    aboveChartR cell x y ∈ Icc (1 : Real) (360002 / 212499) := by
  obtain ⟨hu, hr0, hr1, horder, hspan⟩ := aboveChartFacts cell hx
  have h := (convex_Icc (1 : Real) (360002 / 212499)).lineMap_mem hr0 hr1 hy
  rw [AffineMap.lineMap_apply_ring'] at h
  change aboveRLower cell (abovePhysicalU cell x) +
      (aboveRUpper cell (abovePhysicalU cell x) -
        aboveRLower cell (abovePhysicalU cell x)) * y ∈ _
  exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
private theorem aboveChartBase_nonneg (cell : Fin 5) {x : Real}
    (hx : x ∈ Icc (0 : Real) 1) : 0 <= aboveChartBase cell x := by
  obtain ⟨hu, hr0, hr1, horder, hspan⟩ := aboveChartFacts cell hx
  exact mul_nonneg hspan (sub_nonneg.mpr horder)
private theorem aboveChartDenominator_pos (cell : Fin 5) {x y : Real}
    (hx : x ∈ Icc (0 : Real) 1) (hy : y ∈ Icc (0 : Real) 1) :
    0 < aboveChartDenominator cell x y := by
  obtain ⟨hu, hr0, hr1, horder, hspan⟩ := aboveChartFacts cell hx
  have hr := aboveChartR_mem cell hx hy
  have hu0 : 0 < abovePhysicalU cell x := by nlinarith [hu.1]
  have hu1 : 0 < 1 - abovePhysicalU cell x := by nlinarith [hu.2]
  have hr1 : 0 < aboveChartR cell x y + 1 := by nlinarith [hr.1]
  by_cases hcell : cell.val < 2
  · have hlast : 0 < abovePhysicalU cell x + aboveBeta *
        aboveChartR cell x y - aboveGamma := by
      norm_num [aboveBeta, aboveGamma] at hu hr ⊢
      nlinarith [hu.1, hr.1]
    simp only [aboveChartDenominator, hcell, if_pos]
    positivity
  · simp only [aboveChartDenominator, hcell, if_false]
    positivity
private theorem aboveTightLog_continuousOn :
    ContinuousOn aboveTightLog (Icc (1 : Real) (360002 / 212499)) := by
  apply continuousOn_of_forall_continuousAt
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
  have hr1 : 0 < r + 1 := by linarith
  have hz0 : 0 <= (r - 1) / (r + 1) := div_nonneg (sub_nonneg.mpr hr.1) hr1.le
  have hz1 : (r - 1) / (r + 1) < 1 := (div_lt_one hr1).2 (by linarith)
  have hsq : ((r - 1) / (r + 1)) ^ 2 < 1 := by
    nlinarith [mul_pos (show 0 < 1 - (r - 1) / (r + 1) by linarith)
      (show 0 < 1 + (r - 1) / (r + 1) by linarith)]
  unfold aboveTightLog
  fun_prop (disch := positivity)
private theorem aboveTightLog_nonneg {r : Real}
    (hr : r ∈ Icc (1 : Real) (360002 / 212499)) : 0 <= aboveTightLog r := by
  have hr1 : 0 < r + 1 := by linarith [hr.1]
  have hz0 : 0 <= (r - 1) / (r + 1) := div_nonneg (sub_nonneg.mpr hr.1) hr1.le
  have hz1 : (r - 1) / (r + 1) < 1 := (div_lt_one hr1).2 (by linarith)
  have hsq : ((r - 1) / (r + 1)) ^ 2 < 1 := by
    nlinarith [mul_pos (show 0 < 1 - (r - 1) / (r + 1) by linarith)
      (show 0 < 1 + (r - 1) / (r + 1) by linarith)]
  unfold aboveTightLog
  positivity
private theorem aboveLog_le_tightLog {r : Real}
    (hr : r ∈ Icc (1 : Real) (360002 / 212499)) :
    Real.log r <= aboveTightLog r := by
  let z := (r - 1) / (r + 1)
  have hr1 : 0 < r + 1 := by linarith [hr.1]
  have hz0 : 0 <= z := by
    exact div_nonneg (sub_nonneg.mpr hr.1) hr1.le
  have hz1 : z < 1 := by
    exact (div_lt_one hr1).2 (by linarith)
  have h := log_cayley_le_tight_n_one hz0 hz1
  have hratio : (1 + z) / (1 - z) = r := by
    dsimp [z]
    field_simp [hr1.ne']
    ring
  rw [hratio] at h
  simpa only [aboveTightLog, z] using h
private theorem aboveTransformed_eq (logFunction : Real -> Real)
    (cell : Fin 5) (x y : Real) :
    sectionSixFirstLowCentralLargeAboveTransformedIntegrand
        logFunction cell x y =
      aboveChartBase cell x *
        (logFunction (aboveChartR cell x y) /
          aboveChartDenominator cell x y) := by
  fin_cases cell <;> rfl
private theorem continuous_aboveVLower (cell : Fin 5) :
    Continuous (aboveVLower cell) := by
  fin_cases cell
  · change Continuous (fun u : Real => (319999 / 500000 - u) / 2); fun_prop
  · change Continuous (fun u : Real => u - 37501 / 250000); fun_prop
  · change Continuous (fun u : Real => (319999 / 500000 - u) / 2); fun_prop
  · change Continuous (fun _ : Real => (212499 / 500000 : Real) / 2); fun_prop
  · change Continuous (fun _ : Real => (212499 / 500000 : Real) / 2); fun_prop
private theorem continuous_aboveVUpper (cell : Fin 5) :
    Continuous (aboveVUpper cell) := by
  fin_cases cell
  · change Continuous (fun _ : Real => (212499 / 500000 : Real) / 2); fun_prop
  · change Continuous (fun _ : Real => (212499 / 500000 : Real) / 2); fun_prop
  · change Continuous (fun u : Real => u); fun_prop
  · change Continuous (fun u : Real => u); fun_prop
  · change Continuous (fun u : Real => (1 - u) / 3); fun_prop
private theorem aboveVDenominators_pos (cell : Fin 5) {u : Real}
    (hu : u ∈ Icc (aboveULower cell) (aboveUUpper cell)) :
    0 < aboveBeta - aboveVLower cell u ∧
      0 < aboveBeta - aboveVUpper cell u ∧
      0 < aboveVLower cell u ∧ 0 < aboveVUpper cell u := by
  fin_cases cell <;> norm_num [aboveULower, aboveUUpper] at hu
  all_goals
    rcases hu with ⟨hu0, hu1⟩
    simp only [aboveVLower, aboveVUpper, aboveBeta]
    exact ⟨by norm_num <;> nlinarith, by norm_num <;> nlinarith,
      by norm_num <;> nlinarith, by norm_num <;> nlinarith⟩
private theorem aboveRLower_continuousOn (cell : Fin 5) :
    ContinuousOn (aboveRLower cell)
      (Icc (aboveULower cell) (aboveUUpper cell)) := by
  change ContinuousOn (fun u => if cell.val < 2 then
    (aboveGamma - u) / (aboveBeta - aboveVLower cell u)
    else (1 - u) / aboveVUpper cell u - 2) _
  by_cases hcell : cell.val < 2
  · simp only [hcell, if_pos]
    exact (continuous_const.sub continuous_id).continuousOn.div
      ((continuous_const.sub (continuous_aboveVLower cell)).continuousOn)
      (fun u hu => (aboveVDenominators_pos cell hu).1.ne')
  · simp only [hcell, if_false]
    exact ((continuous_const.sub continuous_id).continuousOn.div
      (continuous_aboveVUpper cell).continuousOn
      (fun u hu => (aboveVDenominators_pos cell hu).2.2.2.ne')).sub
        continuousOn_const
private theorem aboveRUpper_continuousOn (cell : Fin 5) :
    ContinuousOn (aboveRUpper cell)
      (Icc (aboveULower cell) (aboveUUpper cell)) := by
  change ContinuousOn (fun u => if cell.val < 2 then
    (aboveGamma - u) / (aboveBeta - aboveVUpper cell u)
    else (1 - u) / aboveVLower cell u - 2) _
  by_cases hcell : cell.val < 2
  · simp only [hcell, if_pos]
    exact (continuous_const.sub continuous_id).continuousOn.div
      ((continuous_const.sub (continuous_aboveVUpper cell)).continuousOn)
      (fun u hu => (aboveVDenominators_pos cell hu).2.1.ne')
  · simp only [hcell, if_false]
    exact ((continuous_const.sub continuous_id).continuousOn.div
      (continuous_aboveVLower cell).continuousOn
      (fun u hu => (aboveVDenominators_pos cell hu).2.2.1.ne')).sub
        continuousOn_const
private theorem aboveTightTransformed_continuousOn (cell : Fin 5) :
    ContinuousOn
      (fun z : Real × Real =>
        sectionSixFirstLowCentralLargeAboveTransformedIntegrand
          aboveTightLog cell z.1 z.2) aboveSquare := by
  have hu : ContinuousOn
      (fun z : Real × Real => abovePhysicalU cell z.1) aboveSquare := by
    unfold abovePhysicalU
    fun_prop
  have humap : MapsTo (fun z : Real × Real => abovePhysicalU cell z.1)
      aboveSquare (Icc (aboveULower cell) (aboveUUpper cell)) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact abovePhysicalU_mem cell hx
  have hr0 : ContinuousOn
      (fun z : Real × Real => aboveRLower cell (abovePhysicalU cell z.1))
      aboveSquare := by
    exact (aboveRLower_continuousOn cell).comp' hu humap
  have hr1 : ContinuousOn
      (fun z : Real × Real => aboveRUpper cell (abovePhysicalU cell z.1))
      aboveSquare := by
    exact (aboveRUpper_continuousOn cell).comp' hu humap
  have hr : ContinuousOn
      (fun z : Real × Real => aboveChartR cell z.1 z.2) aboveSquare := by
    refine (hr0.add ((hr1.sub hr0).mul continuousOn_snd)).congr ?_
    rintro ⟨x, y⟩ _
    rfl
  have hrmap : MapsTo
      (fun z : Real × Real => aboveChartR cell z.1 z.2) aboveSquare
      (Icc (1 : Real) (360002 / 212499)) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact aboveChartR_mem cell hx hy
  have hlog : ContinuousOn
      (fun z : Real × Real => aboveTightLog (aboveChartR cell z.1 z.2))
      aboveSquare := by
    exact aboveTightLog_continuousOn.comp' hr hrmap
  have hbase : ContinuousOn
      (fun z : Real × Real => aboveChartBase cell z.1) aboveSquare := by
    have hspan : ContinuousOn
        (fun _ : Real × Real => aboveUUpper cell - aboveULower cell)
        aboveSquare := continuousOn_const
    refine (hspan.mul (hr1.sub hr0)).congr ?_
    rintro ⟨x, y⟩ _
    rfl
  have hden : ContinuousOn
      (fun z : Real × Real => aboveChartDenominator cell z.1 z.2)
      aboveSquare := by
    by_cases hcell : cell.val < 2
    · simp only [aboveChartDenominator, hcell, if_pos]
      have hone : ContinuousOn (fun _ : Real × Real => (1 : Real)) aboveSquare := continuousOn_const
      have hbeta : ContinuousOn (fun _ : Real × Real => aboveBeta) aboveSquare := continuousOn_const
      have hgamma : ContinuousOn (fun _ : Real × Real => aboveGamma) aboveSquare := continuousOn_const
      refine ((hu.mul (hr.add hone)).mul ((hu.add (hbeta.mul hr)).sub hgamma)).congr ?_
      rintro ⟨x, y⟩ _
      rfl
    · simp only [aboveChartDenominator, hcell, if_false]
      have hone : ContinuousOn (fun _ : Real × Real => (1 : Real)) aboveSquare := continuousOn_const
      refine ((hu.mul (hone.sub hu)).mul (hr.add hone)).congr ?_
      rintro ⟨x, y⟩ _
      rfl
  have hquot : ContinuousOn (fun z : Real × Real =>
      aboveTightLog (aboveChartR cell z.1 z.2) /
        aboveChartDenominator cell z.1 z.2) aboveSquare := by
    refine (hlog.div hden (fun z hz =>
      (aboveChartDenominator_pos cell hz.1 hz.2).ne')).congr ?_
    rintro ⟨x, y⟩ _
    rfl
  have hproduct : ContinuousOn (fun z : Real × Real =>
      aboveChartBase cell z.1 *
        (aboveTightLog (aboveChartR cell z.1 z.2) /
          aboveChartDenominator cell z.1 z.2)) aboveSquare := by
    refine (hbase.mul hquot).congr ?_
    rintro ⟨x, y⟩ _
    rfl
  refine hproduct.congr ?_
  rintro ⟨x, y⟩ hxy
  exact aboveTransformed_eq aboveTightLog cell x y
private theorem aboveNested_intervalIntegrable
    {f : Real × Real -> Real}
    (hf : ContinuousOn f aboveSquare) :
    IntervalIntegrable (fun x => ∫ y in (0 : Real)..1, f (x, y))
      volume 0 1 := by
  let restricted : C(aboveSquare, Real) :=
    ⟨fun z => f z.1, continuousOn_iff_continuous_restrict.mp hf⟩
  obtain ⟨g, hg⟩ := restricted.exists_restrict_eq
    (isClosed_Icc.prod isClosed_Icc)
  have hgpoint : ∀ z ∈ aboveSquare, g z = f z := by
    intro z hz
    have h := congrArg (fun k : C(aboveSquare, Real) => k ⟨z, hz⟩) hg
    change g z = f z at h
    exact h
  have hparam : Continuous (fun x : Real => ∫ y in (0 : Real)..1, g (x, y)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have htarget : ContinuousOn
      (fun x : Real => ∫ y in (0 : Real)..1, f (x, y)) (Icc 0 1) := by
    refine hparam.continuousOn.congr ?_
    intro x hx
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le zero_le_one] at hy
    exact (hgpoint (x, y) ⟨hx, hy⟩).symm
  exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    zero_le_one htarget
theorem sectionSixFirstLowCentralLargeAbove_tight_properties
    (cell : Fin 5) :
    let tightLog : Real -> Real := fun r =>
      let z := (r - 1) / (r + 1)
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2)))
    ContinuousOn
        (fun z : Real × Real =>
          sectionSixFirstLowCentralLargeAboveTransformedIntegrand
            tightLog cell z.1 z.2)
        (Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) ∧
      (∀ x ∈ Icc (0 : Real) 1,
        IntervalIntegrable
          (sectionSixFirstLowCentralLargeAboveTransformedIntegrand
            tightLog cell x) volume 0 1) ∧
      IntervalIntegrable
        (fun x => ∫ y in (0 : Real)..1,
          sectionSixFirstLowCentralLargeAboveTransformedIntegrand
            tightLog cell x y) volume 0 1 ∧
      (∀ x ∈ Icc (0 : Real) 1, ∀ y ∈ Icc (0 : Real) 1,
        0 <= sectionSixFirstLowCentralLargeAboveTransformedIntegrand
          tightLog cell x y) ∧
      (∀ x ∈ Icc (0 : Real) 1, ∀ y ∈ Icc (0 : Real) 1,
        sectionSixFirstLowCentralLargeAboveTransformedIntegrand
            Real.log cell x y <=
          sectionSixFirstLowCentralLargeAboveTransformedIntegrand
            tightLog cell x y) := by
  dsimp only
  have hcontinuous := aboveTightTransformed_continuousOn cell
  refine ⟨hcontinuous, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) zero_le_one
      (hcontinuous.uncurry_left x hx)
  · exact aboveNested_intervalIntegrable hcontinuous
  · intro x hx y hy
    rw [aboveTransformed_eq]
    exact mul_nonneg (aboveChartBase_nonneg cell hx)
      (div_nonneg (aboveTightLog_nonneg (aboveChartR_mem cell hx hy))
        (aboveChartDenominator_pos cell hx hy).le)
  · intro x hx y hy
    rw [aboveTransformed_eq, aboveTransformed_eq]
    apply mul_le_mul_of_nonneg_left _ (aboveChartBase_nonneg cell hx)
    exact div_le_div_of_nonneg_right
      (aboveLog_le_tightLog (aboveChartR_mem cell hx hy))
      (aboveChartDenominator_pos cell hx hy).le
end
end PrimesRestrictedDigits
