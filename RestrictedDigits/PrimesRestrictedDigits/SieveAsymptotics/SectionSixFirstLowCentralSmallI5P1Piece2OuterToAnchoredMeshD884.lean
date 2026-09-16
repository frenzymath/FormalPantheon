import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2OuterCompositionD881
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2AnchoredMeshD883
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Q4AnchorMonotonicityD882
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2Case2AreaD879
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece2OuterToAnchoredMeshD884 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-
compare the variable-anchor outer majorant with its 128-cell anchored mesh. The two regularity
premises are explicit in the public theorem; all scalar, Q4, Case2, and partition helpers are
private.
-/

private abbrev Dr : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Dr
private abbrev D1 : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D1
private abbrev G : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev Beta : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Beta
private abbrev M : Real := 70893 / 125000
private abbrev L : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807L
private abbrev Q : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4
private abbrev P : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
private abbrev Len : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807L
private abbrev Area : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D879Piece2Case2Area
private abbrev O : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant

private abbrev E (k : Nat) : Real :=
  Dr + (k : Real) * (D1 - Dr) / 128
private abbrev A (i : Fin 128) : Real := E i.1
private abbrev B (i : Fin 128) : Real := E (i.1 + 1)
private abbrev R (i : Fin 128) : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant i

private theorem dr_le_d1 : Dr ≤ D1 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, _, hDr, hD1⟩
  change sectionSixFirstLowCentralSmallI5P1D807Dr ≤
    sectionSixFirstLowCentralSmallI5P1D807D1
  rw [hDr, hD1]
  norm_num

private theorem basic_signs : 0 < G ∧ 0 < Dr ∧ 2 * G ≤ Dr ∧ D1 < Beta := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, hβ, hg, _, _, hdr, hd1⟩
  change 0 < sectionSixFirstLowCentralSmallI5P1D807Gap ∧
    0 < sectionSixFirstLowCentralSmallI5P1D807Dr ∧
    2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Dr ∧
    sectionSixFirstLowCentralSmallI5P1D807D1 <
      sectionSixFirstLowCentralSmallI5P1D807Beta
  rw [hg, hdr, hd1, hβ]
  norm_num

private theorem e_zero : E 0 = Dr := by simp [E]

private theorem e_128 : E 128 = D1 := by
  dsimp [E]
  ring_nf

private theorem e_mono {k : Nat} (_hk : k < 128) : E k ≤ E (k + 1) := by
  have hcast : (k : Real) ≤ ((k + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ k
  have hw : 0 ≤ D1 - Dr := sub_nonneg.mpr dr_le_d1
  dsimp [E]
  have h := mul_le_mul_of_nonneg_right hcast
    (div_nonneg hw (by norm_num : (0 : Real) ≤ 128))
  linarith

private theorem e_bounds {k : Nat} (hk : k ≤ 128) : Dr ≤ E k ∧ E k ≤ D1 := by
  have hk0 : (0 : Real) ≤ (k : Real) := by positivity
  have hk128 : (k : Real) ≤ 128 := by exact_mod_cast hk
  have hw : 0 ≤ D1 - Dr := sub_nonneg.mpr dr_le_d1
  dsimp [E]
  constructor
  · have h := mul_nonneg hk0 (div_nonneg hw (by norm_num : (0 : Real) ≤ 128))
    linarith
  · have h := mul_le_mul_of_nonneg_right hk128
      (div_nonneg hw (by norm_num : (0 : Real) ≤ 128))
    linarith

private theorem e_cell_subset {k : Nat} (hk : k < 128) :
    Set.uIcc (E k) (E (k + 1)) ⊆ Set.uIcc Dr D1 := by
  have hcell := e_mono hk
  have hleft := e_bounds (Nat.le_of_lt hk)
  have hright := e_bounds (Nat.succ_le_of_lt hk)
  rw [Set.uIcc_of_le hcell, Set.uIcc_of_le dr_le_d1]
  intro x hx
  exact ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩

private theorem outer_cell_integrable
    (hOuterInt : IntervalIntegrable O (volume : Measure Real) Dr D1)
    {k : Nat} (hk : k < 128) :
    IntervalIntegrable O (volume : Measure Real) (E k) (E (k + 1)) := by
  exact hOuterInt.mono_set (e_cell_subset hk)

private theorem outer_partition
    (hOuterInt : IntervalIntegrable O (volume : Measure Real) Dr D1) :
    (∑ i : Fin 128, ∫ d in A i..B i, O d) =
      ∫ d in Dr..D1, O d := by
  have hsum :
      (∑ k ∈ Finset.range 128, ∫ d in E k..E (k + 1), O d) =
        ∫ d in E 0..E 128, O d := by
    exact intervalIntegral.sum_integral_adjacent_intervals
      (f := O) (μ := (volume : Measure Real)) (a := E) (n := 128)
      (fun k hk => outer_cell_integrable hOuterInt hk)
  calc
    (∑ i : Fin 128, ∫ d in A i..B i, O d) =
        ∑ i : Fin 128, ∫ d in E i.1..E (i.1 + 1), O d := by rfl
    _ = ∑ k ∈ Finset.range 128, ∫ d in E k..E (k + 1), O d := by
      exact Fin.sum_univ_eq_sum_range
        (fun k => ∫ d in E k..E (k + 1), O d) 128
    _ = ∫ d in E 0..E 128, O d := hsum
    _ = ∫ d in Dr..D1, O d := by rw [e_zero, e_128]

private abbrev Scalar (x : Real) : Real :=
  (M / (Beta - x)) * (1 / G - 1 / (x - G))

private theorem scalar_mono_of_signs {x y : Real}
    (hxy : x ≤ y)
    (hG : 0 < G) (h2G : 2 * G ≤ x)
    (hBx : 0 < Beta - x) (hBy : 0 < Beta - y)
    (hXG : 0 < x - G) (_hYG : 0 < y - G)
    (hM : 0 ≤ M) :
    0 ≤ Scalar x ∧ Scalar x ≤ Scalar y := by
  have hden : Beta - y ≤ Beta - x := by linarith
  have hux : 1 / (Beta - x) ≤ 1 / (Beta - y) := by
    exact one_div_le_one_div_of_le hBy hden
  have hxyG : x - G ≤ y - G := by linarith
  have hvrec : 1 / (y - G) ≤ 1 / (x - G) := by
    exact one_div_le_one_div_of_le hXG hxyG
  have hV : 1 / G - 1 / (x - G) ≤ 1 / G - 1 / (y - G) := by
    linarith
  have hV0 : 0 ≤ 1 / G - 1 / (x - G) := by
    have hGX : G ≤ x - G := by linarith
    have hrec : 1 / (x - G) ≤ 1 / G :=
      one_div_le_one_div_of_le hG hGX
    linarith
  have hVy0 : 0 ≤ 1 / G - 1 / (y - G) := le_trans hV0 hV
  have hMU : 0 ≤ M / (Beta - x) := by positivity
  have hMUy : 0 ≤ M / (Beta - y) := by positivity
  have hMmono : M / (Beta - x) ≤ M / (Beta - y) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hux hM
  refine ⟨mul_nonneg hMU hV0, ?_⟩
  exact mul_le_mul hMmono hV hV0 hMUy

private theorem q_nonneg_of_signs {a x : Real}
    (ha : 0 < a) (hx : 0 ≤ x) : 0 ≤ Q a x := by
  exact (by positivity : 0 ≤ 1 / (a + x)).trans
    (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le ha hx)

private theorem q4_prim_eq {a y : Real} (ha : a ≠ 0) :
    (∫ x in (0 : Real)..y, Q a x) = P a y := by
  rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive ha]
  change P a y - P a 0 = P a y
  rw [show P a 0 = 0 by
    simp [P, sectionSixFirstLowCentralSmallI5P1D814Q4Primitive], sub_zero]

private theorem prim_nonneg {a y : Real} (ha : 0 < a) (hy : 0 ≤ y) :
    0 ≤ P a y := by
  have hi : 0 ≤ ∫ x in (0 : Real)..y, Q a x := by
    apply intervalIntegral.integral_nonneg hy
    intro x hx
    exact q_nonneg_of_signs ha hx.1
  rw [q4_prim_eq (ne_of_gt ha)] at hi
  exact hi

private theorem prim_cont (a : Real) : Continuous (P a) := by
  unfold P sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
  fun_prop

private theorem len_nonneg {d : Real} (hd : d ∈ Set.Icc Dr D1) :
    0 ≤ L d := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, _, _, _, _, _, hD1⟩
  unfold L sectionSixFirstLowCentralSmallI5P1D807L
  have hd1 : d ≤ (180001 / 1000000 : Real) := by simpa [hD1] using hd.2
  rw [hA]
  norm_num at hd1 ⊢
  linarith

private theorem primitive_mono_of_q
    {a d y : Real} (ha : a ≠ 0) (hd : d ≠ 0) (hy : 0 ≤ y)
    (hQ : ∀ x ∈ Set.Icc (0 : Real) y, Q d x ≤ Q a x) :
    P d y ≤ P a y := by
  have hdi : IntervalIntegrable (Q d) (volume : Measure Real) 0 y :=
    (sectionSixFirstLowCentralSmallI5P1D816_q4_continuous d).intervalIntegrable _ _
  have hai : IntervalIntegrable (Q a) (volume : Measure Real) 0 y :=
    (sectionSixFirstLowCentralSmallI5P1D816_q4_continuous a).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (μ := (volume : Measure Real))
    hy hdi hai hQ
  rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive hd,
    sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive ha] at h
  have hP0d : P d 0 = 0 := by
    simp [P, sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
  have hP0a : P a 0 = 0 := by
    simp [P, sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
  linarith

private theorem case2_area_mono_of_facts
    {a d len : Real} (hlen : 0 ≤ len)
    (hQmono : ∀ x ∈ Set.Icc (0 : Real) len, Q d x ≤ Q a x)
    (_hQd0 : ∀ x ∈ Set.Icc (0 : Real) len, 0 ≤ Q d x)
    (hQa0 : ∀ x ∈ Set.Icc (0 : Real) len, 0 ≤ Q a x)
    (hPd : ∀ y ∈ Set.Icc (0 : Real) len, 0 ≤ P d y)
    (hPa : ∀ y ∈ Set.Icc (0 : Real) len, 0 ≤ P a y)
    (hPmono : ∀ y ∈ Set.Icc (0 : Real) len, P d y ≤ P a y)
    (hId : IntervalIntegrable
      (fun r => Q d r * P d (len - r)) (volume : Measure Real) (len / 2) len)
    (hIa : IntervalIntegrable
      (fun r => Q a r * P a (len - r)) (volume : Measure Real) (len / 2) len) :
    P d (len / 2) ^ 2 / 2 +
          ∫ r in len / 2..len, Q d r * P d (len - r) ≤
      P a (len / 2) ^ 2 / 2 +
          ∫ r in len / 2..len, Q a r * P a (len - r) := by
  have hhalf : 0 ≤ len / 2 := by linarith
  have hsq : P d (len / 2) ^ 2 ≤ P a (len / 2) ^ 2 := by
    exact (sq_le_sq₀ (hPd _ ⟨hhalf, by linarith⟩)
      (hPa _ ⟨hhalf, by linarith⟩)).2 (hPmono _ ⟨hhalf, by linarith⟩)
  have hupper : ∀ r ∈ Set.Icc (len / 2) len,
      Q d r * P d (len - r) ≤ Q a r * P a (len - r) := by
    intro r hr
    have hr0 : 0 ≤ r := le_trans hhalf hr.1
    have hlenr : 0 ≤ len - r := sub_nonneg.mpr hr.2
    have hq := hQmono r ⟨hr0, by linarith⟩
    have hpd := hPd (len - r) ⟨hlenr, by linarith⟩
    have hpa := hPa (len - r) ⟨hlenr, by linarith⟩
    have hp := hPmono (len - r) ⟨hlenr, by linarith⟩
    calc
      Q d r * P d (len - r) ≤ Q a r * P d (len - r) :=
        mul_le_mul_of_nonneg_right hq hpd
      _ ≤ Q a r * P a (len - r) :=
        mul_le_mul_of_nonneg_left hp (hQa0 r ⟨hr0, by linarith⟩)
  have hi := intervalIntegral.integral_mono_on
    (μ := (volume : Measure Real)) (by linarith : len / 2 ≤ len)
    hId hIa hupper
  have hsq' : P d (len / 2) ^ 2 / 2 ≤ P a (len / 2) ^ 2 / 2 := by
    exact div_le_div_of_nonneg_right hsq (by norm_num)
  linarith

private theorem qp_intervalIntegrable (a len : Real) :
    IntervalIntegrable (fun r : Real => Q a r * P a (len - r))
      (volume : Measure Real) (len / 2) len := by
  have hq : Continuous (Q a) :=
    sectionSixFirstLowCentralSmallI5P1D816_q4_continuous a
  have hp : Continuous (P a) := by
    unfold P sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
      sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
    fun_prop
  exact (hq.mul (hp.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _

private theorem primitive_nonneg_of_facts {a len y : Real}
    (ha : 0 < a) (hy : y ∈ Set.Icc (0 : Real) len) : 0 ≤ P a y := by
  rw [← q4_prim_eq (ne_of_gt ha)]
  apply intervalIntegral.integral_nonneg hy.1
  intro x hx
  exact q_nonneg_of_signs ha hx.1

private theorem case2_area_nonneg_of_facts {a d : Real}
    (_ha : 0 < a) (hlen : 0 ≤ Len d)
    (hQ : ∀ x ∈ Set.Icc (0 : Real) (Len d), 0 ≤ Q a x)
    (hP : ∀ y ∈ Set.Icc (0 : Real) (Len d), 0 ≤ P a y) :
    0 ≤ Area a d := by
  have hh : 0 ≤ Len d / 2 := by linarith
  have hi' : 0 ≤ ∫ r in Len d / 2..Len d, Q a r * P a (Len d - r) := by
    apply intervalIntegral.integral_nonneg
    · linarith
    · intro r hr
      have hr0 : 0 ≤ r := le_trans hh hr.1
      have hrl : 0 ≤ Len d - r := sub_nonneg.mpr hr.2
      exact mul_nonneg (hQ r ⟨hr0, by linarith⟩)
        (hP (Len d - r) ⟨hrl, by linarith⟩)
  unfold Area
  exact add_nonneg (by positivity) hi'

private theorem case2_area_mono {i : Fin 128} {d : Real}
    (hd : d ∈ Set.Icc (A i) (B i)) : Area d d ≤ Area (A i) d := by
  have hm := e_bounds (Nat.succ_le_of_lt i.isLt)
  have ha0 := e_bounds (Nat.le_of_lt i.isLt)
  have hglobal : d ∈ Set.Icc Dr D1 :=
    ⟨ha0.1.trans hd.1, hd.2.trans hm.2⟩
  have hd0 : 0 < d := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, _, hDr, _⟩
    have hDrp : 0 < Dr := by
      change 0 < sectionSixFirstLowCentralSmallI5P1D807Dr
      rw [hDr]
      norm_num
    exact hDrp.trans_le hglobal.1
  have ha0pos : 0 < A i := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, _, hDr, _⟩
    have hDrp : 0 < Dr := by
      change 0 < sectionSixFirstLowCentralSmallI5P1D807Dr
      rw [hDr]
      norm_num
    exact hDrp.trans_le ha0.1
  have hlen := len_nonneg hglobal
  have hQmono : ∀ x ∈ Set.Icc (0 : Real) (Len d), Q d x ≤ Q (A i) x := by
    intro x hx
    exact sectionSixFirstLowCentralSmallI5P1D882_q4_anchor_mono ha0pos
      hd.1 hx.1
  have hQd0 : ∀ x ∈ Set.Icc (0 : Real) (Len d), 0 ≤ Q d x := by
    intro x hx; exact q_nonneg_of_signs hd0 hx.1
  have hQa0 : ∀ x ∈ Set.Icc (0 : Real) (Len d), 0 ≤ Q (A i) x := by
    intro x hx; exact q_nonneg_of_signs ha0pos hx.1
  have hPd : ∀ y ∈ Set.Icc (0 : Real) (Len d), 0 ≤ P d y := by
    intro y hy; exact primitive_nonneg_of_facts hd0 hy
  have hPa : ∀ y ∈ Set.Icc (0 : Real) (Len d), 0 ≤ P (A i) y := by
    intro y hy; exact primitive_nonneg_of_facts ha0pos hy
  have hPmono : ∀ y ∈ Set.Icc (0 : Real) (Len d), P d y ≤ P (A i) y := by
    intro y hy
    apply primitive_mono_of_q (ne_of_gt ha0pos) (ne_of_gt hd0) hy.1
    intro x hx
    exact hQmono x ⟨hx.1, hx.2.trans hy.2⟩
  have hcmp := case2_area_mono_of_facts hlen hQmono hQd0 hQa0 hPd hPa hPmono
    (qp_intervalIntegrable d (Len d)) (qp_intervalIntegrable (A i) (Len d))
  have hwd := sectionSixFirstLowCentralSmallI5P1D879_piece2_weightedSection_eq_case2Area
    (a := d) (d := d) (ne_of_gt hd0) hlen
  have hwa := sectionSixFirstLowCentralSmallI5P1D879_piece2_weightedSection_eq_case2Area
    (a := A i) (d := d) (ne_of_gt ha0pos) hlen
  change Area d d ≤ Area (A i) d at hcmp
  have hwd' : sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection d d =
      Area d d := hwd
  have hwa' : sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection (A i) d =
      Area (A i) d := hwa
  rw [← hwd', ← hwa'] at hcmp
  calc
    Area d d = sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection d d :=
      hwd'.symm
    _ ≤ sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection (A i) d := hcmp
    _ = Area (A i) d := hwa'

private theorem cell_scalar {i : Fin 128} {d : Real}
    (hd : d ∈ Set.Icc (A i) (B i)) :
    0 ≤ Scalar d ∧ Scalar d ≤ Scalar (B i) := by
  have hm := e_bounds (Nat.succ_le_of_lt i.isLt)
  have hglobal : d ∈ Set.Icc Dr D1 :=
    ⟨(e_bounds (Nat.le_of_lt i.isLt)).1.trans hd.1, hd.2.trans hm.2⟩
  rcases basic_signs with ⟨hG, hDr, h2G, hD1B⟩
  have hdpos : 0 < d := lt_of_lt_of_le hDr hglobal.1
  have hdpG : 0 < d - G := by linarith [h2G, hglobal.1, hG]
  have hdB : 0 < Beta - d := by linarith [hD1B, hglobal.2]
  have hBpos : 0 < B i := lt_of_lt_of_le hDr hm.1
  have hBG : 0 < B i - G := by linarith [h2G, hm.1]
  have hBB : 0 < Beta - B i := by linarith [hD1B, hm.2]
  apply scalar_mono_of_signs hd.2 hG (h2G.trans hglobal.1) hdB hBB hdpG hBG
  norm_num

private theorem cell_area_nonneg {i : Fin 128} {d : Real}
    (hd : d ∈ Set.Icc (A i) (B i)) :
    0 ≤ Area d d ∧ 0 ≤ Area (A i) d := by
  have hm := e_bounds (Nat.succ_le_of_lt i.isLt)
  have hglobal : d ∈ Set.Icc Dr D1 :=
    ⟨(e_bounds (Nat.le_of_lt i.isLt)).1.trans hd.1, hd.2.trans hm.2⟩
  rcases basic_signs with ⟨hG, hDr, h2G, hD1B⟩
  have hdpos : 0 < d := lt_of_lt_of_le hDr hglobal.1
  have hap : 0 < A i := lt_of_lt_of_le hDr (e_bounds (Nat.le_of_lt i.isLt)).1
  have hlen := len_nonneg hglobal
  have hqd : ∀ x ∈ Set.Icc (0 : Real) (Len d), 0 ≤ Q d x := by
    intro x hx; exact q_nonneg_of_signs hdpos hx.1
  have hqa : ∀ x ∈ Set.Icc (0 : Real) (Len d), 0 ≤ Q (A i) x := by
    intro x hx; exact q_nonneg_of_signs hap hx.1
  have hpd : ∀ y ∈ Set.Icc (0 : Real) (Len d), 0 ≤ P d y := by
    intro y hy; exact primitive_nonneg_of_facts hdpos hy
  have hpa : ∀ y ∈ Set.Icc (0 : Real) (Len d), 0 ≤ P (A i) y := by
    intro y hy; exact primitive_nonneg_of_facts hap hy
  exact ⟨case2_area_nonneg_of_facts hdpos hlen hqd hpd,
    case2_area_nonneg_of_facts hap hlen hqa hpa⟩

private theorem cell_pointwise {i : Fin 128} {d : Real}
    (hd : d ∈ Set.Icc (A i) (B i)) : O d ≤ R i d := by
  have hs := cell_scalar hd
  have ha := case2_area_mono hd
  have hn := cell_area_nonneg hd
  have hsb : 0 ≤ Scalar (B i) := hs.1.trans hs.2
  change Scalar d * Area d d ≤ Scalar (B i) * Area (A i) d
  calc
    Scalar d * Area d d ≤ Scalar (B i) * Area d d :=
      mul_le_mul_of_nonneg_right hs.2 hn.1
    _ ≤ Scalar (B i) * Area (A i) d :=
      mul_le_mul_of_nonneg_left ha hsb

private theorem compose_skeleton
    (hOuterInt : IntervalIntegrable O (volume : Measure Real) Dr D1)
    (hRowInt : ∀ i : Fin 128,
      IntervalIntegrable (R i) (volume : Measure Real) (A i) (B i))
    (hPoint : ∀ i : Fin 128, ∀ d ∈ Set.Icc (A i) (B i),
      O d ≤ R i d) :
    (∫ d in Dr..D1, O d) ≤ ∑ i : Fin 128, ∫ d in A i..B i, (R i) d := by
  have hcell : ∀ i : Fin 128,
      IntervalIntegrable O (volume : Measure Real) (A i) (B i) := by
    intro i
    exact outer_cell_integrable hOuterInt i.isLt
  have hle : ∀ i : Fin 128,
      (∫ d in A i..B i, O d) ≤ ∫ d in A i..B i, (R i) d := by
    intro i
    apply intervalIntegral.integral_mono_on
      (μ := (volume : Measure Real))
      (by exact e_mono i.isLt)
      (hcell i) (hRowInt i)
    exact hPoint i
  calc
    (∫ d in Dr..D1, O d) = ∑ i : Fin 128, ∫ d in A i..B i, O d :=
      (outer_partition hOuterInt).symm
    _ ≤ ∑ i : Fin 128, ∫ d in A i..B i, (R i) d :=
      Finset.sum_le_sum (fun i hi => hle i)

theorem sectionSixFirstLowCentralSmallI5P1D884_piece2_outerMajorant_le_anchoredMesh
    (hOuterInt :
      IntervalIntegrable
        sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant
        (volume : Measure Real)
        sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1)
    (hRowInt :
      ∀ i : Fin 128,
        IntervalIntegrable
          (fun d =>
            sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant i d)
          (volume : Measure Real)
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (i : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128)
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (((i : Nat) + 1 : Nat) : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128)) :
    (∫ d in sectionSixFirstLowCentralSmallI5P1D807Dr..
        sectionSixFirstLowCentralSmallI5P1D807D1,
        sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant d) ≤
      ∑ i : Fin 128,
        ∫ d in
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (i : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128)..
          (sectionSixFirstLowCentralSmallI5P1D807Dr +
            (((i : Nat) + 1 : Nat) : Real) *
              (sectionSixFirstLowCentralSmallI5P1D807D1 -
                sectionSixFirstLowCentralSmallI5P1D807Dr) / 128),
          sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant i d := by
  exact compose_skeleton hOuterInt hRowInt (fun i d hd => cell_pointwise hd)

end
end PrimesRestrictedDigits
