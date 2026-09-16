import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2AnchoredMeshD883
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2Case2AreaD879
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece2RowRegularityD886 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

private abbrev Dr : Real := sectionSixFirstLowCentralSmallI5P1D807Dr
private abbrev D1 : Real := sectionSixFirstLowCentralSmallI5P1D807D1
private abbrev Beta : Real := sectionSixFirstLowCentralSmallI5P1D807Beta
private abbrev Gap : Real := sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev L : Real → Real := sectionSixFirstLowCentralSmallI5P1D807L
private abbrev Q : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4
private abbrev P : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
private abbrev Area : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D879Piece2Case2Area

private abbrev RowLower (i : Fin 128) : Real :=
  Dr + (i : Real) * (D1 - Dr) / 128
private abbrev RowUpper (i : Fin 128) : Real :=
  Dr + (((i : Nat) + 1 : Nat) : Real) * (D1 - Dr) / 128

private theorem dr_le_d1 : Dr ≤ D1 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, _, hDr, hD1⟩
  change sectionSixFirstLowCentralSmallI5P1D807Dr ≤
    sectionSixFirstLowCentralSmallI5P1D807D1
  rw [hDr, hD1]
  norm_num

private theorem row_endpoint_order (i : Fin 128) : RowLower i ≤ RowUpper i := by
  have hi : (i : Real) ≤ (((i : Nat) + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ i.1
  have hw : 0 ≤ D1 - Dr := sub_nonneg.mpr dr_le_d1
  dsimp [RowLower, RowUpper]
  have h := mul_le_mul_of_nonneg_right hi
    (div_nonneg hw (by norm_num : (0 : Real) ≤ 128))
  linarith

private theorem row_signs (i : Fin 128) :
    0 < RowLower i ∧
      RowUpper i < Beta ∧
      0 < Gap ∧
      0 < RowUpper i - Gap := by
  have hi0 : (0 : Real) ≤ (i : Real) := by positivity
  have hi128 : (((i : Nat) + 1 : Nat) : Real) ≤ 128 := by
    exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hw : 0 ≤ D1 - Dr := sub_nonneg.mpr dr_le_d1
  have hlow : Dr ≤ RowLower i := by
    dsimp [RowLower]
    nlinarith [mul_nonneg hi0 hw]
  have hupp : RowUpper i ≤ D1 := by
    dsimp [RowUpper]
    have hm := mul_le_mul_of_nonneg_right hi128
      (div_nonneg hw (by norm_num : (0 : Real) ≤ 128))
    nlinarith
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, hBeta, hGap, _, _, hDr, hD1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change sectionSixFirstLowCentralSmallI5P1D807Dr ≤ RowLower i at hlow
    rw [hDr] at hlow
    change 0 < sectionSixFirstLowCentralSmallI5P1D807Dr +
      (i : Real) *
        (sectionSixFirstLowCentralSmallI5P1D807D1 -
          sectionSixFirstLowCentralSmallI5P1D807Dr) / 128
    rw [hDr, hD1]
    norm_num at hlow ⊢
    linarith
  · change RowUpper i ≤ sectionSixFirstLowCentralSmallI5P1D807D1 at hupp
    have hupp' := hupp
    dsimp [RowUpper, Dr, D1] at hupp'
    rw [hDr, hD1] at hupp'
    change sectionSixFirstLowCentralSmallI5P1D807Dr +
      (((i : Nat) + 1 : Nat) : Real) *
      (sectionSixFirstLowCentralSmallI5P1D807D1 -
          sectionSixFirstLowCentralSmallI5P1D807Dr) / 128 <
      sectionSixFirstLowCentralSmallI5P1D807Beta
    rw [hDr, hD1, hBeta]
    norm_num [Nat.cast_add] at hupp' ⊢
    linarith
  · change 0 < sectionSixFirstLowCentralSmallI5P1D807Gap
    rw [hGap]
    norm_num
  · have hUG : Dr ≤ RowUpper i := hlow.trans (row_endpoint_order i)
    change 0 < RowUpper i - sectionSixFirstLowCentralSmallI5P1D807Gap
    rw [sub_pos, hGap]
    change sectionSixFirstLowCentralSmallI5P1D807Dr ≤ RowUpper i at hUG
    rw [hDr] at hUG
    norm_num at hUG ⊢
    linarith

private theorem row_first : RowLower (0 : Fin 128) = Dr := by
  simp [RowLower]

private theorem row_last : RowUpper (⟨127, by norm_num⟩ : Fin 128) = D1 := by
  simp [RowUpper]

private theorem row_adjacent {i : Fin 128} (h : i.1 + 1 < 128) :
    RowUpper i = RowLower ⟨i.1 + 1, h⟩ := by
  simp only [RowUpper, RowLower]

private theorem primitive_continuous (a : Real) :
    Continuous (fun x : Real => P a x) := by
  unfold P sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
  fun_prop

private theorem area_continuous (a : Real) :
    Continuous (fun d : Real => Area a d) := by
  let f : Real → Real → Real := fun d r => Q a r * P a (L d - r)
  have hP : Continuous (fun x : Real => P a x) := primitive_continuous a
  have hL : Continuous L := by
    unfold L sectionSixFirstLowCentralSmallI5P1D807L
    fun_prop
  have hf : Continuous f.uncurry := by
    have hq : Continuous (fun p : Real × Real => Q a p.2) :=
      (sectionSixFirstLowCentralSmallI5P1D816_q4_continuous a).comp
        continuous_snd
    have hp : Continuous (fun p : Real × Real => P a (L p.1 - p.2)) :=
      hP.comp ((hL.comp continuous_fst).sub continuous_snd)
    exact hq.mul hp
  have hLcont : Continuous L := hL
  have hhalf : Continuous (fun d : Real => L d / 2) := by
    exact hLcont.div continuous_const (by norm_num)
  have hfull : Continuous (fun d : Real =>
      ∫ r in (0 : Real)..L d, f d r) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hf hLcont
  have hhalfInt : Continuous (fun d : Real =>
      ∫ r in (0 : Real)..L d / 2, f d r) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hf hhalf
  have hupper : Continuous (fun d : Real =>
      ∫ r in L d / 2..L d, f d r) := by
    have heq : (fun d : Real => ∫ r in L d / 2..L d, f d r) =
        (fun d : Real =>
          (∫ r in (0 : Real)..L d, f d r) -
            ∫ r in (0 : Real)..L d / 2, f d r) := by
      funext d
      have hfull : IntervalIntegrable (f d) (volume : Measure Real)
          (0 : Real) (L d) := (hf.uncurry_left d).intervalIntegrable _ _
      have hhalf : IntervalIntegrable (f d) (volume : Measure Real)
          (0 : Real) (L d / 2) := (hf.uncurry_left d).intervalIntegrable _ _
      exact (intervalIntegral.integral_interval_sub_left hfull hhalf).symm
    rw [heq]
    exact hfull.sub hhalfInt
  have hfirst : Continuous (fun d : Real =>
      (P a (L d / 2)) ^ 2 / 2) := by
    have hp := hP.comp hhalf
    fun_prop
  have harea : Continuous (fun d : Real =>
      (P a (L d / 2)) ^ 2 / 2 + ∫ r in L d / 2..L d, f d r) :=
    hfirst.add hupper
  simpa [Area, f, Q, P, L,
    sectionSixFirstLowCentralSmallI5P1D879Piece2Case2Area] using harea

private theorem row_scalar_continuous (i : Fin 128) :
    Continuous (fun _ : Real =>
      (70893 / 125000 : Real) /
          (Beta - RowUpper i) *
        (1 / Gap - 1 / (RowUpper i - Gap))) := by
  rcases row_signs i with ⟨_, hBeta, hGap, hUpperGap⟩
  have hBeta' : 0 < Beta - RowUpper i := sub_pos.mpr hBeta
  have hBeta0 : Continuous (fun _ : Real => Beta - RowUpper i) := continuous_const
  have hGap0 : Continuous (fun _ : Real => Gap) := continuous_const
  have hUpperGap0 : Continuous (fun _ : Real => RowUpper i - Gap) := continuous_const
  have hfirst : Continuous (fun _ : Real =>
      (70893 / 125000 : Real) / (Beta - RowUpper i)) :=
    continuous_const.div₀ hBeta0 (fun _ => ne_of_gt hBeta')
  have hsecond : Continuous (fun _ : Real => 1 / Gap) :=
    continuous_const.div₀ hGap0 (fun _ => ne_of_gt hGap)
  have hthird : Continuous (fun _ : Real => 1 / (RowUpper i - Gap)) :=
    continuous_const.div₀ hUpperGap0 (fun _ => ne_of_gt hUpperGap)
  exact hfirst.mul (hsecond.sub hthird)

theorem sectionSixFirstLowCentralSmallI5P1D886_p2AnchoredRowMajorant_intervalIntegrable
    (i : Fin 128) :
    IntervalIntegrable
      (fun d : Real =>
        sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant i d)
      (volume : Measure Real)
      (sectionSixFirstLowCentralSmallI5P1D807Dr +
        (i : Real) *
          (sectionSixFirstLowCentralSmallI5P1D807D1 -
            sectionSixFirstLowCentralSmallI5P1D807Dr) / 128)
      (sectionSixFirstLowCentralSmallI5P1D807Dr +
        (((i : Nat) + 1 : Nat) : Real) *
          (sectionSixFirstLowCentralSmallI5P1D807D1 -
            sectionSixFirstLowCentralSmallI5P1D807Dr) / 128) := by
  have ha := area_continuous (RowLower i)
  have hs := row_scalar_continuous i
  have hrow : Continuous (fun d : Real =>
      ((70893 / 125000 : Real) /
          (Beta - RowUpper i) *
        (1 / Gap - 1 / (RowUpper i - Gap))) * Area (RowLower i) d) :=
    hs.mul ha
  have hdef : (fun d : Real =>
      sectionSixFirstLowCentralSmallI5P1D883P2AnchoredRowMajorant i d) =
      (fun d : Real =>
        ((70893 / 125000 : Real) /
            (Beta - RowUpper i) *
          (1 / Gap - 1 / (RowUpper i - Gap))) * Area (RowLower i) d) := by
    funext d
    rfl
  rw [hdef]
  exact hrow.intervalIntegrable _ _

end
end PrimesRestrictedDigits
