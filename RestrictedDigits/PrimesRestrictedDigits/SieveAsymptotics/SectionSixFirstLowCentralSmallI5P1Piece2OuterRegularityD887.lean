import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2OuterCompositionD881
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2Case2AreaD879
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece2OuterRegularityD887 -/

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
private abbrev Outer : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant
private abbrev DX := {d : Real // d ∈ Set.Icc Dr D1}

private theorem dr_le_d1 : Dr ≤ D1 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, _, hDr, hD1⟩
  change sectionSixFirstLowCentralSmallI5P1D807Dr ≤
    sectionSixFirstLowCentralSmallI5P1D807D1
  rw [hDr, hD1]
  norm_num

private theorem basic_signs :
    0 < Gap ∧ 0 < Dr ∧ 2 * Gap ≤ Dr ∧ D1 < Beta := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, hBeta, hGap, _, _, hDr, hD1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < sectionSixFirstLowCentralSmallI5P1D807Gap
    rw [hGap]
    norm_num
  · change 0 < sectionSixFirstLowCentralSmallI5P1D807Dr
    rw [hDr]
    norm_num
  · change 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Dr
    rw [hGap, hDr]
    norm_num
  · change sectionSixFirstLowCentralSmallI5P1D807D1 <
      sectionSixFirstLowCentralSmallI5P1D807Beta
    rw [hD1, hBeta]
    norm_num

private theorem point_signs {d : Real}
    (hd : d ∈ Set.Icc Dr D1) :
    0 < d ∧ 0 < Beta - d ∧ 0 < d - Gap := by
  rcases basic_signs with ⟨hG, hDr, h2G, hD1⟩
  refine ⟨lt_of_lt_of_le hDr hd.1, ?_, ?_⟩
  · exact sub_pos.mpr (lt_of_le_of_lt hd.2 hD1)
  · linarith [hd.1, h2G]

private theorem l_nonneg {d : Real} (hd : d ∈ Set.Icc Dr D1) : 0 ≤ L d := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, _, _, _, _, hDr, hD1⟩
  change d ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
    sectionSixFirstLowCentralSmallI5P1D807D1 at hd
  change 0 ≤ sectionSixFirstLowCentralSmallI5P1D807L d
  norm_num [sectionSixFirstLowCentralSmallI5P1D807L,
    sectionSixFirstLowCentralSmallI5P1D807A,
    sectionSixFirstLowCentralSmallI5P1D807Delta,
    sectionSixThetaOne, sectionSixThetaTwo] at hd ⊢
  linarith

private theorem continuous_variable_interval
    {X : Type*} [TopologicalSpace X]
    (f : X → Real → Real) (a b : X → Real)
    (hf : Continuous f.uncurry) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => ∫ t in a x..b x, f x t) := by
  have hfull : Continuous (fun x => ∫ t in (0 : Real)..b x, f x t) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hf hb
  have hleft : Continuous (fun x => ∫ t in (0 : Real)..a x, f x t) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hf ha
  have heq : (fun x => ∫ t in a x..b x, f x t) =
      (fun x => (∫ t in (0 : Real)..b x, f x t) -
        ∫ t in (0 : Real)..a x, f x t) := by
    funext x
    have hxb : IntervalIntegrable (f x) (volume : Measure Real)
        (0 : Real) (b x) := (hf.uncurry_left x).intervalIntegrable _ _
    have hxa : IntervalIntegrable (f x) (volume : Measure Real)
        (0 : Real) (a x) := (hf.uncurry_left x).intervalIntegrable _ _
    exact (intervalIntegral.integral_interval_sub_left hxb hxa).symm
  rw [heq]
  exact hfull.sub hleft

private theorem primitive_continuous (a : Real) :
    Continuous (fun x : Real => P a x) := by
  unfold P sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
  fun_prop

private theorem q4_joint_continuous :
    Continuous (fun p : DX × Real => Q (p.1 : Real) p.2) := by
  have ha : Continuous (fun p : DX × Real => (p.1 : Real)) := by
    exact continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : DX × Real => p.2) := continuous_snd
  have ha0 : ∀ p : DX × Real, (p.1 : Real) ≠ 0 := by
    intro p
    exact ne_of_gt (point_signs p.1.property).1
  have ha2 : Continuous (fun p : DX × Real => (p.1 : Real) ^ (2 : Nat)) :=
    ha.pow 2
  have ha3 : Continuous (fun p : DX × Real => (p.1 : Real) ^ (3 : Nat)) :=
    ha.pow 3
  have ha4 : Continuous (fun p : DX × Real => (p.1 : Real) ^ (4 : Nat)) :=
    ha.pow 4
  have ha5 : Continuous (fun p : DX × Real => (p.1 : Real) ^ (5 : Nat)) :=
    ha.pow 5
  have ha20 : ∀ p : DX × Real, (p.1 : Real) ^ (2 : Nat) ≠ 0 := fun p =>
    pow_ne_zero 2 (ha0 p)
  have ha30 : ∀ p : DX × Real, (p.1 : Real) ^ (3 : Nat) ≠ 0 := fun p =>
    pow_ne_zero 3 (ha0 p)
  have ha40 : ∀ p : DX × Real, (p.1 : Real) ^ (4 : Nat) ≠ 0 := fun p =>
    pow_ne_zero 4 (ha0 p)
  have ha50 : ∀ p : DX × Real, (p.1 : Real) ^ (5 : Nat) ≠ 0 := fun p =>
    pow_ne_zero 5 (ha0 p)
  have h0 : Continuous (fun p : DX × Real => 1 / (p.1 : Real)) := by
    simpa only [one_div, Pi.inv_def] using ha.inv₀ ha0
  have h2 : Continuous (fun p : DX × Real =>
      p.2 / (p.1 : Real) ^ (2 : Nat)) := hx.div₀ ha2 ha20
  have h3 : Continuous (fun p : DX × Real =>
      p.2 ^ (2 : Nat) / (p.1 : Real) ^ (3 : Nat)) :=
    (hx.pow 2).div₀ ha3 ha30
  have h4 : Continuous (fun p : DX × Real =>
      p.2 ^ (3 : Nat) / (p.1 : Real) ^ (4 : Nat)) :=
    (hx.pow 3).div₀ ha4 ha40
  have h5 : Continuous (fun p : DX × Real =>
      p.2 ^ (4 : Nat) / (p.1 : Real) ^ (5 : Nat)) :=
    (hx.pow 4).div₀ ha5 ha50
  have hq : Continuous (fun p : DX × Real =>
      1 / (p.1 : Real) - p.2 / (p.1 : Real) ^ (2 : Nat) +
        p.2 ^ (2 : Nat) / (p.1 : Real) ^ (3 : Nat) -
        p.2 ^ (3 : Nat) / (p.1 : Real) ^ (4 : Nat) +
        p.2 ^ (4 : Nat) / (p.1 : Real) ^ (5 : Nat)) := by
    exact (((h0.sub h2).add h3).sub h4).add h5
  simpa [Q, sectionSixFirstLowCentralSmallI5P1D816Row0Q4,
    sectionSixFirstLowCentralSmallI5P1D814Q4] using hq

private theorem primitive_joint_continuous :
    Continuous (fun p : DX × Real => P (p.1 : Real) p.2) := by
  have ha : Continuous (fun p : DX × Real => (p.1 : Real)) := by
    exact continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : DX × Real => p.2) := continuous_snd
  have ha0 : ∀ p : DX × Real, (p.1 : Real) ≠ 0 := by
    intro p
    exact ne_of_gt (point_signs p.1.property).1
  have ha2 : Continuous (fun p : DX × Real => (p.1 : Real) ^ (2 : Nat)) :=
    ha.pow 2
  have ha3 : Continuous (fun p : DX × Real => (p.1 : Real) ^ (3 : Nat)) :=
    ha.pow 3
  have ha4 : Continuous (fun p : DX × Real => (p.1 : Real) ^ (4 : Nat)) :=
    ha.pow 4
  have ha5 : Continuous (fun p : DX × Real => (p.1 : Real) ^ (5 : Nat)) :=
    ha.pow 5
  have hden1 : Continuous (fun p : DX × Real => (p.1 : Real)) := ha
  have hden2 : Continuous (fun p : DX × Real => (2 : Real) * (p.1 : Real) ^ 2) :=
    continuous_const.mul ha2
  have hden3 : Continuous (fun p : DX × Real => (3 : Real) * (p.1 : Real) ^ 3) :=
    continuous_const.mul ha3
  have hden4 : Continuous (fun p : DX × Real => (4 : Real) * (p.1 : Real) ^ 4) :=
    continuous_const.mul ha4
  have hden5 : Continuous (fun p : DX × Real => (5 : Real) * (p.1 : Real) ^ 5) :=
    continuous_const.mul ha5
  have hden10 : ∀ p : DX × Real, (p.1 : Real) ≠ 0 := ha0
  have hden20 : ∀ p : DX × Real, (2 : Real) * (p.1 : Real) ^ 2 ≠ 0 := by
    intro p
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ha0 p))
  have hden30 : ∀ p : DX × Real, (3 : Real) * (p.1 : Real) ^ 3 ≠ 0 := by
    intro p
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (ha0 p))
  have hden40 : ∀ p : DX × Real, (4 : Real) * (p.1 : Real) ^ 4 ≠ 0 := by
    intro p
    exact mul_ne_zero (by norm_num) (pow_ne_zero 4 (ha0 p))
  have hden50 : ∀ p : DX × Real, (5 : Real) * (p.1 : Real) ^ 5 ≠ 0 := by
    intro p
    exact mul_ne_zero (by norm_num) (pow_ne_zero 5 (ha0 p))
  have h1 : Continuous (fun p : DX × Real => p.2 / (p.1 : Real)) :=
    hx.div₀ hden1 hden10
  have h2 : Continuous (fun p : DX × Real => p.2 ^ 2 /
      ((2 : Real) * (p.1 : Real) ^ 2)) :=
    (hx.pow 2).div₀ hden2 hden20
  have h3 : Continuous (fun p : DX × Real => p.2 ^ 3 /
      ((3 : Real) * (p.1 : Real) ^ 3)) :=
    (hx.pow 3).div₀ hden3 hden30
  have h4 : Continuous (fun p : DX × Real => p.2 ^ 4 /
      ((4 : Real) * (p.1 : Real) ^ 4)) :=
    (hx.pow 4).div₀ hden4 hden40
  have h5 : Continuous (fun p : DX × Real => p.2 ^ 5 /
      ((5 : Real) * (p.1 : Real) ^ 5)) :=
    (hx.pow 5).div₀ hden5 hden50
  have hp : Continuous (fun p : DX × Real =>
      p.2 / (p.1 : Real) - p.2 ^ 2 / (2 * (p.1 : Real) ^ 2) +
        p.2 ^ 3 / (3 * (p.1 : Real) ^ 3) -
        p.2 ^ 4 / (4 * (p.1 : Real) ^ 4) +
        p.2 ^ 5 / (5 * (p.1 : Real) ^ 5)) := by
    exact (((h1.sub h2).add h3).sub h4).add h5
  simpa [P, sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive] using hp

private theorem diagonal_area_continuous :
    Continuous (fun x : DX => Area (x : Real) (x : Real)) := by
  let f : DX → Real → Real := fun x r =>
    Q (x : Real) r * P (x : Real) (L (x : Real) - r)
  have hL : Continuous (fun x : DX => L (x : Real)) := by
    unfold L sectionSixFirstLowCentralSmallI5P1D807L
    fun_prop
  have hmap : Continuous (fun p : DX × Real =>
      (p.1, L (p.1 : Real) - p.2)) := by
    exact continuous_fst.prodMk
      ((hL.comp continuous_fst).sub continuous_snd)
  have hf : Continuous f.uncurry := by
    dsimp [f]
    exact q4_joint_continuous.mul (primitive_joint_continuous.comp hmap)
  have hhalf : Continuous (fun x : DX => L (x : Real) / 2) := by
    exact hL.div continuous_const (by norm_num)
  have hzero : Continuous (fun _ : DX => (0 : Real)) := continuous_const
  have hupper : Continuous (fun x : DX =>
      ∫ r in L (x : Real) / 2..L (x : Real), f x r) := by
    exact continuous_variable_interval f
      (fun x : DX => L (x : Real) / 2)
      (fun x : DX => L (x : Real)) hf hhalf hL
  have hdiagmap : Continuous (fun x : DX =>
      (x, L (x : Real) / 2)) := by
    exact continuous_id.prodMk hhalf
  have hdiagP : Continuous (fun x : DX =>
      P (x : Real) (L (x : Real) / 2)) :=
    primitive_joint_continuous.comp hdiagmap
  have hfirst : Continuous (fun x : DX =>
      (P (x : Real) (L (x : Real) / 2)) ^ 2 / 2) := by
    exact (hdiagP.pow 2).div continuous_const (by norm_num)
  have harea : Continuous (fun x : DX =>
      (P (x : Real) (L (x : Real) / 2)) ^ 2 / 2 +
        ∫ r in L (x : Real) / 2..L (x : Real), f x r) :=
    hfirst.add hupper
  simpa [Area, f, Q, P, L,
    sectionSixFirstLowCentralSmallI5P1D879Piece2Case2Area] using harea

private theorem scalar_continuousOn :
    ContinuousOn (fun d : Real =>
      ((70893 / 125000 : Real) / (Beta - d) *
        (1 / Gap - 1 / (d - Gap)))) (Set.Icc Dr D1) := by
  have hBeta : ContinuousOn (fun d : Real => Beta - d)
      (Set.Icc Dr D1) := by fun_prop
  have hGap : ContinuousOn (fun d : Real => d - Gap)
      (Set.Icc Dr D1) := by fun_prop
  have hBeta0 : ∀ d ∈ Set.Icc Dr D1, Beta - d ≠ 0 := by
    intro d hd
    exact ne_of_gt (point_signs hd).2.1
  have hGap0 : ∀ d ∈ Set.Icc Dr D1, d - Gap ≠ 0 := by
    intro d hd
    exact ne_of_gt (point_signs hd).2.2
  have hiBeta := hBeta.inv₀ hBeta0
  have hiGap : ContinuousOn (fun d : Real => 1 / (d - Gap))
      (Set.Icc Dr D1) := by
    simpa only [one_div, Pi.inv_def] using hGap.inv₀ hGap0
  have hGapConst : ContinuousOn (fun _ : Real => (Gap : Real))
      (Set.Icc Dr D1) := continuousOn_const
  have hGapConst0 : ∀ d ∈ Set.Icc Dr D1, Gap ≠ 0 :=
    fun _ _ => ne_of_gt basic_signs.1
  have hconst : ContinuousOn (fun _ : Real => (1 / Gap : Real))
      (Set.Icc Dr D1) := by
    simpa only [one_div, Pi.inv_def] using hGapConst.inv₀ hGapConst0
  exact ((continuousOn_const.mul hiBeta).mul (hconst.sub hiGap))

private theorem diagonal_area_continuousOn :
    ContinuousOn (fun d : Real => Area d d) (Set.Icc Dr D1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun x : DX => Area (x : Real) (x : Real))
  exact diagonal_area_continuous

theorem sectionSixFirstLowCentralSmallI5P1D887_piece2_outerMajorant_intervalIntegrable :
    IntervalIntegrable
      sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant
      (volume : Measure Real)
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1 := by
  have hscalar := scalar_continuousOn
  have harea := diagonal_area_continuousOn
  have hout : ContinuousOn (fun d : Real =>
      ((70893 / 125000 : Real) / (Beta - d) *
        (1 / Gap - 1 / (d - Gap))) * Area d d) (Set.Icc Dr D1) :=
    hscalar.mul harea
  have hdef : (fun d : Real => Outer d) = (fun d : Real =>
      ((70893 / 125000 : Real) / (Beta - d) *
        (1 / Gap - 1 / (d - Gap))) * Area d d) := by
    funext d
    rfl
  change IntervalIntegrable (fun d : Real => Outer d) (volume : Measure Real) Dr D1
  rw [hdef]
  exact hout.intervalIntegrable_of_Icc dr_le_d1

end
end PrimesRestrictedDigits
