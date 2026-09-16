import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1GenericTFiberD851
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowFiberIntegrabilityD852
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1WeightedSectionAreaBridgeD832
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1GenericRowOuterComparisonD853 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/--
# generic P1 row outer comparison

This module integrates the t-fiber envelope over the nested r/s fibers. The fixed-d comparison
is unconditional on each closed row; outer interval comparisons retain explicit right-hand
integrability premises. No numeric, source, image, aggregate, or cap claim is made.
-/

private abbrev G : Real := sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev H : Real → Real := sectionSixFirstLowCentralSmallI5P1D807H
private abbrev L : Real → Real := sectionSixFirstLowCentralSmallI5P1D807L
private abbrev Q : Real → Real → Real := sectionSixFirstLowCentralSmallI5P1D816Row0Q4
def sectionSixFirstLowCentralSmallI5P1D853P1RowFactor (i : Fin 256) : Real :=
  (70893 / 125000 : Real) /
      (sectionSixFirstLowCentralSmallI5P1D807Beta -
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i) *
    (1 / G - 1 /
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i - G))

def sectionSixFirstLowCentralSmallI5P1D853P1RowWeight (i : Fin 256) (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i *
    sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
    (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d

private abbrev Fiber (i : Fin 256) (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d

private abbrev rowFactor (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i

private abbrev rowWeight (i : Fin 256) (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D853P1RowWeight i d

private theorem interval_integral_mono_of_nonneg_left
    {f g : Real → Real} {a b : Real}
    (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Ioc a b, 0 ≤ f x)
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ x ∈ Set.Ioc a b, f x ≤ g x) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  apply MeasureTheory.integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hf x hx
  · exact hg.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hfg x hx

private theorem row_mem_piece_interval {i : Fin 256} {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i) :
    d ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
  have hdi : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i) := by
    rw [← sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc i]
    exact hd
  exact ⟨(sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i).trans hdi.1,
    hdi.2.trans (sectionSixFirstLowCentralSmallI5P1D850_row_upper_le_dr i)⟩

private theorem row_h_nonneg {i : Fin 256} {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i) :
    0 ≤ H d := by
  have hp := row_mem_piece_interval hd
  exact (sectionSixFirstLowCentralSmallI5P1D830_p1Case1_endpoint_order hp).1.trans
    (sectionSixFirstLowCentralSmallI5P1D830_p1Case1_endpoint_order hp).2.1

private theorem row_gap_order {i : Fin 256} {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i) :
    G ≤ d - G := by
  have hp := row_mem_piece_interval hd
  have h2g : 2 * G ≤ sectionSixFirstLowCentralSmallI5P1D807Ds := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hg, _, hds, _, _⟩
    change 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Ds
    rw [hg, hds]
    norm_num
  linarith [h2g, hp.1]

private theorem row_piece_mem {i : Fin 256} {d r s t : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 (min r (L d - r)))
    (ht : t ∈ Set.Icc G (d - G)) :
    (((d, r), s), t) ∈ sectionSixFirstLowCentralSmallI5P1D807Piece1 := by
  have hdp := row_mem_piece_interval hd
  change d ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr ∧
    r ∈ Set.Icc 0 (H d) ∧ s ∈ Set.Icc 0 (min r (L d - r)) ∧
      t ∈ Set.Icc G (d - G)
  exact ⟨hdp, hr, hs, ht⟩

private theorem t_nonneg {i : Fin 256} {d r s : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 (min r (L d - r))) :
    ∀ t ∈ Set.Icc G (d - G),
      0 ≤ sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t) := by
  intro t ht
  apply sectionSixFirstLowCentralSmallI5P1D809_kernel_nonneg_piece (1 : Fin 3)
  simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
    row_piece_mem hd hr hs ht

private theorem t_integral_nonneg {i : Fin 256} {d r s : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 (min r (L d - r))) :
    0 ≤ (∫ t in G..(d - G),
      sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) := by
  apply intervalIntegral.integral_nonneg (row_gap_order hd)
  exact t_nonneg hd hr hs

private theorem row_lower_pos (i : Fin 256) :
    0 < sectionSixFirstLowCentralSmallI5P1D849RowLower i := by
  have hds : 0 < sectionSixFirstLowCentralSmallI5P1D807Ds := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, hds, _, _⟩
    rw [hds]
    norm_num
  exact lt_of_lt_of_le hds
    (sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i)

private theorem s_integrand_intervalIntegrable {i : Fin 256} {d r : Real}
    (_hr : r ∈ Set.Icc 0 (H d)) :
    IntervalIntegrable (fun s : Real =>
      rowFactor i * Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) volume
      0 (min r (L d - r)) := by
  have hq : Continuous (fun s : Real =>
      Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) := by
    simpa [Q] using
      sectionSixFirstLowCentralSmallI5P1D816_q4_continuous
        (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
  exact ((continuous_const.mul continuous_const).mul hq).intervalIntegrable _ _

private theorem inner_fiber_le_weight {i : Fin 256} {d r : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (H d)) :
    (∫ s in (0 : Real)..min r (L d - r),
      ∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      ∫ s in (0 : Real)..min r (L d - r),
        rowFactor i * Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s := by
  apply interval_integral_mono_of_nonneg_left
    (sectionSixFirstLowCentralSmallI5P1D831_p1Case1_endpoint_nonneg
      (row_mem_piece_interval hd) hr)
  · intro s hs
    exact t_integral_nonneg hd hr ⟨le_of_lt hs.1, hs.2⟩
  · exact s_integrand_intervalIntegrable hr
  · intro s hs
    exact sectionSixFirstLowCentralSmallI5P1D851_generic_tfiber_le_q4_d809_public hd
      hr ⟨le_of_lt hs.1, hs.2⟩

private theorem inner_fiber_le_weight' {i : Fin 256} {d r : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (H d)) :
    (∫ s in (0 : Real)..min r (L d - r),
      ∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      rowFactor i * (∫ s in (0 : Real)..min r (L d - r),
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) := by
  calc
    (∫ s in (0 : Real)..min r (L d - r),
        ∫ t in G..(d - G),
          sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
        ∫ s in (0 : Real)..min r (L d - r),
          rowFactor i * Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
            Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s :=
      inner_fiber_le_weight hd hr
    _ = rowFactor i * (∫ s in (0 : Real)..min r (L d - r),
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_const_mul]
      ring

private theorem outer_right_continuous (i : Fin 256) (d : Real) :
    Continuous (fun r : Real =>
      rowFactor i * (∫ s in (0 : Real)..min r (L d - r),
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s)) := by
  have hA0 : sectionSixFirstLowCentralSmallI5P1D849RowLower i ≠ 0 := by
    exact ne_of_gt (row_lower_pos i)
  have hq : Continuous (fun r : Real =>
      Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
          (min r (L d - r))) := by
    apply (sectionSixFirstLowCentralSmallI5P1D816_q4_continuous
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)).mul
    have hp : Continuous (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
        (sectionSixFirstLowCentralSmallI5P1D849RowLower i)) := by
      unfold sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
        sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
      fun_prop
    exact hp.comp (continuous_id.min (continuous_const.sub continuous_id))
  have hi : ∀ r : Real,
      (∫ s in (0 : Real)..min r (L d - r),
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) =
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
            (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
            (min r (L d - r)) := by
    intro r
    rw [intervalIntegral.integral_const_mul]
    rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive hA0]
    simp [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
      sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
  rw [show (fun r : Real => rowFactor i *
      (∫ s in (0 : Real)..min r (L d - r),
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s)) =
      (fun r => rowFactor i *
        (Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
            (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
            (min r (L d - r)))) by
        funext r; rw [hi]]
  exact continuous_const.mul hq

private theorem outer_left_nonneg {i : Fin 256} {d r : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (H d)) :
    0 ≤ (∫ s in (0 : Real)..min r (L d - r),
      ∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) := by
  apply intervalIntegral.integral_nonneg
  · exact sectionSixFirstLowCentralSmallI5P1D831_p1Case1_endpoint_nonneg
      (row_mem_piece_interval hd) hr
  intro s hs
  exact t_integral_nonneg hd hr hs

theorem sectionSixFirstLowCentralSmallI5P1D853_p1Row_fiber_le_weightedSection
    {i : Fin 256} {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i) :
    sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d ≤
      sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i *
      sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
        (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d := by
  have hH := row_h_nonneg hd
  have hrightInt : IntervalIntegrable (fun r : Real =>
      rowFactor i * (∫ s in (0 : Real)..min r (L d - r),
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s)) volume
      0 (H d) := (outer_right_continuous i d).intervalIntegrable _ _
  have houter :
      (∫ r in (0 : Real)..H d,
        ∫ s in (0 : Real)..min r (L d - r),
          ∫ t in G..(d - G),
            sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      ∫ r in (0 : Real)..H d,
        rowFactor i * (∫ s in (0 : Real)..min r (L d - r),
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
            Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) := by
    apply interval_integral_mono_of_nonneg_left hH
    · intro r hr
      exact outer_left_nonneg hd ⟨le_of_lt hr.1, hr.2⟩
    · exact hrightInt
    · intro r hr
      exact inner_fiber_le_weight' hd ⟨le_of_lt hr.1, hr.2⟩
  calc
    Fiber i d =
        ∫ r in (0 : Real)..H d,
          ∫ s in (0 : Real)..min r (L d - r),
            ∫ t in G..(d - G),
              sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t) := rfl
    _ ≤ ∫ r in (0 : Real)..H d,
        rowFactor i * (∫ s in (0 : Real)..min r (L d - r),
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
            Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) := houter
    _ = rowFactor i *
        sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d := by
      have hA0 : sectionSixFirstLowCentralSmallI5P1D849RowLower i ≠ 0 := by
        exact ne_of_gt (row_lower_pos i)
      have hinnerQ : ∀ r : Real,
          (∫ s in (0 : Real)..min r (L d - r),
            Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
              Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) =
            Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
              sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
                (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
                (min r (L d - r)) := by
        intro r
        rw [intervalIntegral.integral_const_mul]
        rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive hA0]
        simp [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
          sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
      let g : Real → Real := fun r =>
        Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
            (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
            (min r (L d - r))
      have hsetg :
          sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
              (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d =
            ∫ r in Set.Icc 0 (H d), g r := by
        unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
        apply integral_congr_ae
        filter_upwards with r
        dsimp [g]
        unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight
        change (∫ s in (0 : Real)..min r (L d - r),
            Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
              Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) =
          Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
              (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
              (min r (L d - r))
        exact hinnerQ r
      have hintervalg :
          (∫ r in Set.Icc 0 (H d), g r) = ∫ r in (0 : Real)..H d, g r := by
        rw [integral_Icc_eq_integral_Ioc]
        exact (intervalIntegral.integral_of_le hH).symm
      have hqouter :
          (∫ r in (0 : Real)..H d,
            ∫ s in (0 : Real)..min r (L d - r),
              Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
                Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) =
            sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
              (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d := by
        calc
          (∫ r in (0 : Real)..H d,
              ∫ s in (0 : Real)..min r (L d - r),
                Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
                  Q (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) =
              ∫ r in (0 : Real)..H d, g r := by
                apply intervalIntegral.integral_congr
                intro r hr
                exact hinnerQ r
          _ = ∫ r in Set.Icc 0 (H d), g r := hintervalg.symm
          _ = sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
                (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d := hsetg.symm
      rw [intervalIntegral.integral_const_mul]
      exact congrArg (fun x : Real => rowFactor i * x) hqouter


theorem sectionSixFirstLowCentralSmallI5P1D853_p1Row_integral_le_weightedSection
    (i : Fin 256)
    (hWeightInt : IntervalIntegrable
      (sectionSixFirstLowCentralSmallI5P1D853P1RowWeight i) volume
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i)) :
    (∫ d in sectionSixFirstLowCentralSmallI5P1D849RowLower i..
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d) ≤
      ∫ d in sectionSixFirstLowCentralSmallI5P1D849RowLower i..
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D853P1RowWeight i d := by
  have hab : sectionSixFirstLowCentralSmallI5P1D849RowLower i ≤
      sectionSixFirstLowCentralSmallI5P1D849RowUpper i :=
    sectionSixFirstLowCentralSmallI5P1D850_row_lower_le_upper i
  apply intervalIntegral.integral_mono_on (μ := (volume : Measure Real)) hab
    (sectionSixFirstLowCentralSmallI5P1D852_p1Row_hFiberInt i) hWeightInt
  intro d hd
  apply sectionSixFirstLowCentralSmallI5P1D853_p1Row_fiber_le_weightedSection
  rw [sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc i]
  exact hd


theorem sectionSixFirstLowCentralSmallI5P1D853_p1Row_integral_le_scaled_area
    (i : Fin 256)
    (hAreaInt : IntervalIntegrable (fun d : Real =>
      sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i *
        sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
        (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d) volume
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i)) :
    (∫ d in sectionSixFirstLowCentralSmallI5P1D849RowLower i..
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d) ≤
      ∫ d in sectionSixFirstLowCentralSmallI5P1D849RowLower i..
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i *
          sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) d := by
  have hab : sectionSixFirstLowCentralSmallI5P1D849RowLower i ≤
      sectionSixFirstLowCentralSmallI5P1D849RowUpper i :=
    sectionSixFirstLowCentralSmallI5P1D850_row_lower_le_upper i
  apply intervalIntegral.integral_mono_on (μ := (volume : Measure Real)) hab
    (sectionSixFirstLowCentralSmallI5P1D852_p1Row_hFiberInt i) hAreaInt
  intro d hd
  have hpoint := sectionSixFirstLowCentralSmallI5P1D853_p1Row_fiber_le_weightedSection
    (i := i) (d := d) (by
      rw [sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc i]
      exact hd)
  have harea := sectionSixFirstLowCentralSmallI5P1D832_p1Case1_weightedSection_eq_area
    (a := sectionSixFirstLowCentralSmallI5P1D849RowLower i) (d := d)
    (ne_of_gt (row_lower_pos i))
    ⟨(sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i).trans hd.1,
      hd.2.trans (sectionSixFirstLowCentralSmallI5P1D850_row_upper_le_dr i)⟩
  rw [harea] at hpoint
  exact hpoint


end
end PrimesRestrictedDigits
