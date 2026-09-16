/-
fixed-delta, pointwise P1 row-1 fiber envelope. The exported theorem is deliberately local to
the closed row slab; all analytic and geometric extensions remain separate obligations.
-/
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowTFiberD841
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1WeightedSectionAreaBridgeD832
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1SelectedRowHFiberD844 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/- A one-sided interval comparison needs only right-hand integrability when
   the left integrand is nonnegative. -/
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

private abbrev A : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
private abbrev B : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper
private abbrev G : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev H : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807H
private abbrev L : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807L
private abbrev F : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor
private abbrev Q : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4

private theorem row_h_nonneg {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab) :
    0 ≤ H d := by
  have hp := sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd
  exact (sectionSixFirstLowCentralSmallI5P1D830_p1Case1_endpoint_order hp).1.trans
    (sectionSixFirstLowCentralSmallI5P1D830_p1Case1_endpoint_order hp).2.1

private theorem row_gap_order {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab) :
    G ≤ d - G := by
  have hp := sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd
  have hds : sectionSixFirstLowCentralSmallI5P1D807Ds ≤ d :=
    sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints.2.1.trans hd.1
  have h2g : 2 * G ≤ sectionSixFirstLowCentralSmallI5P1D807Ds := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hg, _, hds0, _, _⟩
    change 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Ds
    rw [hg, hds0]
    norm_num
  linarith

private theorem row_piece_mem {d r s t : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab)
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 (min r (L d - r)))
    (ht : t ∈ Set.Icc G (d - G)) :
    (((d, r), s), t) ∈ sectionSixFirstLowCentralSmallI5P1D807Piece1 := by
  have hdp := sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd
  change d ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr ∧
    r ∈ Set.Icc 0 (H d) ∧ s ∈ Set.Icc 0 (min r (L d - r)) ∧
      t ∈ Set.Icc G (d - G)
  exact ⟨hdp, hr, hs, ht⟩

private theorem t_nonneg {d r s : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab)
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 (min r (L d - r))) :
    ∀ t ∈ Set.Icc G (d - G),
      0 ≤ sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t) := by
  intro t ht
  apply sectionSixFirstLowCentralSmallI5P1D809_kernel_nonneg_piece (1 : Fin 3)
  simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
    row_piece_mem hd hr hs ht

private theorem t_integral_nonneg {d r s : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab)
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 (min r (L d - r))) :
    0 ≤ (∫ t in G..(d - G),
      sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) := by
  apply intervalIntegral.integral_nonneg (row_gap_order hd)
  exact t_nonneg hd hr hs

private theorem s_integrand_continuous {d r : Real}
    (_hr : r ∈ Set.Icc 0 (H d)) :
    Continuous (fun s : Real => F * Q A r * Q A s) := by
  have hq : Continuous (fun s : Real => Q A s) := by
    simpa [Q] using sectionSixFirstLowCentralSmallI5P1D816_q4_continuous A
  exact (continuous_const.mul continuous_const).mul hq

private theorem s_integrand_intervalIntegrable {d r : Real}
    (hr : r ∈ Set.Icc 0 (H d)) :
    IntervalIntegrable (fun s : Real => F * Q A r * Q A s) volume
      0 (min r (L d - r)) := by
  exact (s_integrand_continuous hr).intervalIntegrable _ _

private theorem inner_fiber_le_weight {d r : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab)
    (hr : r ∈ Set.Icc 0 (H d)) :
    (∫ s in (0 : Real)..min r (L d - r),
      ∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      ∫ s in (0 : Real)..min r (L d - r), F * Q A r * Q A s := by
  apply interval_integral_mono_of_nonneg_left
    (sectionSixFirstLowCentralSmallI5P1D831_p1Case1_endpoint_nonneg
      (sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd) hr)
  · intro s hs
    exact t_integral_nonneg hd hr ⟨le_of_lt hs.1, hs.2⟩
  · exact s_integrand_intervalIntegrable hr
  · intro s hs
    exact sectionSixFirstLowCentralSmallI5P1D841_p1Row1_tfiber_le_q4 hd
      hr ⟨le_of_lt hs.1, hs.2⟩

private theorem inner_fiber_le_weight' {d r : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab)
    (hr : r ∈ Set.Icc 0 (H d)) :
    (∫ s in (0 : Real)..min r (L d - r),
      ∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      F * (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) := by
  calc
    (∫ s in (0 : Real)..min r (L d - r),
        ∫ t in G..(d - G),
          sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
        ∫ s in (0 : Real)..min r (L d - r), F * Q A r * Q A s :=
      inner_fiber_le_weight hd hr
    _ = F * (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_const_mul]
      ring

private theorem outer_right_continuous {d : Real}
    (_hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab) :
    Continuous (fun r : Real =>
      F * (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s)) := by
  have hq : Continuous (fun r : Real =>
      Q A r * sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A
        (min r (L d - r))) := by
    apply (sectionSixFirstLowCentralSmallI5P1D816_q4_continuous A).mul
    have hp : Continuous (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A) := by
      unfold sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
        sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
      fun_prop
    exact hp.comp (continuous_id.min (continuous_const.sub continuous_id))
  have hi : ∀ r : Real,
      (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) =
        Q A r * sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A
          (min r (L d - r)) := by
    intro r
    rw [intervalIntegral.integral_const_mul]
    rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive]
    · simp [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
        sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
    · exact by
        norm_num [A, sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower]
  rw [show (fun r : Real => F *
      (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s)) =
      (fun r => F * (Q A r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A
          (min r (L d - r)))) by
        funext r; rw [hi]]
  fun_prop

private theorem outer_left_nonneg {d r : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab)
    (hr : r ∈ Set.Icc 0 (H d)) :
    0 ≤ (∫ s in (0 : Real)..min r (L d - r),
      ∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) := by
  apply intervalIntegral.integral_nonneg
  · exact sectionSixFirstLowCentralSmallI5P1D831_p1Case1_endpoint_nonneg
      (sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd) hr
  intro s hs
  exact t_integral_nonneg hd hr hs

theorem sectionSixFirstLowCentralSmallI5P1D844_p1Row1_hFiber
    {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab) :
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber d ≤
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight d := by
  have hH := row_h_nonneg hd
  have hleft_right := outer_right_continuous hd
  have hrightInt : IntervalIntegrable (fun r : Real =>
      F * (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s)) volume 0 (H d) :=
    hleft_right.intervalIntegrable _ _
  have houter :
      (∫ r in (0 : Real)..H d,
        ∫ s in (0 : Real)..min r (L d - r),
          ∫ t in G..(d - G),
            sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      ∫ r in (0 : Real)..H d,
        F * (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) := by
    apply interval_integral_mono_of_nonneg_left hH
    · intro r hr
      exact outer_left_nonneg hd ⟨le_of_lt hr.1, hr.2⟩
    · exact hrightInt
    · intro r hr
      exact inner_fiber_le_weight' hd ⟨le_of_lt hr.1, hr.2⟩
  calc
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber d =
        ∫ r in (0 : Real)..H d,
          ∫ s in (0 : Real)..min r (L d - r),
            ∫ t in G..(d - G),
              sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t) := rfl
    _ ≤ ∫ r in (0 : Real)..H d,
        F * (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) := houter
    _ = F * sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection A d := by
      have hA0 : A ≠ 0 := by
        norm_num [A, sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower]
      have hinnerQ : ∀ r : Real,
          (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) =
            Q A r * sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A
              (min r (L d - r)) := by
        intro r
        rw [intervalIntegral.integral_const_mul]
        rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive hA0]
        have hq0 : sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A 0 = 0 := by
          simp [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
            sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
        rw [hq0, sub_zero]
      let g : Real → Real := fun r =>
        Q A r * sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A
          (min r (L d - r))
      have hsetg :
          sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection A d =
            ∫ r in Set.Icc 0 (H d), g r := by
        unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
        apply integral_congr_ae
        filter_upwards with r
        dsimp [g]
        unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight
        change (∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) =
          Q A r * sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A
            (min r (L d - r))
        rw [intervalIntegral.integral_const_mul]
        rw [sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive hA0]
        have hq0 : sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive A 0 = 0 := by
          simp [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
            sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
        rw [hq0, sub_zero]
      have hintervalg :
          (∫ r in Set.Icc 0 (H d), g r) = ∫ r in (0 : Real)..H d, g r := by
        rw [integral_Icc_eq_integral_Ioc]
        exact (intervalIntegral.integral_of_le hH).symm
      have hqouter :
          (∫ r in (0 : Real)..H d,
            ∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) =
            sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection A d := by
        calc
          (∫ r in (0 : Real)..H d,
              ∫ s in (0 : Real)..min r (L d - r), Q A r * Q A s) =
              ∫ r in (0 : Real)..H d, g r := by
                apply intervalIntegral.integral_congr
                intro r hr
                exact hinnerQ r
          _ = ∫ r in Set.Icc 0 (H d), g r := hintervalg.symm
          _ = sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection A d := hsetg.symm
      rw [intervalIntegral.integral_const_mul]
      exact congrArg (fun x : Real => F * x) hqouter
    _ = sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight d := by rfl


end
end PrimesRestrictedDigits
