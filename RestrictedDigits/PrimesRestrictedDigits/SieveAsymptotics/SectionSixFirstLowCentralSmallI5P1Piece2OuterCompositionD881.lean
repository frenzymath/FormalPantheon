import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2PremiseDischargeD825
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2Q4FiberAdapterD880
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece2Case2AreaD879
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece2OuterCompositionD881 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# variable-d Piece2 Q4 outer composition

This module composes the transformed Piece2 fiber bridge with the variable-anchor Q4 bound and
the Case2 area identity. The theorem remains conditional on the displayed one-dimensional
outer integrability premise; no numerical cap, source/image, or global claim is made here.
Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

def sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant
    (d : Real) : Real :=
  ((70893 / 125000 : Real) /
      (sectionSixFirstLowCentralSmallI5P1D807Beta - d) *
    (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
      1 / (d - sectionSixFirstLowCentralSmallI5P1D807Gap))) *
    sectionSixFirstLowCentralSmallI5P1D879Piece2Case2Area d d

private abbrev D2 : Set Real :=
  sectionSixFirstLowCentralSmallI5P1D823DOuter2
private abbrev R2 : Set (Real × Real) :=
  sectionSixFirstLowCentralSmallI5P1D823ROuter2
private abbrev S2 : Set ((Real × Real) × Real) :=
  sectionSixFirstLowCentralSmallI5P1D823SOuter2
private abbrev C2 : Set SectionSixP1AffineT :=
  sectionSixFirstLowCentralSmallI5P1D823Piece2Cell
private abbrev F : ((Real × Real) × Real) → Real :=
  sectionSixFirstLowCentralSmallI5P1D823Fiber
private abbrev K : SectionSixP1AffineT → Real :=
  sectionSixFirstLowCentralSmallI5P1D817Kernel
private abbrev Q4 : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4
private abbrev L : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807L
private abbrev G : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev Beta : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Beta
private abbrev Scalar : Real → Real := fun d : Real =>
  ((70893 / 125000 : Real) /
      (Beta - d) * (1 / G - 1 / (d - G)))
private abbrev Box : Set ((Real × Real) × Real) :=
  ((Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1 ×ˢ
      Set.Icc (0 : Real) sectionSixFirstLowCentralSmallI5P1D807A) ×ˢ
    Set.Icc (0 : Real) sectionSixFirstLowCentralSmallI5P1D807A)
private abbrev Q : ((Real × Real) × Real) → Real := fun y =>
  Scalar y.1.1 * Q4 y.1.1 y.1.2 * Q4 y.1.1 y.2

private theorem d881_dr_le_d1 :
    sectionSixFirstLowCentralSmallI5P1D807Dr ≤
      sectionSixFirstLowCentralSmallI5P1D807D1 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, _, hDr, hD1⟩
  rw [hDr, hD1]
  norm_num

private theorem d881_l_nonneg {d : Real} (hd : d ∈ D2) : 0 ≤ L d := by
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

private theorem d881_s_upper_nonneg {z : Real × Real} (hz : z ∈ R2) :
    0 ≤ min z.2 (L z.1 - z.2) := by
  have hr : z.2 ∈ Set.Icc (0 : Real) (L z.1) := hz.2
  exact le_min hr.1 (sub_nonneg.mpr hr.2)

private theorem d881_t_ordered {y : (Real × Real) × Real}
    (hy : y ∈ S2) : G ≤ y.1.1 - G := by
  have hd : sectionSixFirstLowCentralSmallI5P1D807Dr ≤ y.1.1 := hy.1.1.1
  have h2G : 2 * G ≤ sectionSixFirstLowCentralSmallI5P1D807Dr := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hgap, _, _, hdr, _⟩
    change 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Dr
    rw [hgap, hdr]
    norm_num
  linarith

private theorem d881_actual_fiber_integrable :
    IntegrableOn F S2 (volume : Measure ((Real × Real) × Real)) := by
  exact sectionSixFirstLowCentralSmallI5P1D825_piece2_fiber_integrable

private theorem d881_actual_fubini :
    (∫ z in C2, K z ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ y in S2, F y ∂(volume : Measure ((Real × Real) × Real)) := by
  exact sectionSixFirstLowCentralSmallI5P1D825_piece2_fubini

private theorem d881_q4_joint_continuousOn_box :
    ContinuousOn (fun y : (Real × Real) × Real =>
      Q4 y.1.1 y.1.2 * Q4 y.1.1 y.2)
      Box := by
  unfold Q4 sectionSixFirstLowCentralSmallI5P1D816Row0Q4
    sectionSixFirstLowCentralSmallI5P1D814Q4
  let Bx : Set ((Real × Real) × Real) :=
    ((Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1 ×ˢ
      Set.Icc (0 : Real) sectionSixFirstLowCentralSmallI5P1D807A) ×ˢ
      Set.Icc (0 : Real) sectionSixFirstLowCentralSmallI5P1D807A)
  have ha : ContinuousOn (fun y : (Real × Real) × Real => y.1.1) Bx := by
    fun_prop
  have har : ContinuousOn (fun y : (Real × Real) × Real => y.1.2) Bx := by
    fun_prop
  have has : ContinuousOn (fun y : (Real × Real) × Real => y.2) Bx := by
    fun_prop
  have ha0 : ∀ y ∈ Bx, y.1.1 ≠ 0 := by
    intro y hy
    have hd : sectionSixFirstLowCentralSmallI5P1D807Dr ≤ y.1.1 := hy.1.1.1
    have hDrPos : 0 < sectionSixFirstLowCentralSmallI5P1D807Dr := by
      rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
        ⟨_, _, _, _, _, hDr, _⟩
      rw [hDr]
      norm_num
    exact ne_of_gt (lt_of_lt_of_le hDrPos hd)
  have ha2 : ContinuousOn (fun y : (Real × Real) × Real => y.1.1 ^ (2 : Nat)) Bx :=
    ha.pow 2
  have ha3 : ContinuousOn (fun y : (Real × Real) × Real => y.1.1 ^ (3 : Nat)) Bx :=
    ha.pow 3
  have ha4 : ContinuousOn (fun y : (Real × Real) × Real => y.1.1 ^ (4 : Nat)) Bx :=
    ha.pow 4
  have ha5 : ContinuousOn (fun y : (Real × Real) × Real => y.1.1 ^ (5 : Nat)) Bx :=
    ha.pow 5
  have ha20 : ∀ y ∈ Bx, y.1.1 ^ (2 : Nat) ≠ 0 := fun y hy =>
    pow_ne_zero 2 (ha0 y hy)
  have ha30 : ∀ y ∈ Bx, y.1.1 ^ (3 : Nat) ≠ 0 := fun y hy =>
    pow_ne_zero 3 (ha0 y hy)
  have ha40 : ∀ y ∈ Bx, y.1.1 ^ (4 : Nat) ≠ 0 := fun y hy =>
    pow_ne_zero 4 (ha0 y hy)
  have ha50 : ∀ y ∈ Bx, y.1.1 ^ (5 : Nat) ≠ 0 := fun y hy =>
    pow_ne_zero 5 (ha0 y hy)
  have h0 : ContinuousOn (fun y : (Real × Real) × Real =>
      1 / y.1.1) Bx := by
    simpa only [one_div, Pi.inv_def] using ha.inv₀ ha0
  have h2 : ContinuousOn (fun y : (Real × Real) × Real =>
      y.1.2 / y.1.1 ^ (2 : Nat)) Bx :=
    har.div₀ ha2 ha20
  have h3 : ContinuousOn (fun y : (Real × Real) × Real =>
      y.1.2 ^ (2 : Nat) / y.1.1 ^ (3 : Nat)) Bx := by
    exact (har.pow 2).div₀ ha3 ha30
  have h4 : ContinuousOn (fun y : (Real × Real) × Real =>
      y.1.2 ^ (3 : Nat) / y.1.1 ^ (4 : Nat)) Bx := by
    exact (har.pow 3).div₀ ha4 ha40
  have h5 : ContinuousOn (fun y : (Real × Real) × Real =>
      y.1.2 ^ (4 : Nat) / y.1.1 ^ (5 : Nat)) Bx := by
    exact (har.pow 4).div₀ ha5 ha50
  have hqr : ContinuousOn (fun y : (Real × Real) × Real =>
      1 / y.1.1 - y.1.2 / y.1.1 ^ (2 : Nat) +
        y.1.2 ^ (2 : Nat) / y.1.1 ^ (3 : Nat) -
        y.1.2 ^ (3 : Nat) / y.1.1 ^ (4 : Nat) +
        y.1.2 ^ (4 : Nat) / y.1.1 ^ (5 : Nat)) Bx := by
    exact (((h0.sub h2).add h3).sub h4).add h5
  have h2s : ContinuousOn (fun y : (Real × Real) × Real =>
      y.2 / y.1.1 ^ (2 : Nat)) Bx :=
    has.div₀ ha2 ha20
  have h3s : ContinuousOn (fun y : (Real × Real) × Real =>
      y.2 ^ (2 : Nat) / y.1.1 ^ (3 : Nat)) Bx := by
    exact (has.pow 2).div₀ ha3 ha30
  have h4s : ContinuousOn (fun y : (Real × Real) × Real =>
      y.2 ^ (3 : Nat) / y.1.1 ^ (4 : Nat)) Bx := by
    exact (has.pow 3).div₀ ha4 ha40
  have h5s : ContinuousOn (fun y : (Real × Real) × Real =>
      y.2 ^ (4 : Nat) / y.1.1 ^ (5 : Nat)) Bx := by
    exact (has.pow 4).div₀ ha5 ha50
  have hqs : ContinuousOn (fun y : (Real × Real) × Real =>
      1 / y.1.1 - y.2 / y.1.1 ^ (2 : Nat) +
        y.2 ^ (2 : Nat) / y.1.1 ^ (3 : Nat) -
        y.2 ^ (3 : Nat) / y.1.1 ^ (4 : Nat) +
        y.2 ^ (4 : Nat) / y.1.1 ^ (5 : Nat)) Bx := by
    exact (((h0.sub h2s).add h3s).sub h4s).add h5s
  exact (hqr.mul hqs)

private theorem d881_scalar_continuousOn_Icc :
    ContinuousOn (fun d : Real =>
      ((70893 / 125000 : Real) /
          (Beta - d) * (1 / G - 1 / (d - G))))
      (Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1) := by
  have hBeta : ContinuousOn (fun d : Real => Beta - d)
      (Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1) := by fun_prop
  have hGap : ContinuousOn (fun d : Real => d - G)
      (Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1) := by fun_prop
  have hBeta0 : ∀ d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1, Beta - d ≠ 0 := by
    intro d hd
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, hbeta, _, _, _, _, hD1⟩
    change sectionSixFirstLowCentralSmallI5P1D807Beta - d ≠ 0
    have hlt : d < sectionSixFirstLowCentralSmallI5P1D807Beta := by
      have hD1lt : sectionSixFirstLowCentralSmallI5P1D807D1 <
          sectionSixFirstLowCentralSmallI5P1D807Beta := by
        rw [hD1, hbeta]
        norm_num
      linarith [hd.2, hD1lt]
    exact ne_of_gt (sub_pos.mpr hlt)
  have hGap0 : ∀ d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1, d - G ≠ 0 := by
    intro d hd
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hgap, _, _, hDr, _⟩
    change d - sectionSixFirstLowCentralSmallI5P1D807Gap ≠ 0
    have hpos : 0 < d - sectionSixFirstLowCentralSmallI5P1D807Gap := by
      have h2G : 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
          sectionSixFirstLowCentralSmallI5P1D807Dr := by
        rw [hgap, hDr]
        norm_num
      have hGpos : 0 < sectionSixFirstLowCentralSmallI5P1D807Gap := by
        rw [hgap]
        norm_num
      linarith [hd.1, h2G]
    exact ne_of_gt hpos
  have hiBeta := hBeta.inv₀ hBeta0
  have hiGap : ContinuousOn (fun d : Real => 1 / (d - G))
      (Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1) := by
    simpa only [one_div, Pi.inv_def] using hGap.inv₀ hGap0
  have hconst : ContinuousOn (fun _ : Real =>
      (1 / G : Real)) (Set.Icc
        sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1) := by fun_prop
  exact ((continuousOn_const.mul hiBeta).mul (hconst.sub hiGap))

private theorem d881_box_subset : S2 ⊆ Box := by
  intro y hy
  change y.1 ∈ R2 ∧ y.2 ∈ Set.Icc (0 : Real)
    (min y.1.2 (L y.1.1 - y.1.2)) at hy
  have hd : y.1.1 ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1 := hy.1.1
  have hr : y.1.2 ∈ Set.Icc (0 : Real) (L y.1.1) := hy.1.2
  have hs := hy.2
  have hrA : y.1.2 ≤ sectionSixFirstLowCentralSmallI5P1D807A := by
    have h := hr.2
    have hA : sectionSixFirstLowCentralSmallI5P1D807A =
        (180001 / 500000 : Real) :=
      sectionSixFirstLowCentralSmallI5P1D807_constants.1
    have hDr : sectionSixFirstLowCentralSmallI5P1D807Dr =
        (84167 / 500000 : Real) :=
      sectionSixFirstLowCentralSmallI5P1D807_constants.2.2.2.2.2.1
    have hd0 : (0 : Real) ≤ y.1.1 := by
      rw [hDr] at hd
      exact (by norm_num : (0 : Real) ≤ 84167 / 500000).trans hd.1
    change y.1.2 ≤ sectionSixFirstLowCentralSmallI5P1D807L y.1.1 at h
    norm_num [sectionSixFirstLowCentralSmallI5P1D807L,
      sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Delta,
      sectionSixThetaOne, sectionSixThetaTwo] at h ⊢
    linarith
  have hsR : y.2 ≤ y.1.2 := (le_min_iff.mp hs.2).1
  have hsA : y.2 ≤ sectionSixFirstLowCentralSmallI5P1D807A :=
    hsR.trans hrA
  exact ⟨⟨hd, ⟨hr.1, hrA⟩⟩, ⟨hs.1, hsA⟩⟩

private theorem d881_q_continuousOn_box : ContinuousOn Q Box := by
  have hscalar : ContinuousOn (fun y : (Real × Real) × Real =>
      Scalar y.1.1) Box := by
    exact d881_scalar_continuousOn_Icc.comp (by fun_prop)
      (fun y hy => hy.1.1)
  have hprod := d881_q4_joint_continuousOn_box
  change ContinuousOn (fun y : (Real × Real) × Real =>
    Scalar y.1.1 * Q4 y.1.1 y.1.2 * Q4 y.1.1 y.2) Box
  have hh := hscalar.mul hprod
  convert hh using 1
  · funext y
    dsimp [Q, Scalar]
    ring

private theorem d881_q4_integrable :
    IntegrableOn Q S2
      (volume : Measure ((Real × Real) × Real)) := by
  have hbox : IsCompact Box := by
    exact (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  exact (d881_q_continuousOn_box.integrableOn_compact hbox).mono_set
    d881_box_subset

private theorem d881_q4_set_eq_outer :
    (∫ y in S2, Q y
      ∂(volume : Measure ((Real × Real) × Real))) =
      ∫ d in sectionSixFirstLowCentralSmallI5P1D807Dr..
        sectionSixFirstLowCentralSmallI5P1D807D1,
        sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant d := by
  have hLmeas : Measurable L := by
    unfold L sectionSixFirstLowCentralSmallI5P1D807L
    fun_prop
  have hsUpperMeas : Measurable (fun z : Real × Real =>
      min z.2 (L z.1 - z.2)) := by
    exact measurable_snd.min
      ((hLmeas.comp measurable_fst).sub measurable_snd)
  have h3 : IntegrableOn Q S2
      (volume : Measure ((Real × Real) × Real)) := d881_q4_integrable
  have h2 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    R2 (fun _ : Real × Real => (0 : Real))
      (fun z : Real × Real => min z.2 (L z.1 - z.2)) Q
      sectionSixFirstLowCentralSmallI5P1D823ROuter2_measurable
      (by fun_prop) hsUpperMeas
      (fun z hz => d881_s_upper_nonneg hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  have hS := setIntegral_closedIccFiberCell_eq_iterated
    R2 (fun _ : Real × Real => (0 : Real))
      (fun z : Real × Real => min z.2 (L z.1 - z.2)) Q
      sectionSixFirstLowCentralSmallI5P1D823ROuter2_measurable
      (by fun_prop) hsUpperMeas
      (fun z hz => d881_s_upper_nonneg hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  have hR := setIntegral_closedIccFiberCell_eq_iterated
    D2 (fun _ : Real => (0 : Real)) L
      (fun z : Real × Real =>
        ∫ s in (0 : Real)..min z.2 (L z.1 - z.2), Q (z, s))
      sectionSixFirstLowCentralSmallI5P1D823DOuter2_measurable
      (by fun_prop) hLmeas (fun d hd => d881_l_nonneg hd) (by
        rw [← Measure.volume_eq_prod]
        exact h2)
  have hDrD1 : sectionSixFirstLowCentralSmallI5P1D807Dr ≤
      sectionSixFirstLowCentralSmallI5P1D807D1 := d881_dr_le_d1
  change (∫ y in S2, Q y ∂(volume : Measure ((Real × Real) × Real))) = _
  unfold S2 sectionSixFirstLowCentralSmallI5P1D823SOuter2
  rw [Measure.volume_eq_prod, hS]
  unfold R2 sectionSixFirstLowCentralSmallI5P1D823ROuter2
  rw [Measure.volume_eq_prod, hR]
  unfold D2 sectionSixFirstLowCentralSmallI5P1D823DOuter2
  rw [integral_Icc_eq_integral_Ioc]
  rw [intervalIntegral.integral_of_le hDrD1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with d hd
  have hdIcc : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1 :=
    ⟨le_of_lt hd.1, hd.2⟩
  have hL0 : 0 ≤ L d := by
    apply d881_l_nonneg
    exact hdIcc
  have hd0 : d ≠ 0 := by
    have hDrPos : 0 < sectionSixFirstLowCentralSmallI5P1D807Dr := by
      rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
        ⟨_, _, _, _, _, hDr, _⟩
      rw [hDr]
      norm_num
    exact ne_of_gt (lt_of_lt_of_le hDrPos hdIcc.1)
  have hweighted :
      (∫ r in (0 : Real)..L d,
        ∫ s in (0 : Real)..min r (L d - r), Q4 d r * Q4 d s) =
        sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection d d := by
    unfold sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection
    rw [integral_Icc_eq_integral_Ioc]
    exact intervalIntegral.integral_of_le hL0
  have hw :
      (∫ r in (0 : Real)..L d,
        ∫ s in (0 : Real)..min r (L d - r), Q ((d, r), s)) =
        Scalar d * sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection d d := by
    calc
      (∫ r in (0 : Real)..L d,
          ∫ s in (0 : Real)..min r (L d - r), Q ((d, r), s)) =
          ∫ r in (0 : Real)..L d,
            Scalar d * (∫ s in (0 : Real)..min r (L d - r),
              Q4 d r * Q4 d s) := by
        apply intervalIntegral.integral_congr
        intro r hr
        change (∫ s in (0 : Real)..min r (L d - r),
            (Scalar d * Q4 d r) * Q4 d s) =
          Scalar d * (∫ s in (0 : Real)..min r (L d - r),
            Q4 d r * Q4 d s)
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const_mul]
        ring
      _ = Scalar d *
          (∫ r in (0 : Real)..L d,
            ∫ s in (0 : Real)..min r (L d - r), Q4 d r * Q4 d s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = Scalar d *
          sectionSixFirstLowCentralSmallI5P1D879Piece2WeightedSection d d := by
        rw [hweighted]
  rw [hw]
  rw [sectionSixFirstLowCentralSmallI5P1D879_piece2_weightedSection_eq_case2Area
    (ha := hd0) (hL0 := hL0)]
  rfl

private theorem d881_pointwise {y : (Real × Real) × Real} (hy : y ∈ S2) :
    F y ≤ Q y := by
  rcases y with ⟨⟨d, r⟩, s⟩
  have hy' : (d ∈ D2 ∧ r ∈ Set.Icc (0 : Real) (L d)) ∧
      s ∈ Set.Icc (0 : Real) (min r (L d - r)) := by
    simpa [S2, sectionSixFirstLowCentralSmallI5P1D823SOuter2,
      R2, sectionSixFirstLowCentralSmallI5P1D823ROuter2,
      D2, sectionSixFirstLowCentralSmallI5P1D823DOuter2,
      closedIccFiberCell] using hy
  have hrs : r + s ≤ L d := by
    have hsL := (le_min_iff.mp hy'.2.2).2
    linarith
  have hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1 := by
    simpa [D2, sectionSixFirstLowCentralSmallI5P1D823DOuter2] using hy'.1.1
  simpa [F, Q, Scalar, Beta, G,
    sectionSixFirstLowCentralSmallI5P1D823Fiber] using
    (sectionSixFirstLowCentralSmallI5P1D880_piece2_kernel_fiber_le_q4_self
      (hd := hd) (hr := hy'.1.2.1) (hs := hy'.2.1) (hrs := hrs))

theorem sectionSixFirstLowCentralSmallI5P1D881_piece2_integral_le_outerMajorant
    (_hMajorantInt :
      IntervalIntegrable
        sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant
        (volume : Measure Real)
        sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D807Piece2,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) ≤
      ∫ d in sectionSixFirstLowCentralSmallI5P1D807Dr..
        sectionSixFirstLowCentralSmallI5P1D807D1,
        sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant d := by
  have hmono := setIntegral_mono_on
    d881_actual_fiber_integrable d881_q4_integrable
    sectionSixFirstLowCentralSmallI5P1D823SOuter2_measurable
    (fun y hy => d881_pointwise hy)
  calc
    (∫ z in sectionSixFirstLowCentralSmallI5P1D807Piece2,
        sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ z in C2, K z ∂(volume : Measure SectionSixP1AffineT) := by
        rw [← sectionSixFirstLowCentralSmallI5P1D823_piece2Cell_eq_d807]
        rfl
    _ = ∫ y in S2, F y ∂(volume : Measure ((Real × Real) × Real)) :=
      d881_actual_fubini
    _ ≤ ∫ y in S2, Q y
        ∂(volume : Measure ((Real × Real) × Real)) := hmono
    _ = ∫ d in sectionSixFirstLowCentralSmallI5P1D807Dr..
          sectionSixFirstLowCentralSmallI5P1D807D1,
        sectionSixFirstLowCentralSmallI5P1D881Piece2OuterMajorant d :=
      d881_q4_set_eq_outer

end
end PrimesRestrictedDigits
