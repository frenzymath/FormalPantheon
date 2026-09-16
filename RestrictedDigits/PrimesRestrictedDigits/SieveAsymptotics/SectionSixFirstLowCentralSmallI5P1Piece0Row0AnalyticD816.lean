import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1D814P0RowPolynomial
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0FubiniD815
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809
import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece0Row0AnalyticD816 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# transformed P1 Piece0 Row0 analytic helpers

This fixed-delta module proves the local Layer B analytic identities for the closed first
d-row. It exposes the kernel formula, linked tail wall, q4 primitive and triangular identity,
and reciprocal-square adapter. The eventual outer cap remains conditional on separately proved
majorant integrability and composition hypotheses; no source-region or aggregate claim is made
here.

Source: MAYNARD-PRD-PUBLISHED, Section 6, Eq. (6.12).
-/

abbrev sectionSixFirstLowCentralSmallI5P1D816Row0A : Real := 16249 / 125000
abbrev sectionSixFirstLowCentralSmallI5P1D816Row0B : Real := 208081 / 1600000
abbrev sectionSixFirstLowCentralSmallI5P1D816Row0Beta : Real := 212499 / 500000
abbrev sectionSixFirstLowCentralSmallI5P1D816Row0Gap : Real := 16249 / 250000
abbrev sectionSixFirstLowCentralSmallI5P1D816Row0C : Real := 16 / 25
abbrev sectionSixFirstLowCentralSmallI5P1D816Row0TailC : Real := 564383 / 1000000
abbrev sectionSixFirstLowCentralSmallI5P1D816Row0Q4 :=
  sectionSixFirstLowCentralSmallI5P1D814Q4
abbrev sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive :=
  sectionSixFirstLowCentralSmallI5P1D814Q4Primitive

private abbrev d816A : Real := sectionSixFirstLowCentralSmallI5P1D816Row0A
private abbrev d816B : Real := sectionSixFirstLowCentralSmallI5P1D816Row0B
private abbrev d816Beta : Real := sectionSixFirstLowCentralSmallI5P1D816Row0Beta
private abbrev d816Gap : Real := sectionSixFirstLowCentralSmallI5P1D816Row0Gap
private abbrev d816C : Real := sectionSixFirstLowCentralSmallI5P1D816Row0C
private abbrev d816TailC : Real := sectionSixFirstLowCentralSmallI5P1D816Row0TailC
private abbrev d816Q4 := sectionSixFirstLowCentralSmallI5P1D816Row0Q4
private abbrev d816Q4Primitive := sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive

def sectionSixFirstLowCentralSmallI5P1D816Row0Y
    (z : SectionSixP1AffineT) : Real :=
  (1 - sectionSixFirstLowCentralSmallI5P1D816Row0Beta - z.1.1.1 -
      z.1.1.2 - z.1.2 - z.2) / z.2

def sectionSixFirstLowCentralSmallI5P1D816Row0Kernel
    (z : SectionSixP1AffineT) : Real :=
  sectionSixFirstLowCentralSmallI5P1D809Kernel z

theorem sectionSixFirstLowCentralSmallI5P1D816_endpoint_identifications :
    sectionSixFirstLowCentralSmallI5P1D814P0Row0A =
        sectionSixFirstLowCentralSmallI5P1D816Row0A ∧
      sectionSixFirstLowCentralSmallI5P1D814P0Row0B =
        sectionSixFirstLowCentralSmallI5P1D816Row0B := by
  norm_num [sectionSixFirstLowCentralSmallI5P1D814P0Row0A,
    sectionSixFirstLowCentralSmallI5P1D814P0Row0B,
    sectionSixFirstLowCentralSmallI5P1D816Row0A,
    sectionSixFirstLowCentralSmallI5P1D816Row0B]

private theorem d816_row0_bounds {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0) :
    d816A ≤ z.1.1.1 ∧ z.1.1.1 ≤ d816B ∧
      0 ≤ z.1.1.2 ∧ z.1.1.2 ≤ (d816C - d816Beta - z.1.1.1) / 2 ∧
      0 ≤ z.1.2 ∧ z.1.2 ≤ z.1.1.2 ∧
      d816Gap ≤ z.2 ∧ z.2 ≤ z.1.1.1 - d816Gap := by
  have h := (sectionSixFirstLowCentralSmallI5P1D815_row0_mem_iff (z := z)).1 hz
  rcases h with ⟨⟨hd0, hd1⟩, ⟨hr0, hr1⟩, ⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩
  exact ⟨hd0, hd1, hr0, hr1, hs0, hs1, ht0, ht1⟩

theorem sectionSixFirstLowCentralSmallI5P1D816_kernel_formula
    (d r s t : Real) :
    sectionSixFirstLowCentralSmallI5P1D816Row0Kernel (((d, r), s), t) =
      buchstabFunction
          ((1 - sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d - r - s - t) / t) /
        ((sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d) *
          (d + r) * (d + s) * t ^ (2 : Nat)) := by
  unfold sectionSixFirstLowCentralSmallI5P1D816Row0Kernel
    sectionSixFirstLowCentralSmallI5P1D809Kernel
    sectionSixFirstLowCentralSmallQuadrupleKernel
    sectionSixP1SharpPhiD806
  simp only [Prod.fst_add, Prod.snd_add, zero_add]
  simp [sectionSixFirstLowCentralSmallI5P1D807Beta,
    sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaTwo]
  ring_nf

private theorem d816_row0_tail_wall {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0) :
    4 * (z.1.1.1 - d816Gap) ≤
      1 - d816Beta - z.1.1.1 - z.1.1.2 - z.1.2 := by
  rcases d816_row0_bounds hz with
    ⟨hd0, hd1, hr0, hrH, hs0, hsr, ht0, ht1⟩
  have hsum : z.1.1.2 + z.1.2 ≤
      d816C - d816Beta - z.1.1.1 := by
    norm_num [d816C, d816Beta] at hrH ⊢
    linarith
  have hdUpper : 2 * z.1.1.1 ≤
      (9 / 25 : Real) + 4 * d816Gap := by
    norm_num [d816B, d816Gap] at hd1 ⊢
    linarith
  norm_num [d816Beta, d816Gap] at *
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D816_row0_argument_ge_three
    {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0) :
    3 ≤ sectionSixFirstLowCentralSmallI5P1D816Row0Y z := by
  rcases d816_row0_bounds hz with
    ⟨hd0, hd1, hr0, hrH, hs0, hsr, ht0, ht1⟩
  have htail := d816_row0_tail_wall hz
  have htpos : 0 < z.2 := by
    norm_num [d816Gap] at ht0 ⊢
    linarith
  unfold sectionSixFirstLowCentralSmallI5P1D816Row0Y
  rw [le_div_iff₀ htpos]
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D816_row0_denominators_pos
    {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0) :
    0 < sectionSixFirstLowCentralSmallI5P1D816Row0Beta - z.1.1.1 ∧
      0 < z.1.1.1 + z.1.1.2 ∧
      0 < z.1.1.1 + z.1.2 ∧ 0 < z.2 := by
  rcases d816_row0_bounds hz with
    ⟨hd0, hd1, hr0, hrH, hs0, hsr, ht0, ht1⟩
  have hbetaB : d816B < d816Beta := by norm_num [d816B, d816Beta]
  have hApos : 0 < d816A := by norm_num [d816A]
  have hgapPos : 0 < d816Gap := by norm_num [d816Gap]
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D816_row0_tail_fiber_le
    {d r s : Real}
    (hd0 : sectionSixFirstLowCentralSmallI5P1D816Row0A ≤ d)
    (hd1 : d ≤ sectionSixFirstLowCentralSmallI5P1D816Row0B)
    (hr0 : 0 ≤ r) (hr1 : r ≤
      (sectionSixFirstLowCentralSmallI5P1D816Row0C -
        sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d) / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ r) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D816Row0Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D816Row0Gap),
      sectionSixFirstLowCentralSmallI5P1D816Row0Kernel (((d, r), s), t)) ≤
      sectionSixFirstLowCentralSmallI5P1D816Row0TailC /
          ((sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d) *
            (d + r) * (d + s)) *
        (1 / sectionSixFirstLowCentralSmallI5P1D816Row0Gap -
          1 / (d - sectionSixFirstLowCentralSmallI5P1D816Row0Gap)) := by
  have hbetaB : d816B < d816Beta := by
    norm_num [d816A, d816B, d816Beta]
  have hApos : 0 < d816A := by norm_num [d816A]
  have hgapPos : 0 < d816Gap := by norm_num [d816Gap]
  have hu : 0 < d816Beta - d := by linarith
  have hv : 0 < d + r := by linarith
  have hw : 0 < d + s := by linarith
  have hGh : d816Gap ≤ d - d816Gap := by
    norm_num [d816A, d816Gap] at hd0 ⊢
    linarith
  have hrs : r + s ≤ d816C - d816Beta - d := by
    norm_num [d816C, d816Beta] at hr1 ⊢
    linarith
  have htail : 4 * (d - d816Gap) ≤
      1 - d816Beta - d - r - s := by
    have hdUpper : 2 * d ≤ (9 / 25 : Real) + 4 * d816Gap := by
      norm_num [d816B, d816Gap] at hd1 ⊢
      linarith
    norm_num [d816Beta, d816Gap] at *
    linarith
  calc
    (∫ t in d816Gap..(d - d816Gap),
        sectionSixFirstLowCentralSmallI5P1D816Row0Kernel (((d, r), s), t)) =
      ∫ t in d816Gap..(d - d816Gap),
        buchstabFunction ((1 - d816Beta - d - r - s - t) / t) /
          ((d816Beta - d) * (d + r) * (d + s) * t ^ (2 : Nat)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact sectionSixFirstLowCentralSmallI5P1D816_kernel_formula d r s t
    _ ≤ d816TailC / ((d816Beta - d) * (d + r) * (d + s)) *
        (1 / d816Gap - 1 / (d - d816Gap)) := by
      simpa [d816Beta, d816Gap, d816TailC, div_eq_mul_inv, mul_assoc] using
        (integral_sectionSixBuchstabTailBranch_le
          (u := d816Beta - d) (v := d + r) (w := d + s)
          (B := 1 - d816Beta - d - r - s)
          (l := d816Gap) (h := d - d816Gap)
          hu hv hw hgapPos hGh htail)

theorem sectionSixFirstLowCentralSmallI5P1D816_row0_tail_fiber_of_mem
    {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D816Row0Gap..
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D816Row0Gap),
      sectionSixFirstLowCentralSmallI5P1D816Row0Kernel
        (((z.1.1.1, z.1.1.2), z.1.2), t)) ≤
      sectionSixFirstLowCentralSmallI5P1D816Row0TailC /
        ((sectionSixFirstLowCentralSmallI5P1D816Row0Beta - z.1.1.1) *
          (z.1.1.1 + z.1.1.2) * (z.1.1.1 + z.1.2)) *
        (1 / sectionSixFirstLowCentralSmallI5P1D816Row0Gap -
          1 / (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D816Row0Gap)) := by
  rcases d816_row0_bounds hz with
    ⟨hd0, hd1, hr0, hr1, hs0, hs1, ht0, ht1⟩
  exact sectionSixFirstLowCentralSmallI5P1D816_row0_tail_fiber_le
    hd0 hd1 hr0 hr1 hs0 hs1

theorem sectionSixFirstLowCentralSmallI5P1D816_q4_continuous
    (a : Real) : Continuous
      (sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a) := by
  unfold sectionSixFirstLowCentralSmallI5P1D816Row0Q4
    sectionSixFirstLowCentralSmallI5P1D814Q4
  fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D816_q4Primitive_hasDerivAt
    (a : Real) {x : Real} (ha : a ≠ 0) :
    HasDerivAt (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a)
      (sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a x) x := by
  unfold sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
    sectionSixFirstLowCentralSmallI5P1D816Row0Q4
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
    sectionSixFirstLowCentralSmallI5P1D814Q4
  have h0 := (hasDerivAt_id x).div_const a
  have h1 := ((hasDerivAt_id x).pow 2).div_const (2 * a ^ 2)
  have h2 := ((hasDerivAt_id x).pow 3).div_const (3 * a ^ 3)
  have h3 := ((hasDerivAt_id x).pow 4).div_const (4 * a ^ 4)
  have h4 := ((hasDerivAt_id x).pow 5).div_const (5 * a ^ 5)
  have h := (((h0.sub h1).add h2).sub h3).add h4
  convert h using 1
  all_goals try { rfl }
  norm_num [id_eq]
  field_simp [ha]

theorem sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive
    {a l u : Real} (ha : a ≠ 0) :
    (∫ x in l..u,
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a x) =
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a u -
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a l := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => sectionSixFirstLowCentralSmallI5P1D816_q4Primitive_hasDerivAt
      a ha)
    ((sectionSixFirstLowCentralSmallI5P1D816_q4_continuous a).intervalIntegrable l u)

theorem sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
    {a x : Real} (ha : 0 < a) (hx : 0 ≤ x) :
    1 / (a + x) ≤ sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a x := by
  have h := sectionSixFirstLowCentralSmallI5P1D814_q4_sub_inv ha hx
  have hr : 0 ≤ x ^ (5 : Nat) / (a ^ (5 : Nat) * (a + x)) := by
    positivity
  unfold sectionSixFirstLowCentralSmallI5P1D816Row0Q4
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D816_reciprocal_sq_interval
    {l u : Real} (hl : 0 < l) (hlu : l ≤ u) :
    (∫ x in l..u, 1 / x ^ (2 : Nat)) = 1 / l - 1 / u := by
  have hne : ∀ x ∈ Set.uIcc l u, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hlu] at hx
    exact (hl.trans_le hx.1).ne'
  have hderiv : ∀ x ∈ Set.uIcc l u,
      HasDerivAt (fun y : Real => -(y⁻¹)) (x ^ (2 : Nat))⁻¹ x := by
    intro x hx
    have h := (hasDerivAt_inv (hne x hx)).neg
    convert h using 1 <;> try rfl
    simp only [neg_neg]
  have hint : IntervalIntegrable (fun x : Real => (x ^ (2 : Nat))⁻¹)
      volume l u := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_id.pow 2).inv₀
      (fun x hx => pow_ne_zero 2 (hne x hx))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    (∫ x in l..u, 1 / x ^ (2 : Nat)) =
        ∫ x in l..u, (x ^ (2 : Nat))⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [one_div]
    _ = -u⁻¹ - -l⁻¹ := h
    _ = 1 / l - 1 / u := by simp only [one_div]; ring

theorem sectionSixFirstLowCentralSmallI5P1D816_triangular_q4
    {a H : Real} (ha : a ≠ 0) :
    (∫ r in 0..H,
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
      (∫ s in 0..r,
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a s)) =
      (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a H) ^ 2 / 2 := by
  have hinner : ∀ r : Real, (∫ s in 0..r,
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a s) =
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r -
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0 := by
    intro r
    exact sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive ha
  have hQ0 : sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0 = 0 := by
    simp [sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
      sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]
  simp_rw [hinner, hQ0, sub_zero]
  have hderiv : ∀ x : Real,
      HasDerivAt (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a)
        (sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a x) x := by
    intro x
    exact sectionSixFirstLowCentralSmallI5P1D816_q4Primitive_hasDerivAt a ha
  have hcomp :
      (∫ r in 0..H,
          ((sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a) ∘ id) r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r) =
        ∫ y in sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0..
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a H, id y := by
    apply intervalIntegral.integral_comp_mul_deriv (a := (0 : Real)) (b := H)
      (f := sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a)
      (f' := sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a) (g := id)
    · intro x hx
      exact hderiv x
    · exact (sectionSixFirstLowCentralSmallI5P1D816_q4_continuous a).continuousOn
    · fun_prop
  have hcomp' :
      (∫ r in 0..H,
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r) =
        ∫ y in sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0..
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a H, id y := by
    simpa only [Function.comp_apply, id_eq, mul_comm] using hcomp
  rw [hcomp']
  simp only [hQ0]
  change (∫ y in (0 : Real)..
      (sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a H), y) = _
  rw [integral_id]
  ring

theorem sectionSixFirstLowCentralSmallI5P1D816_Icc_to_interval
    {f : Real → Real}
    (hab : sectionSixFirstLowCentralSmallI5P1D816Row0A ≤
      sectionSixFirstLowCentralSmallI5P1D816Row0B) :
    (∫ d in Set.Icc sectionSixFirstLowCentralSmallI5P1D816Row0A
      sectionSixFirstLowCentralSmallI5P1D816Row0B,
      f d ∂(volume : Measure Real)) =
      ∫ d in sectionSixFirstLowCentralSmallI5P1D816Row0A..
        sectionSixFirstLowCentralSmallI5P1D816Row0B, f d := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le hab).symm

theorem sectionSixFirstLowCentralSmallI5P1D816_row0_cross_intervalIntegrable :
    IntervalIntegrable
      (fun d => sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly d)
      (volume : Measure Real)
      sectionSixFirstLowCentralSmallI5P1D816Row0A
      sectionSixFirstLowCentralSmallI5P1D816Row0B := by
  have hcont : Continuous
      (fun d => sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly d) := by
    unfold sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly
      sectionSixFirstLowCentralSmallI5P1D814FinPoly
    apply continuous_finsetSum
    intro i hi
    fun_prop
  exact hcont.intervalIntegrable _ _

theorem sectionSixFirstLowCentralSmallI5P1D816_row0_kernel_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D816Row0Kernel
      sectionSixFirstLowCentralSmallI5P1D815Row0
      (volume : Measure SectionSixP1AffineT) := by
  change IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
      sectionSixFirstLowCentralSmallI5P1D815Row0
      (volume : Measure SectionSixP1AffineT)
  exact sectionSixFirstLowCentralSmallI5P1D815_row0_kernel_integrable

end

end PrimesRestrictedDigits
