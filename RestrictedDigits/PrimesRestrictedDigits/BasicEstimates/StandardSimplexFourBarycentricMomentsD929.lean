import PrimesRestrictedDigits.BasicEstimates.StandardSimplexVolumeD904
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # StandardSimplexFourBarycentricMomentsD929 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

/-!
# Polynomial moments of the four barycentric coordinates

Exact moments on the closed standard three-dimensional simplex.

Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 140-147.
-/

private def d929Base : Set (Real × Real) :=
  closedIccFiberCell (Icc (0 : Real) 1)
    (fun _ : Real => 0) (fun x : Real => 1 - x)

private def d929Simplex : Set ((Real × Real) × Real) :=
  closedIccFiberCell d929Base
    (fun _ : Real × Real => 0)
    (fun x : Real × Real => 1 - x.1 - x.2)

private theorem d929Simplex_eq_standardSimplex3 :
    d929Simplex = standardSimplex3 := by rfl

private theorem segment_recurrence929 (a b : ℕ) (L : ℝ) :
    (∫ y in (0 : ℝ)..L, y ^ (a + 1) * (L - y) ^ b) =
      ((a + 1 : ℝ) / (b + 1)) *
        (∫ y in (0 : ℝ)..L, y ^ a * (L - y) ^ (b + 1)) := by
  have hu : ∀ x ∈ uIcc (0 : ℝ) L,
      HasDerivAt (fun y : ℝ => y ^ (a + 1)) ((a + 1) * x ^ a) x := by
    intro x hx
    have h := (hasDerivAt_id x).pow (a + 1)
    change HasDerivAt (fun y : ℝ => y ^ (a + 1)) _ x at h
    simpa [id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one] using h
  have hv : ∀ x ∈ uIcc (0 : ℝ) L,
      HasDerivAt (fun y : ℝ => -(L - y) ^ (b + 1) / (b + 1 : ℝ))
        ((L - x) ^ b) x := by
    intro x hx
    have hsub : HasDerivAt (fun y : ℝ => L - y) (-1 : ℝ) x := by
      have h := (hasDerivAt_const x L).sub (hasDerivAt_id x)
      change HasDerivAt (fun y : ℝ => L - y) _ x at h
      simpa using h
    have hp := hsub.pow (b + 1)
    have hc := hp.neg.div_const (b + 1 : ℝ)
    change HasDerivAt (fun y : ℝ => -(L - y) ^ (b + 1) / (b + 1 : ℝ)) _ x at hc
    have hc' : HasDerivAt (fun y : ℝ => -(L - y) ^ (b + 1) / (b + 1 : ℝ))
        (-((b + 1 : ℝ) * (L - x) ^ (b + 1 - 1) * (-1)) / (b + 1 : ℝ)) x := by
      simpa only [Nat.cast_add, Nat.cast_one] using hc
    convert hc' using 1
    norm_num [Nat.add_sub_cancel]
    field_simp
  have hu' : IntervalIntegrable (fun x : ℝ => (a + 1 : ℝ) * x ^ a) volume 0 L := by
    exact (continuousOn_const.mul (continuousOn_id.pow a)).intervalIntegrable
  have hv' : IntervalIntegrable (fun x : ℝ => (L - x) ^ b) volume 0 L := by
    exact ((continuousOn_const.sub continuousOn_id).pow b).intervalIntegrable
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hzero : (0 : ℝ) ^ (a + 1) = 0 := by simp
  simp [hzero] at h
  calc
    (∫ y in (0 : ℝ)..L, y ^ (a + 1) * (L - y) ^ b) =
        -(∫ y in (0 : ℝ)..L,
          (a + 1 : ℝ) * y ^ a * (-(L - y) ^ (b + 1) / (b + 1 : ℝ))) := h
    _ = ((a + 1 : ℝ) / (b + 1 : ℝ)) *
          (∫ y in (0 : ℝ)..L, y ^ a * (L - y) ^ (b + 1)) := by
      rw [show (fun y : ℝ =>
          (a + 1 : ℝ) * y ^ a * (-(L - y) ^ (b + 1) / (b + 1 : ℝ))) =
          (fun y => -((a + 1 : ℝ) / (b + 1 : ℝ)) *
            (y ^ a * (L - y) ^ (b + 1))) by
          funext y; ring]
      rw [intervalIntegral.integral_const_mul]
      ring

private theorem segment_base929 (b : ℕ) (L : ℝ) :
    (∫ y in (0 : ℝ)..L, (L - y) ^ b) = L ^ (b + 1) / (b + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun y : ℝ => y ^ b) L]
  rw [integral_pow]
  simp

private theorem segment_moment929 (a b : ℕ) (L : ℝ) :
    (∫ y in (0 : ℝ)..L, y ^ a * (L - y) ^ b) =
      ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) /
        (Nat.factorial (a + b + 1) : ℝ)) * L ^ (a + b + 1) := by
  induction a generalizing b L with
  | zero =>
      rw [Nat.factorial_zero]
      convert segment_base929 b L using 1
      · simp
      · rw [Nat.factorial_succ]
        field_simp
        norm_num
        ring
  | succ a ih =>
      rw [segment_recurrence929 a b L, ih (b := b + 1) (L := L)]
      have h₁ : a + (b + 1) + 1 = a + b + 2 := by omega
      have h₂ : a + 1 + b + 1 = a + b + 2 := by omega
      rw [h₁, h₂]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp

private theorem d929Base_measurable : MeasurableSet d929Base := by
  apply measurableSet_closedIccFiberCell
  · exact measurableSet_Icc
  · fun_prop
  · fun_prop

private theorem d929Simplex_subset_box :
    d929Simplex ⊆ ((Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) ×ˢ Icc (0 : Real) 1) := by
  intro z hz
  change z.1 ∈ d929Base ∧ z.2 ∈ Icc (0 : Real) (1 - z.1.1 - z.1.2) at hz
  dsimp [d929Base, closedIccFiberCell] at hz
  change ((z.1.1 ∈ Icc (0 : Real) 1 ∧
      z.1.2 ∈ Icc (0 : Real) (1 - z.1.1)) ∧
      z.2 ∈ Icc (0 : Real) (1 - z.1.1 - z.1.2)) at hz
  change ((z.1.1 ∈ Icc (0 : Real) 1 ∧ z.1.2 ∈ Icc (0 : Real) 1) ∧
      z.2 ∈ Icc (0 : Real) 1)
  refine ⟨⟨hz.1.1, ?_⟩, ?_⟩
  · exact ⟨hz.1.2.1, by linarith [hz.1.2.2, hz.1.1.1]⟩
  · exact ⟨hz.2.1, by linarith [hz.2.2, hz.1.1.1, hz.1.2.1]⟩

private theorem d929Simplex_integrable (a0 a1 a2 a3 : ℕ) :
    IntegrableOn
      (fun z : ((Real × Real) × Real) =>
        (1 - z.1.1 - z.1.2 - z.2) ^ a0 * z.1.1 ^ a1 *
          z.1.2 ^ a2 * z.2 ^ a3)
      d929Simplex (volume.prod volume) := by
  have hc : IsCompact
      (((Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) ×ˢ Icc (0 : Real) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcont : ContinuousOn
      (fun z : ((Real × Real) × Real) =>
        (1 - z.1.1 - z.1.2 - z.2) ^ a0 * z.1.1 ^ a1 *
          z.1.2 ^ a2 * z.2 ^ a3)
      (((Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) ×ˢ Icc (0 : Real) 1)) := by
    fun_prop
  apply hcont.integrableOn_compact hc |>.mono_set
  exact d929Simplex_subset_box

theorem standardSimplex3_fourBarycentricMoment_D929 (a0 a1 a2 a3 : Nat) :
    (∫ z in standardSimplex3,
      (1 - z.1.1 - z.1.2 - z.2) ^ a0 * z.1.1 ^ a1 *
        z.1.2 ^ a2 * z.2 ^ a3
      ∂((volume : Measure (Real × Real)).prod (volume : Measure Real))) =
      (((a0.factorial : Nat) : Real) * ((a1.factorial : Nat) : Real) *
        ((a2.factorial : Nat) : Real) * ((a3.factorial : Nat) : Real)) /
        (((a0 + a1 + a2 + a3 + 3).factorial : Nat) : Real) := by
  rw [← d929Simplex_eq_standardSimplex3]
  have hfint := d929Simplex_integrable a0 a1 a2 a3
  unfold d929Simplex
  rw [setIntegral_closedIccFiberCell_eq_iterated
    d929Base
    (fun _ : Real × Real => 0)
    (fun x : Real × Real => 1 - x.1 - x.2)
    (fun z : ((Real × Real) × Real) =>
      (1 - z.1.1 - z.1.2 - z.2) ^ a0 * z.1.1 ^ a1 *
        z.1.2 ^ a2 * z.2 ^ a3)
    d929Base_measurable (by fun_prop) (by fun_prop)
    (by
      intro x hx
      change x.1 ∈ Icc (0 : Real) 1 ∧ x.2 ∈ Icc (0 : Real) (1 - x.1) at hx
      exact sub_nonneg.mpr (by linarith [hx.2.2]))
    hfint]
  have hinner : ∀ x : Real × Real,
      (∫ t in (0 : Real)..(1 - x.1 - x.2),
        (1 - x.1 - x.2 - t) ^ a0 * x.1 ^ a1 *
          x.2 ^ a2 * t ^ a3) =
        x.1 ^ a1 * x.2 ^ a2 *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real)) *
          (1 - x.1 - x.2) ^ (a3 + a0 + 1) := by
    intro x
    rw [show (fun t : Real =>
        (1 - x.1 - x.2 - t) ^ a0 * x.1 ^ a1 * x.2 ^ a2 * t ^ a3) =
        (fun t => (x.1 ^ a1 * x.2 ^ a2) *
          (t ^ a3 * ((1 - x.1 - x.2) - t) ^ a0)) by
          funext t; ring, intervalIntegral.integral_const_mul]
    rw [segment_moment929 a3 a0 (1 - x.1 - x.2)]
    ring
  rw [show (∫ x in d929Base,
      (∫ t in (0 : Real)..(1 - x.1 - x.2),
        (1 - x.1 - x.2 - t) ^ a0 * x.1 ^ a1 *
          x.2 ^ a2 * t ^ a3)) =
      (∫ x in d929Base,
        x.1 ^ a1 * x.2 ^ a2 *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real)) *
          (1 - x.1 - x.2) ^ (a3 + a0 + 1)) by
        apply setIntegral_congr_fun d929Base_measurable
        intro x hx
        exact hinner x]
  change (∫ x in closedIccFiberCell (Icc (0 : Real) 1)
      (fun _ : Real => 0) (fun x : Real => 1 - x),
      x.1 ^ a1 * x.2 ^ a2 *
        ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
          (Nat.factorial (a3 + a0 + 1) : Real)) *
        (1 - x.1 - x.2) ^ (a3 + a0 + 1)
      ∂(volume.prod volume)) = _
  have hbaseint : IntegrableOn
      (fun x : Real × Real =>
        x.1 ^ a1 * x.2 ^ a2 *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real)) *
          (1 - x.1 - x.2) ^ (a3 + a0 + 1))
      d929Base (volume.prod volume) := by
    have hcont : ContinuousOn
        (fun x : Real × Real =>
          x.1 ^ a1 * x.2 ^ a2 *
            ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
              (Nat.factorial (a3 + a0 + 1) : Real)) *
            (1 - x.1 - x.2) ^ (a3 + a0 + 1))
        (Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1) := by
      fun_prop
    apply hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) |>.mono_set
    intro x hx
    dsimp [d929Base, closedIccFiberCell] at hx
    change x.1 ∈ Icc (0 : Real) 1 ∧ x.2 ∈ Icc (0 : Real) (1 - x.1) at hx
    change x.1 ∈ Icc (0 : Real) 1 ∧ x.2 ∈ Icc (0 : Real) 1
    exact ⟨hx.1, ⟨hx.2.1, by linarith [hx.2.2, hx.1.1]⟩⟩
  rw [setIntegral_closedIccFiberCell_eq_iterated
    (Icc (0 : Real) 1) (fun _ : Real => 0) (fun x : Real => 1 - x)
    (fun x : Real × Real =>
      x.1 ^ a1 * x.2 ^ a2 *
        ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
          (Nat.factorial (a3 + a0 + 1) : Real)) *
        (1 - x.1 - x.2) ^ (a3 + a0 + 1))
    measurableSet_Icc (by fun_prop) (by fun_prop)
    (by intro x hx; linarith [hx.2]) hbaseint]
  change (∫ x in Icc (0 : Real) 1,
      (∫ y in (0 : Real)..(1 - x),
        x ^ a1 * y ^ a2 *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real)) *
          (1 - x - y) ^ (a3 + a0 + 1))) = _
  have hy : ∀ x : Real,
      (∫ y in (0 : Real)..(1 - x),
        x ^ a1 * y ^ a2 *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real)) *
          (1 - x - y) ^ (a3 + a0 + 1)) =
      x ^ a1 *
        ((Nat.factorial a2 : Real) * (Nat.factorial (a3 + a0 + 1) : Real) /
          (Nat.factorial (a2 + a3 + a0 + 2) : Real)) *
        ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
          (Nat.factorial (a3 + a0 + 1) : Real)) *
        (1 - x) ^ (a2 + a3 + a0 + 2) := by
    intro x
    rw [show (fun y : Real =>
        x ^ a1 * y ^ a2 *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real)) *
          (1 - x - y) ^ (a3 + a0 + 1)) =
        (fun y => (x ^ a1 *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real))) *
          (y ^ a2 * ((1 - x) - y) ^ (a3 + a0 + 1))) by
          funext y; ring, intervalIntegral.integral_const_mul]
    rw [segment_moment929 a2 (a3 + a0 + 1) (1 - x)]
    rw [show a2 + (a3 + a0 + 1) + 1 = a2 + a3 + a0 + 2 by omega]
    ring
  rw [show (∫ x in Icc (0 : Real) 1,
      (∫ y in (0 : Real)..(1 - x),
        x ^ a1 * y ^ a2 *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real)) *
          (1 - x - y) ^ (a3 + a0 + 1))) =
      (∫ x in Icc (0 : Real) 1,
        x ^ a1 *
          ((Nat.factorial a2 : Real) * (Nat.factorial (a3 + a0 + 1) : Real) /
            (Nat.factorial (a2 + a3 + a0 + 2) : Real)) *
          ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
            (Nat.factorial (a3 + a0 + 1) : Real)) *
          (1 - x) ^ (a2 + a3 + a0 + 2)) by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact hy x]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  rw [show (fun x : Real =>
      x ^ a1 *
        ((Nat.factorial a2 : Real) * (Nat.factorial (a3 + a0 + 1) : Real) /
          (Nat.factorial (a2 + a3 + a0 + 2) : Real)) *
        ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
          (Nat.factorial (a3 + a0 + 1) : Real)) *
        (1 - x) ^ (a2 + a3 + a0 + 2)) =
      (fun x => (((Nat.factorial a2 : Real) * (Nat.factorial (a3 + a0 + 1) : Real) /
          (Nat.factorial (a2 + a3 + a0 + 2) : Real)) *
        ((Nat.factorial a3 : Real) * (Nat.factorial a0 : Real) /
          (Nat.factorial (a3 + a0 + 1) : Real)) *
        (x ^ a1 * (1 - x) ^ (a2 + a3 + a0 + 2)))) by funext x; ring,
    intervalIntegral.integral_const_mul]
  rw [segment_moment929 a1 (a2 + a3 + a0 + 2) 1]
  rw [show a1 + (a2 + a3 + a0 + 2) + 1 = a0 + a1 + a2 + a3 + 3 by omega]
  simp only [one_pow]
  field_simp

end
end PrimesRestrictedDigits
