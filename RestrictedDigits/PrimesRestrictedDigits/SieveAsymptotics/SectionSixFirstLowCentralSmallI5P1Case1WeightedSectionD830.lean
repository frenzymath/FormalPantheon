import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1P1SelectedProvenanceD828
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Case1WeightedSectionD830 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

theorem sectionSixFirstLowCentralSmallI5P1D830_intervalIntegrable_sum
    {ι : Type} (s : Finset ι) (f : ι → Real → Real)
    {u v : Real}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume u v) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume u v := by
  exact (IntervalIntegrable.sum s hf).congr (by
    intro x hx
    simp [Finset.sum_apply])

theorem sectionSixFirstLowCentralSmallI5P1D830_monomial_integral
    (C l m h : Real) (i j k : Nat) :
    (∫ r in m..h, (C / (j + 1 : Real)) * l ^ (j + 1 - k) * r ^ (i + k)) =
      (C / ((j + 1 : Real) * (i + k + 1 : Real))) * l ^ (j + 1 - k) *
        (h ^ (i + k + 1) - m ^ (i + k + 1)) := by
  rw [intervalIntegral.integral_const_mul]
  rw [integral_pow]
  have hj : (0 : Real) < (j + 1 : Nat) := by positivity
  have hik : (0 : Real) < (i + k + 1 : Nat) := by positivity
  field_simp [ne_of_gt hj, ne_of_gt hik]
  norm_num [Nat.cast_add]

def sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperIntegrand
    (a d r : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D814Q4 a r *
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive a
      (sectionSixFirstLowCentralSmallI5P1D807L d - r)

def sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperExpanded
    (a d r : Real) : Real :=
  let l := sectionSixFirstLowCentralSmallI5P1D807L d
  ∑ i ∈ Finset.range 5,
    (∑ j ∈ Finset.range 5,
      (∑ k ∈ Finset.range (j + 2),
          (sectionSixFirstLowCentralSmallI5P1D828QCoeff a i *
              sectionSixFirstLowCentralSmallI5P1D828QCoeff a j *
            (j + 1 : Nat).choose k * (-1 : Real) ^ k /
              (j + 1 : Real)) *
          l ^ (j + 1 - k) * r ^ (i + k)))

theorem sectionSixFirstLowCentralSmallI5P1D830_p1Case1_upper_pointwise
    (a d r : Real) :
    sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperIntegrand a d r =
      sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperExpanded a d r := by
  simp [sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperIntegrand,
    sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperExpanded,
    sectionSixFirstLowCentralSmallI5P1D814Q4,
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive,
    sectionSixFirstLowCentralSmallI5P1D828QCoeff,
    sectionSixFirstLowCentralSmallI5P1D807L,
    Finset.sum_range_succ, Nat.choose]
  ring

def sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
    (a d : Real) : Real :=
  (sectionSixFirstLowCentralSmallI5P1D814Q4Primitive a
      (sectionSixFirstLowCentralSmallI5P1D807L d / 2)) ^ 2 / 2 +
    ∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
      sectionSixFirstLowCentralSmallI5P1D807H d,
      sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperIntegrand a d r

theorem sectionSixFirstLowCentralSmallI5P1D830_p1Case1_endpoint_order
    {d : Real}
    (hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr) :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D807L d / 2 ∧
      sectionSixFirstLowCentralSmallI5P1D807L d / 2 ≤
        sectionSixFirstLowCentralSmallI5P1D807H d ∧
      sectionSixFirstLowCentralSmallI5P1D807H d ≤
        sectionSixFirstLowCentralSmallI5P1D807L d := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  norm_num [sectionSixFirstLowCentralSmallI5P1D807L,
    sectionSixFirstLowCentralSmallI5P1D807H,
    sectionSixFirstLowCentralSmallI5P1D807A,
    sectionSixFirstLowCentralSmallI5P1D807Beta,
    sectionSixFirstLowCentralSmallI5P1D807Square,
    sectionSixFirstLowCentralSmallI5P1D807Ds,
    sectionSixFirstLowCentralSmallI5P1D807Dr,
    sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
    sectionSixThetaTwo] at hd ⊢
  constructor
  · linarith
  constructor <;> linarith

theorem sectionSixFirstLowCentralSmallI5P1D830_p1Case1_upper_integral_eq_sum
    (a d : Real) :
    (∫ r in sectionSixFirstLowCentralSmallI5P1D807L d / 2..
      sectionSixFirstLowCentralSmallI5P1D807H d,
      sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperIntegrand a d r) =
      ∑ i ∈ Finset.range 5,
        (∑ j ∈ Finset.range 5,
          (∑ k ∈ Finset.range (j + 2),
            (sectionSixFirstLowCentralSmallI5P1D828QCoeff a i *
                sectionSixFirstLowCentralSmallI5P1D828QCoeff a j *
              (j + 1 : Nat).choose k * (-1 : Real) ^ k /
                ((j + 1 : Real) * (i + k + 1 : Real))) *
              sectionSixFirstLowCentralSmallI5P1D807L d ^ (j + 1 - k) *
                (sectionSixFirstLowCentralSmallI5P1D807H d ^ (i + k + 1) -
                  (sectionSixFirstLowCentralSmallI5P1D807L d / 2) ^
                    (i + k + 1)))) := by
  rw [intervalIntegral.integral_congr (fun r hr =>
    sectionSixFirstLowCentralSmallI5P1D830_p1Case1_upper_pointwise a d r)]
  simp only [sectionSixFirstLowCentralSmallI5P1D830P1Case1UpperExpanded]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k hk
        simpa [mul_assoc] using
          sectionSixFirstLowCentralSmallI5P1D830_monomial_integral
            (sectionSixFirstLowCentralSmallI5P1D828QCoeff a i *
              sectionSixFirstLowCentralSmallI5P1D828QCoeff a j *
              (j + 1 : Nat).choose k * (-1 : Real) ^ k)
            (sectionSixFirstLowCentralSmallI5P1D807L d)
            (sectionSixFirstLowCentralSmallI5P1D807L d / 2)
            (sectionSixFirstLowCentralSmallI5P1D807H d) i j k
      · intro k hk
        have hc : Continuous (fun r : Real =>
            (sectionSixFirstLowCentralSmallI5P1D828QCoeff a i *
                sectionSixFirstLowCentralSmallI5P1D828QCoeff a j *
              (j + 1 : Nat).choose k * (-1 : Real) ^ k /
                (j + 1 : Real)) *
              sectionSixFirstLowCentralSmallI5P1D807L d ^ (j + 1 - k) *
                r ^ (i + k)) := by
          fun_prop
        exact hc.intervalIntegrable (μ := volume)
          (sectionSixFirstLowCentralSmallI5P1D807L d / 2)
          (sectionSixFirstLowCentralSmallI5P1D807H d)
    · intro j hj
      apply sectionSixFirstLowCentralSmallI5P1D830_intervalIntegrable_sum
      intro k hk
      have hc : Continuous (fun r : Real =>
          (sectionSixFirstLowCentralSmallI5P1D828QCoeff a i *
              sectionSixFirstLowCentralSmallI5P1D828QCoeff a j *
            (j + 1 : Nat).choose k * (-1 : Real) ^ k /
              (j + 1 : Real)) *
            sectionSixFirstLowCentralSmallI5P1D807L d ^ (j + 1 - k) *
              r ^ (i + k)) := by
        fun_prop
      exact hc.intervalIntegrable (μ := volume)
        (sectionSixFirstLowCentralSmallI5P1D807L d / 2)
        (sectionSixFirstLowCentralSmallI5P1D807H d)
  · intro i hi
    apply sectionSixFirstLowCentralSmallI5P1D830_intervalIntegrable_sum
    intro j hj
    apply sectionSixFirstLowCentralSmallI5P1D830_intervalIntegrable_sum
    intro k hk
    have hc : Continuous (fun r : Real =>
        (sectionSixFirstLowCentralSmallI5P1D828QCoeff a i *
            sectionSixFirstLowCentralSmallI5P1D828QCoeff a j *
          (j + 1 : Nat).choose k * (-1 : Real) ^ k /
            (j + 1 : Real)) *
          sectionSixFirstLowCentralSmallI5P1D807L d ^ (j + 1 - k) *
            r ^ (i + k)) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume)
      (sectionSixFirstLowCentralSmallI5P1D807L d / 2)
      (sectionSixFirstLowCentralSmallI5P1D807H d)

theorem sectionSixFirstLowCentralSmallI5P1D830_p1Case1_area_eq_D828_formula
    (d : Real) :
    sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
        sectionSixFirstLowCentralSmallI5P1D828P1SelectedAnchor d =
      sectionSixFirstLowCentralSmallI5P1D828P1SelectedFormula
        sectionSixFirstLowCentralSmallI5P1D828P1SelectedAnchor d := by
  unfold sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
  rw [sectionSixFirstLowCentralSmallI5P1D830_p1Case1_upper_integral_eq_sum]
  rfl


end
end PrimesRestrictedDigits
