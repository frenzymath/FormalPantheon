import Mathlib.NumberTheory.AbelSummation

noncomputable section

/-!
# Quantitative Abel transfer for smooth weighted sums

This separates the calculus part of the weighted summation lemma from its
multiplicative summatory estimate.  A uniform error for the cumulative weight
transfers to a weighted sum with loss given by the endpoint and total
variation of the test function.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real

noncomputable def abelCumulative (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k

noncomputable def logarithmicAbelMain
    (R : ℕ) (S : ℝ) (f : ℝ → ℝ) : ℝ :=
  f R * (S * Real.log R) -
    ∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (S * Real.log t)

theorem abs_weightedSum_sub_logarithmicAbelMain_le
    {R : ℕ} (hR : 1 ≤ R) {c : ℕ → ℝ} (hc : c 0 = 0)
    {S E V : ℝ} (hE : 0 ≤ E)
    {f : ℝ → ℝ}
    (hfDiff : ∀ t ∈ Set.Icc (1 : ℝ) R, DifferentiableAt ℝ f t)
    (hfInt : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) R))
    (hfNormInt : IntegrableOn
      (fun t => |deriv f t|) (Set.Ioc (1 : ℝ) R))
    (hmainInt : IntegrableOn
      (fun t => deriv f t * (S * Real.log t)) (Set.Ioc (1 : ℝ) R))
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) R,
      |abelCumulative c t - S * Real.log t| ≤ E)
    (hvariation : (∫ t in Set.Ioc (1 : ℝ) R, |deriv f t|) ≤ V) :
    |(∑ k ∈ Finset.Icc 0 R, f k * c k) -
        logarithmicAbelMain R S f| ≤ E * (|f R| + V) := by
  let A : ℝ → ℝ := abelCumulative c
  let B : ℝ → ℝ := fun t => S * Real.log t
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hactualInt : IntegrableOn
      (fun t => deriv f t * A t) (Set.Ioc (1 : ℝ) R) := by
    apply (integrableOn_mul_sum_Icc (m := 0) c zero_le_one hfInt).mono_set
    exact Set.Ioc_subset_Icc_self
  have hmainIntB : IntegrableOn
      (fun t => deriv f t * B t) (Set.Ioc (1 : ℝ) R) := by
    simpa [B] using hmainInt
  have herrorInt : IntegrableOn
      (fun t => deriv f t * (A t - B t)) (Set.Ioc (1 : ℝ) R) := by
    convert hactualInt.sub hmainIntB using 1
    funext t
    dsimp [B]
    ring
  have hmajorant : IntegrableOn
      (fun t => |deriv f t| * E) (Set.Ioc (1 : ℝ) R) :=
    hfNormInt.mul_const E
  have hpoint : ∀ t ∈ Set.Ioc (1 : ℝ) R,
      |deriv f t * (A t - B t)| ≤ |deriv f t| * E := by
    intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (happrox t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)
  have hintegral :
      |∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (A t - B t)| ≤
        E * V := by
    calc
      |∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (A t - B t)| ≤
          ∫ t in Set.Ioc (1 : ℝ) R,
            |deriv f t * (A t - B t)| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioc (1 : ℝ) R, |deriv f t| * E := by
        apply integral_mono_ae herrorInt.norm hmajorant
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        simpa only [Real.norm_eq_abs] using hpoint t ht
      _ = E * (∫ t in Set.Ioc (1 : ℝ) R, |deriv f t|) := by
        rw [integral_mul_const]
        ring
      _ ≤ E * V := mul_le_mul_of_nonneg_left hvariation hE
  have hendpoint := happrox (R : ℝ) ⟨hRreal, le_rfl⟩
  rw [sum_mul_eq_sub_integral_mul₀' c hc R hfDiff hfInt]
  unfold logarithmicAbelMain
  rw [show (∑ k ∈ Finset.Icc 0 R, c k) = A R by
    simp [A, abelCumulative]]
  change |(f R * A R - ∫ t in Set.Ioc (1 : ℝ) R, deriv f t * A t) -
      (f R * B R - ∫ t in Set.Ioc (1 : ℝ) R, deriv f t * B t)| ≤ _
  have hint :
      (∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (A t - B t)) =
        (∫ t in Set.Ioc (1 : ℝ) R, deriv f t * A t) -
          ∫ t in Set.Ioc (1 : ℝ) R, deriv f t * B t := by
    calc
      (∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (A t - B t)) =
          ∫ t in Set.Ioc (1 : ℝ) R,
            deriv f t * A t - deriv f t * B t := by
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ = _ := integral_sub hactualInt hmainIntB
  have hdecomp :
      (f R * A R - ∫ t in Set.Ioc (1 : ℝ) R, deriv f t * A t) -
          (f R * B R - ∫ t in Set.Ioc (1 : ℝ) R, deriv f t * B t) =
        f R * (A R - B R) -
          ∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (A t - B t) := by
    rw [hint]
    ring
  rw [hdecomp]
  calc
    |f R * (A R - B R) -
        ∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (A t - B t)| ≤
      |f R| * |A R - B R| +
        |∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (A t - B t)| := by
      simpa [abs_mul] using abs_sub (f R * (A R - B R))
        (∫ t in Set.Ioc (1 : ℝ) R, deriv f t * (A t - B t))
    _ ≤ |f R| * E + E * V := add_le_add
      (mul_le_mul_of_nonneg_left hendpoint (abs_nonneg _)) hintegral
    _ = E * (|f R| + V) := by ring

end BoundedGaps.Maynard
