import BoundedGaps.Maynard.WeightedSmoothAbel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

/-!
# Calculus identities for the logarithmic Abel main term

Integration by parts converts the endpoint-minus-derivative expression from
Abel summation into the logarithmic measure integral used by the smooth
summation lemma.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Real

theorem logarithmicAbelMain_eq_intervalIntegral_div
    {R : ℕ} (hR : 1 ≤ R) {S : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (1 : ℝ) R))
    (hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) R,
      HasDerivAt f (deriv f x) x)
    (hfDerivInt : IntervalIntegrable (deriv f) volume 1 R) :
    logarithmicAbelMain R S f =
      ∫ t in (1 : ℝ)..R, f t * (S / t) := by
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hxPos : ∀ x ∈ Set.Icc (1 : ℝ) R, 0 < x := by
    intro x hx
    exact zero_lt_one.trans_le hx.1
  have hv : ContinuousOn (fun t : ℝ => S * Real.log t)
      (Set.Icc (1 : ℝ) R) := by
    exact continuousOn_const.mul
      (continuousOn_id.log fun x hx => (hxPos x hx).ne')
  have hvDeriv : ∀ x ∈ Set.Icc (1 : ℝ) R,
      HasDerivAt (fun t : ℝ => S * Real.log t) (S / x) x := by
    intro x hx
    simpa [div_eq_mul_inv] using
      (Real.hasDerivAt_log (hxPos x hx).ne').const_mul S
  have hvDerivInt : IntervalIntegrable (fun t : ℝ => S / t) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hRreal]
    exact continuousOn_const.div continuousOn_id
      (fun x hx => (hxPos x hx).ne')
  have hfDerivU : ∀ x ∈ Set.uIcc (1 : ℝ) R,
      HasDerivAt f (deriv f x) x := by
    rw [Set.uIcc_of_le hRreal]
    exact hfDeriv
  have hvDerivU : ∀ x ∈ Set.uIcc (1 : ℝ) R,
      HasDerivAt (fun t : ℝ => S * Real.log t) (S / x) x := by
    rw [Set.uIcc_of_le hRreal]
    exact hvDeriv
  have hfU : ContinuousOn f (Set.uIcc (1 : ℝ) R) := by
    rw [Set.uIcc_of_le hRreal]
    exact hf
  have hvU : ContinuousOn (fun t : ℝ => S * Real.log t)
      (Set.uIcc (1 : ℝ) R) := by
    rw [Set.uIcc_of_le hRreal]
    exact hv
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    hfDerivU hvDerivU hfDerivInt hvDerivInt
  unfold logarithmicAbelMain
  rw [← intervalIntegral.integral_of_le hRreal]
  have hlogOne : S * Real.log (1 : ℝ) = 0 := by simp
  rw [hlogOne, mul_zero, sub_zero] at hparts
  rw [intervalIntegral.integral_add
    (hfDerivInt.mul_continuousOn hvU)
    (hvDerivInt.continuousOn_mul hfU)] at hparts
  calc
    f R * (S * Real.log R) -
        ∫ t in (1 : ℝ)..R, deriv f t * (S * Real.log t) =
      ∫ t in (1 : ℝ)..R, f t * (S / t) := by
        linarith [hparts]

theorem intervalIntegral_normalizedLog_div
    {R : ℕ} (hR : 1 < R) {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ t in (1 : ℝ)..R,
        G (Real.log t / Real.log R) / t) =
      Real.log R * ∫ x in (0 : ℝ)..1, G x := by
  have hRreal : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRreal
  let q : ℝ → ℝ := fun t => Real.log t / Real.log R
  let q' : ℝ → ℝ := fun t => t⁻¹ / Real.log R
  have hxPos : ∀ x ∈ Set.uIcc (1 : ℝ) R, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hRreal.le] at hx
    exact zero_lt_one.trans_le hx.1
  have hq : ∀ x ∈ Set.uIcc (1 : ℝ) R, HasDerivAt q (q' x) x := by
    intro x hx
    exact (Real.hasDerivAt_log (hxPos x hx).ne').div_const (Real.log R)
  have hq' : ContinuousOn q' (Set.uIcc (1 : ℝ) R) := by
    exact (continuousOn_id.inv₀ fun x hx => (hxPos x hx).ne').div_const _
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (1 : ℝ)) (b := (R : ℝ)) hq hq' hG
  have hqOne : q 1 = 0 := by simp [q]
  have hqR : q R = 1 := by simp [q, hlogR.ne']
  rw [hqOne, hqR] at hsub
  calc
    (∫ t in (1 : ℝ)..R, G (Real.log t / Real.log R) / t) =
        ∫ t in (1 : ℝ)..R,
          Real.log R * ((G ∘ q) t * q' t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htPos := hxPos t ht
      dsimp [q, q']
      field_simp [hlogR.ne', htPos.ne']
    _ = Real.log R * ∫ t in (1 : ℝ)..R, (G ∘ q) t * q' t := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.log R * ∫ x in (0 : ℝ)..1, G x := by rw [hsub]

theorem logarithmicAbelMain_normalizedLog_eq
    {R : ℕ} (hR : 1 < R) {S : ℝ} {G : ℝ → ℝ} (hG : Continuous G)
    (hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) R,
      HasDerivAt (fun t => G (Real.log t / Real.log R))
        (deriv (fun t => G (Real.log t / Real.log R)) x) x)
    (hfDerivInt : IntervalIntegrable
      (deriv (fun t => G (Real.log t / Real.log R))) volume 1 R) :
    logarithmicAbelMain R S
        (fun t => G (Real.log t / Real.log R)) =
      S * Real.log R * ∫ x in (0 : ℝ)..1, G x := by
  let f : ℝ → ℝ := fun t => G (Real.log t / Real.log R)
  have hRreal : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRreal
  have hqCont : ContinuousOn (fun t : ℝ => Real.log t / Real.log R)
      (Set.Icc (1 : ℝ) R) := by
    apply (continuousOn_id.log fun x hx => (zero_lt_one.trans_le hx.1).ne').div_const
  have hf : ContinuousOn f (Set.Icc (1 : ℝ) R) := hG.continuousOn.comp
    hqCont (fun x hx => Set.mem_univ _)
  have hfDeriv' : ∀ x ∈ Set.Icc (1 : ℝ) R,
      HasDerivAt f (deriv f x) x := by
    simpa [f] using hfDeriv
  have hfDerivInt' : IntervalIntegrable (deriv f) volume 1 R := by
    simpa [f] using hfDerivInt
  have hmain := logarithmicAbelMain_eq_intervalIntegral_div
    (S := S) (f := f) hR.le hf hfDeriv' hfDerivInt'
  have hsub := intervalIntegral_normalizedLog_div hR hG
  change logarithmicAbelMain R S f = _
  rw [hmain]
  calc
    (∫ t in (1 : ℝ)..R, f t * (S / t)) =
        S * ∫ t in (1 : ℝ)..R, f t / t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    _ = S * (Real.log R * ∫ x in (0 : ℝ)..1, G x) := by
      rw [hsub]
    _ = S * Real.log R * ∫ x in (0 : ℝ)..1, G x := by ring

end BoundedGaps.Maynard
