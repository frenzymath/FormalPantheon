import BoundedGaps.Maynard.LogarithmicAbelMain

noncomputable section

/-!
Normalized smooth partial summation for the S2 coordinate fiber.
Maynard2013v3, source lines 520--527, applies this Abel transfer after the
scalar fiber has been isolated.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real

theorem abs_weightedSum_sub_normalizedLogIntegral_le
    {R : ℕ} (hR : 1 < R) {c : ℕ → ℝ} (hc : c 0 = 0)
    {S E V : ℝ} (hE : 0 ≤ E) {G : ℝ → ℝ} (hG : Continuous G)
    (hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) R,
      HasDerivAt (fun t => G (Real.log t / Real.log R))
        (deriv (fun t => G (Real.log t / Real.log R)) x) x)
    (hfDerivInt : IntervalIntegrable
      (deriv (fun t => G (Real.log t / Real.log R))) volume 1 R)
    (hfInt : IntegrableOn
      (deriv (fun t => G (Real.log t / Real.log R)))
      (Set.Icc (1 : ℝ) R))
    (hfNormInt : IntegrableOn
      (fun t => |deriv (fun t => G (Real.log t / Real.log R)) t|)
      (Set.Ioc (1 : ℝ) R))
    (hmainInt : IntegrableOn
      (fun t => deriv (fun t => G (Real.log t / Real.log R)) t *
        (S * Real.log t)) (Set.Ioc (1 : ℝ) R))
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) R,
      |abelCumulative c t - S * Real.log t| ≤ E)
    (hvariation : (∫ t in Set.Ioc (1 : ℝ) R,
      |deriv (fun t => G (Real.log t / Real.log R)) t|) ≤ V) :
    |(∑ k ∈ Finset.Icc 0 R,
        G (Real.log k / Real.log R) * c k) -
        S * Real.log R * (∫ x in (0 : ℝ)..1, G x)| ≤
      E * (|G 1| + V) := by
  let f : ℝ → ℝ := fun t => G (Real.log t / Real.log R)
  have hAbel := abs_weightedSum_sub_logarithmicAbelMain_le
    (R := R) hR.le hc hE (f := f)
    (fun t ht => by simpa [f] using hfDeriv t ht)
    (by simpa [f] using hfInt)
    (by simpa [f] using hfNormInt)
    (by simpa [f] using hmainInt)
    happrox hvariation
  have hMain := logarithmicAbelMain_normalizedLog_eq
    (R := R) (S := S) hR hG hfDeriv hfDerivInt
  rw [hMain] at hAbel
  have hlogR : Real.log (R : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast hR)).ne'
  have harg : Real.log (R : ℝ) / Real.log R = 1 := by
    field_simp [hlogR]
  simpa [f, harg] using hAbel

end BoundedGaps.Maynard
