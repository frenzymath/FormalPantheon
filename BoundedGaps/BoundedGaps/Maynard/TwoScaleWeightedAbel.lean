import BoundedGaps.Maynard.NormalizedWeightedAbel

noncomputable section

/-!
Two-scale normalized partial summation.
Maynard2013v3, source lines 520--527, normalizes by the global radius while a
fixed off-coordinate product changes the scalar summation endpoint.
-/

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real

theorem intervalIntegral_normalizedLog_div_to
    {Q R : ℕ} (hQ : 1 < Q) (hR : 1 < R)
    {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ t in (1 : ℝ)..Q,
        G (Real.log t / Real.log R) / t) =
      Real.log R *
        ∫ x in (0 : ℝ)..(Real.log Q / Real.log R), G x := by
  have hQreal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hRreal : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRreal
  let q : ℝ → ℝ := fun t => Real.log t / Real.log R
  let q' : ℝ → ℝ := fun t => t⁻¹ / Real.log R
  have hxPos : ∀ x ∈ Set.uIcc (1 : ℝ) Q, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hQreal.le] at hx
    exact zero_lt_one.trans_le hx.1
  have hq : ∀ x ∈ Set.uIcc (1 : ℝ) Q, HasDerivAt q (q' x) x := by
    intro x hx
    exact (Real.hasDerivAt_log (hxPos x hx).ne').div_const (Real.log R)
  have hq' : ContinuousOn q' (Set.uIcc (1 : ℝ) Q) := by
    exact (continuousOn_id.inv₀ fun x hx => (hxPos x hx).ne').div_const _
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (1 : ℝ)) (b := (Q : ℝ)) hq hq' hG
  have hqOne : q 1 = 0 := by simp [q]
  have hqQ : q Q = Real.log Q / Real.log R := by rfl
  rw [hqOne, hqQ] at hsub
  calc
    (∫ t in (1 : ℝ)..Q, G (Real.log t / Real.log R) / t) =
        ∫ t in (1 : ℝ)..Q,
          Real.log R * ((G ∘ q) t * q' t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htPos := hxPos t ht
      dsimp [q, q']
      field_simp [hlogR.ne', htPos.ne']
    _ = Real.log R * ∫ t in (1 : ℝ)..Q, (G ∘ q) t * q' t := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.log R *
        ∫ x in (0 : ℝ)..(Real.log Q / Real.log R), G x := by
      rw [hsub]

theorem logarithmicAbelMain_normalizedLog_to_eq
    {Q R : ℕ} (hQ : 1 < Q) (hR : 1 < R)
    {S : ℝ} {G : ℝ → ℝ} (hG : Continuous G)
    (hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) Q,
      HasDerivAt (fun t => G (Real.log t / Real.log R))
        (deriv (fun t => G (Real.log t / Real.log R)) x) x)
    (hfDerivInt : IntervalIntegrable
      (deriv (fun t => G (Real.log t / Real.log R))) volume 1 Q) :
    logarithmicAbelMain Q S
        (fun t => G (Real.log t / Real.log R)) =
      S * Real.log R *
        ∫ x in (0 : ℝ)..(Real.log Q / Real.log R), G x := by
  let f : ℝ → ℝ := fun t => G (Real.log t / Real.log R)
  have hQreal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hqCont : ContinuousOn (fun t : ℝ => Real.log t / Real.log R)
      (Set.Icc (1 : ℝ) Q) := by
    apply (continuousOn_id.log fun x hx => (zero_lt_one.trans_le hx.1).ne').div_const
  have hf : ContinuousOn f (Set.Icc (1 : ℝ) Q) := hG.continuousOn.comp
    hqCont (fun x hx => Set.mem_univ _)
  have hfDeriv' : ∀ x ∈ Set.Icc (1 : ℝ) Q,
      HasDerivAt f (deriv f x) x := by
    simpa [f] using hfDeriv
  have hfDerivInt' : IntervalIntegrable (deriv f) volume 1 Q := by
    simpa [f] using hfDerivInt
  have hmain := logarithmicAbelMain_eq_intervalIntegral_div
    (R := Q) (S := S) (f := f) hQ.le hf hfDeriv' hfDerivInt'
  have hsub := intervalIntegral_normalizedLog_div_to hQ hR hG
  change logarithmicAbelMain Q S f = _
  rw [hmain]
  calc
    (∫ t in (1 : ℝ)..Q, f t * (S / t)) =
        S * ∫ t in (1 : ℝ)..Q, f t / t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    _ = S * (Real.log R *
        ∫ x in (0 : ℝ)..(Real.log Q / Real.log R), G x) := by
      rw [hsub]
    _ = S * Real.log R *
        ∫ x in (0 : ℝ)..(Real.log Q / Real.log R), G x := by ring

theorem abs_weightedSum_sub_twoScaleNormalizedLogIntegral_le
    {Q R : ℕ} (hQ : 1 < Q) (hR : 1 < R)
    {c : ℕ → ℝ} (hc : c 0 = 0)
    {S E V : ℝ} (hE : 0 ≤ E) {G : ℝ → ℝ} (hG : Continuous G)
    (hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) Q,
      HasDerivAt (fun t => G (Real.log t / Real.log R))
        (deriv (fun t => G (Real.log t / Real.log R)) x) x)
    (hfDerivInt : IntervalIntegrable
      (deriv (fun t => G (Real.log t / Real.log R))) volume 1 Q)
    (hfInt : IntegrableOn
      (deriv (fun t => G (Real.log t / Real.log R)))
      (Set.Icc (1 : ℝ) Q))
    (hfNormInt : IntegrableOn
      (fun t => |deriv (fun t => G (Real.log t / Real.log R)) t|)
      (Set.Ioc (1 : ℝ) Q))
    (hmainInt : IntegrableOn
      (fun t => deriv (fun t => G (Real.log t / Real.log R)) t *
        (S * Real.log t)) (Set.Ioc (1 : ℝ) Q))
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      |abelCumulative c t - S * Real.log t| ≤ E)
    (hvariation : (∫ t in Set.Ioc (1 : ℝ) Q,
      |deriv (fun t => G (Real.log t / Real.log R)) t|) ≤ V) :
    |(∑ k ∈ Finset.Icc 0 Q,
        G (Real.log k / Real.log R) * c k) -
        S * Real.log R *
          (∫ x in (0 : ℝ)..(Real.log Q / Real.log R), G x)| ≤
      E * (|G (Real.log Q / Real.log R)| + V) := by
  let f : ℝ → ℝ := fun t => G (Real.log t / Real.log R)
  have hAbel := abs_weightedSum_sub_logarithmicAbelMain_le
    (R := Q) hQ.le hc hE (f := f)
    (fun t ht => by simpa [f] using hfDeriv t ht)
    (by simpa [f] using hfInt)
    (by simpa [f] using hfNormInt)
    (by simpa [f] using hmainInt)
    happrox hvariation
  have hMain := logarithmicAbelMain_normalizedLog_to_eq
    (Q := Q) (R := R) (S := S) hQ hR hG hfDeriv hfDerivInt
  rw [hMain] at hAbel
  simpa [f] using hAbel

end BoundedGaps.Maynard
