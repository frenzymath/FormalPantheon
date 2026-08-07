import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLocalCancellation
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldFourFactorClosedStrip
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldMellinStripDecay

/-!
# Goldfeld horizontal-edge decay

The closed-strip growth and Mellin estimates are combined on the real-part
interval `[-1,2]`.  The filled numerator supplies interval integrability; on
the nonzero high horizontal lines it agrees with the raw contour integrand.
The left-to-right lower integral is kept separate from the positively
oriented contour side, whose later consumer inserts a minus sign.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 58, 74,
125--127, especially (5.13), (7.9), and the proof of Theorem 12.9.
Semantic review: `SEM-557`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set Filter
open scoped Interval Topology

noncomputable section

private lemma goldfeld_mul_decay_bound
    {q u x C : ℝ} {A : ℕ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (_hx : 0 ≤ x) (hC : 0 ≤ C) :
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 ≤
      (C * (2 : ℝ) ^ A) * q ^ A * x ^ 2 / (1 + u) ^ 2 := by
  have hbase : u + 2 ≤ 2 * (1 + u) := by linarith
  have hpow : (u + 2) ^ A ≤ (2 * (1 + u)) ^ A :=
    pow_le_pow_left₀ (by linarith) hbase A
  have hqpow : 0 ≤ q ^ A := pow_nonneg hq A
  have hprod :
      q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 ≤
        q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x ^ 2 := by
    gcongr
  calc
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 =
        q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 := by
      rw [mul_pow]
    _ ≤ q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x ^ 2 := hprod
    _ = (C * (2 : ℝ) ^ A) * q ^ A * x ^ 2 / (1 + u) ^ 2 := by
      rw [mul_pow]
      field_simp
      ring

private theorem norm_goldfeldContourIntegrand_horizontal_le_of_bounds
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    {A : ℕ} {Cphi beta x sigma t : ℝ}
    (hx : 1 ≤ x)
    (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2) (ht : 1 ≤ |t|)
    (hF : ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ ≤
      ((q : ℝ) * (|t| + 2)) ^ A)
    (hPhi : ‖goldfeldMellinContinuationData.Phi
        ((sigma : ℂ) + t * I)‖ ≤ Cphi / (1 + |t|) ^ (A + 2))
    (hCphi : 0 ≤ Cphi) :
    ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + t * I)‖ ≤
      (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A * x ^ 2 /
        (1 + |t|) ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsigmaPow : x ^ sigma ≤ x ^ (2 : ℕ) := by
    calc
      x ^ sigma ≤ x ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx hsigma.2
      _ = x ^ (2 : ℕ) := Real.rpow_two x
  have hpowprod := goldfeld_mul_decay_bound (A := A) hq0 (abs_nonneg t)
    (by positivity : 0 ≤ x) hCphi
  have hcpow : ‖(x : ℂ) ^ ((sigma : ℂ) + t * I)‖ = x ^ sigma := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp
  rw [goldfeldContourIntegrand, norm_mul, norm_mul, hcpow]
  calc
    ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ *
        ‖goldfeldMellinContinuationData.Phi ((sigma : ℂ) + t * I)‖ *
        x ^ sigma ≤
      ((q : ℝ) * (|t| + 2)) ^ A *
        (Cphi / (1 + |t|) ^ (A + 2)) * x ^ 2 := by
      calc
        _ ≤
            ‖goldfeldFourFactorLFunction chi1 chi
                (((sigma : ℂ) + t * I) + (beta : ℂ))‖ *
              ‖goldfeldMellinContinuationData.Phi ((sigma : ℂ) + t * I)‖ *
              x ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hsigmaPow
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ _ := by
          gcongr
    _ ≤ (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A * x ^ 2 /
          (1 + |t|) ^ 2 := hpowprod

/-- One absolute exponent and one absolute constant bound the raw integrand on
both signed high horizontal lines. -/
theorem exists_norm_goldfeldContourIntegrand_horizontal_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x sigma t : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            sigma ∈ Icc (-(1 : ℝ)) 2 → 1 ≤ |t| →
            ‖goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) + t * I)‖ ≤
              C * (q : ℝ) ^ A * x ^ 2 / (1 + |t|) ^ 2 := by
  obtain ⟨A, hA, hF⟩ :=
    exists_norm_goldfeldFourFactorLFunction_closedStrip_le_pow
  obtain ⟨Cphi, hCphi, hPhi⟩ :=
    goldfeldMellinContinuation_decay_on_closedStrip (A + 2) (by omega)
  let C : ℝ := Cphi * (2 : ℝ) ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x sigma t hbeta0 hbeta1 hx hsigma ht
  have him : (((sigma : ℂ) + t * I).im) = t := by simp
  have hF' : ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ ≤
      ((q : ℝ) * (|t| + 2)) ^ A := by
    have h := hF q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta ((sigma : ℂ) + t * I) hbeta0 hbeta1
        (by simpa using hsigma.1) (by simpa using hsigma.2)
        (by simpa [him] using ht)
    simpa [him] using h
  have hPhi' := hPhi sigma t hsigma ht
  have hpoint := norm_goldfeldContourIntegrand_horizontal_le_of_bounds
    (A := A) (q := q) (chi1 := chi1) (chi := chi)
    hx hsigma ht hF' hPhi' hCphi.le
  simpa [C, mul_assoc, mul_left_comm, mul_comm] using hpoint

private theorem continuous_goldfeldRegularizedContourIntegrand_horizontal_plus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    Continuous (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
      chi1 chi beta x ((sigma : ℂ) + T * I)) := by
  have hpath : Continuous (fun sigma : ℝ => (sigma : ℂ) + T * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hnum : Continuous (goldfeldContourNumerator chi1 chi beta x) :=
    (differentiable_goldfeldContourNumerator hchi1 hchi hcross beta hx).continuous
  have hden : Continuous (fun sigma : ℝ =>
      ((sigma : ℂ) + T * I) - goldfeldShiftedZetaPole beta) :=
    hpath.sub continuous_const
  have hden_ne : ∀ sigma : ℝ,
      ((sigma : ℂ) + T * I) - goldfeldShiftedZetaPole beta ≠ 0 := by
    intro sigma hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  unfold goldfeldRegularizedContourIntegrand
  exact (hnum.comp hpath).div hden hden_ne

private theorem continuous_goldfeldRegularizedContourIntegrand_horizontal_minus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    Continuous (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
      chi1 chi beta x ((sigma : ℂ) - T * I)) := by
  have hpath : Continuous (fun sigma : ℝ => (sigma : ℂ) - T * I) :=
    Complex.continuous_ofReal.sub continuous_const
  have hnum : Continuous (goldfeldContourNumerator chi1 chi beta x) :=
    (differentiable_goldfeldContourNumerator hchi1 hchi hcross beta hx).continuous
  have hden : Continuous (fun sigma : ℝ =>
      ((sigma : ℂ) - T * I) - goldfeldShiftedZetaPole beta) :=
    hpath.sub continuous_const
  have hden_ne : ∀ sigma : ℝ,
      ((sigma : ℂ) - T * I) - goldfeldShiftedZetaPole beta ≠ 0 := by
    intro sigma hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  unfold goldfeldRegularizedContourIntegrand
  exact (hnum.comp hpath).div hden hden_ne

/-- The filled Goldfeld integrand is interval-integrable on both high
horizontal edges. -/
theorem intervalIntegrable_goldfeldRegularizedContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
        chi1 chi beta x ((sigma : ℂ) + T * I)) volume (-1) 2 ∧
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
        chi1 chi beta x ((sigma : ℂ) - T * I)) volume (-1) 2 := by
  exact ⟨(continuous_goldfeldRegularizedContourIntegrand_horizontal_plus
      hchi1 hchi hcross hx hT).intervalIntegrable _ _,
    (continuous_goldfeldRegularizedContourIntegrand_horizontal_minus
      hchi1 hchi hcross hx hT).intervalIntegrable _ _⟩

private theorem goldfeldRegularizedContourIntegrand_eq_horizontal_plus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) (sigma : ℝ) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I) =
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs0 : ((sigma : ℂ) + T * I) ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    simp at hi
    linarith
  have hsp : ((sigma : ℂ) + T * I) ≠ goldfeldShiftedZetaPole beta := by
    intro hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    chi1 chi hzero hs0 hsp

private theorem goldfeldRegularizedContourIntegrand_eq_horizontal_minus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) (sigma : ℝ) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I) =
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs0 : ((sigma : ℂ) - T * I) ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    simp at hi
    linarith
  have hsp : ((sigma : ℂ) - T * I) ≠ goldfeldShiftedZetaPole beta := by
    intro hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    chi1 chi hzero hs0 hsp

/-- On either high horizontal line the filled and raw integrals coincide. -/
theorem goldfeldRegularizedContourIntegrand_eq_intervalIntegral_goldfeldContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) :
    (∫ sigma in (-1)..2,
      goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) =
      ∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I) ∧
    (∫ sigma in (-1)..2,
      goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) =
      ∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I) := by
  have hplus : Set.EqOn
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I))
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) (uIcc (-1) 2) := by
    intro sigma _hsigma
    exact goldfeldRegularizedContourIntegrand_eq_horizontal_plus
      chi1 chi hzero hT sigma
  have hminus : Set.EqOn
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I))
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) (uIcc (-1) 2) := by
    intro sigma _hsigma
    exact goldfeldRegularizedContourIntegrand_eq_horizontal_minus
      chi1 chi hzero hT sigma
  exact ⟨intervalIntegral.integral_congr hplus,
    intervalIntegral.integral_congr hminus⟩

/-- Under the canceling zero hypothesis, the raw integrand is also
interval-integrable on both horizontal edges. -/
theorem intervalIntegrable_goldfeldContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) volume (-1) 2 ∧
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) volume (-1) 2 := by
  have hreg := intervalIntegrable_goldfeldRegularizedContourIntegrand_horizontal
    (beta := beta) hchi1 hchi hcross hx hT
  constructor
  · exact hreg.1.congr fun sigma _hsigma =>
      goldfeldRegularizedContourIntegrand_eq_horizontal_plus
        chi1 chi hzero hT sigma
  · exact hreg.2.congr fun sigma _hsigma =>
      goldfeldRegularizedContourIntegrand_eq_horizontal_minus
        chi1 chi hzero hT sigma

end

end BoundedGaps.Maynard
