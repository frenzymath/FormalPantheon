import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldHorizontalEdge
import BoundedGaps.BombieriVinogradov.Analytic.RectangleReciprocalWedgeIntegral

/-!
# Goldfeld's finite contour rectangle

The entire Goldfeld numerator is split at the shifted-zeta pole by Mathlib's
filled divided slope. Cauchy kills that analytic remainder, while the exact
reciprocal-rectangle theorem evaluates the retained principal part. The final
identity is stated on the raw source integrand with all four orientations
visible.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 58 and 126,
especially (5.13) and the proof of Theorem 12.9. Semantic review: `SEM-559`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

/-- The entire remainder after subtracting the shifted-zeta principal part. -/
noncomputable def goldfeldContourAnalyticRemainder
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  dslope (goldfeldContourNumerator chi1 chi beta x)
    (goldfeldShiftedZetaPole beta) s

/-- The normalized upward vertical integral truncated at ordinates `-T,T`. -/
noncomputable def goldfeldTruncatedVerticalIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in (-T)..T,
      goldfeldContourIntegrand chi1 chi beta x
        ((alpha : ℂ) + t * I)

/-- The source-oriented lower horizontal contribution. Its explicit minus
reverses the left-to-right scalar parameterization. -/
noncomputable def goldfeldTruncatedLowerIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x T : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
    (-(∫ sigma in (-1)..2,
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)))

/-- The source-oriented upper horizontal contribution. -/
noncomputable def goldfeldTruncatedUpperIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x T : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
    ∫ sigma in (-1)..2,
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)

/-- The numerator divided slope is entire whenever the numerator is. -/
theorem differentiable_goldfeldContourAnalyticRemainder
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ
      (goldfeldContourAnalyticRemainder chi1 chi beta x) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2
    (differentiable_goldfeldContourNumerator
      hchi1 hchi hcross beta hx).differentiableOn

/-- Off the shifted pole, the filled integrand is its entire remainder plus
the exact reciprocal principal part. -/
theorem goldfeldRegularizedContourIntegrand_eq_remainder_add
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : beta < 1)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    {s : ℂ} (hs : s ≠ goldfeldShiftedZetaPole beta) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x s =
      goldfeldContourAnalyticRemainder chi1 chi beta x s +
        goldfeldContourResidue chi1 chi beta x /
          (s - goldfeldShiftedZetaPole beta) := by
  have hnum := sub_smul_dslope
    (goldfeldContourNumerator chi1 chi beta x)
    (goldfeldShiftedZetaPole beta) s
  have hp := goldfeldContourNumerator_apply_shiftedZetaPole
    chi1 chi (x := x) hbeta hzero
  rw [hp] at hnum
  unfold goldfeldRegularizedContourIntegrand
    goldfeldContourAnalyticRemainder
  have hsub : s - goldfeldShiftedZetaPole beta ≠ 0 :=
    sub_ne_zero.mpr hs
  simp only [smul_eq_mul] at hnum
  apply (div_eq_iff hsub).2
  rw [add_mul, div_mul_cancel₀ _ hsub]
  calc
    goldfeldContourNumerator chi1 chi beta x s =
        (goldfeldContourNumerator chi1 chi beta x s -
          goldfeldContourResidue chi1 chi beta x) +
          goldfeldContourResidue chi1 chi beta x := by ring
    _ = (s - goldfeldShiftedZetaPole beta) *
          dslope (goldfeldContourNumerator chi1 chi beta x)
            (goldfeldShiftedZetaPole beta) s +
          goldfeldContourResidue chi1 chi beta x := by rw [hnum]
    _ = dslope (goldfeldContourNumerator chi1 chi beta x)
          (goldfeldShiftedZetaPole beta) s *
          (s - goldfeldShiftedZetaPole beta) +
          goldfeldContourResidue chi1 chi beta x := by ring

private lemma continuous_horizontal_principal_part
    (c p : ℂ) (y : ℝ) (hy : y ≠ p.im) :
    Continuous (fun t : ℝ => c / ((t : ℂ) + y * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_ofReal.add (continuous_const.mul continuous_const)).sub
      continuous_const)
  intro t
  apply sub_ne_zero.mpr
  intro h
  apply hy
  simpa using congrArg Complex.im h

private lemma continuous_vertical_principal_part
    (c p : ℂ) (x : ℝ) (hx : x ≠ p.re) :
    Continuous (fun t : ℝ => c / ((x : ℂ) + t * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const)
  intro t
  apply sub_ne_zero.mpr
  intro h
  apply hx
  simpa using congrArg Complex.re h

private theorem rectangle_boundary_eq_two_pi_I_mul_of_decomposition
    (f F : ℂ → ℂ) (z w p c : ℂ)
    (hF : Differentiable ℂ F)
    (hdecomp : ∀ s, s ≠ p → f s = F s + c / (s - p))
    (hzRe : z.re < p.re) (hpRe : p.re < w.re)
    (hzIm : z.im < p.im) (hpIm : p.im < w.im) :
    Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f =
      (2 * Real.pi * I) * c := by
  let G : ℂ → ℂ := fun s => c / (s - p)
  have hFcontinuous : Continuous F := hF.continuous
  have hFbottom : IntervalIntegrable
      (fun t : ℝ => F ((t : ℂ) + z.im * I)) volume z.re w.re :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFtop : IntervalIntegrable
      (fun t : ℝ => F ((t : ℂ) + w.im * I)) volume w.re z.re :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFright : IntervalIntegrable
      (fun t : ℝ => F ((w.re : ℂ) + t * I)) volume z.im w.im :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFleft : IntervalIntegrable
      (fun t : ℝ => F ((z.re : ℂ) + t * I)) volume w.im z.im :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hGbottom : IntervalIntegrable
      (fun t : ℝ => G ((t : ℂ) + z.im * I)) volume z.re w.re := by
    exact (continuous_horizontal_principal_part c p z.im
      (ne_of_lt hzIm)).intervalIntegrable _ _
  have hGtop : IntervalIntegrable
      (fun t : ℝ => G ((t : ℂ) + w.im * I)) volume w.re z.re := by
    exact (continuous_horizontal_principal_part c p w.im
      (ne_of_gt hpIm)).intervalIntegrable _ _
  have hGright : IntervalIntegrable
      (fun t : ℝ => G ((w.re : ℂ) + t * I)) volume z.im w.im := by
    exact (continuous_vertical_principal_part c p w.re
      (ne_of_gt hpRe)).intervalIntegrable _ _
  have hGleft : IntervalIntegrable
      (fun t : ℝ => G ((z.re : ℂ) + t * I)) volume w.im z.im := by
    exact (continuous_vertical_principal_part c p z.re
      (ne_of_lt hzRe)).intervalIntegrable _ _
  have hnotBottom (t : ℝ) : (t : ℂ) + z.im * I ≠ p := by
    intro h
    exact (ne_of_lt hzIm) (by simpa using congrArg Complex.im h)
  have hnotTop (t : ℝ) : (t : ℂ) + w.im * I ≠ p := by
    intro h
    exact (ne_of_gt hpIm) (by simpa using congrArg Complex.im h)
  have hnotRight (t : ℝ) : (w.re : ℂ) + t * I ≠ p := by
    intro h
    exact (ne_of_gt hpRe) (by simpa using congrArg Complex.re h)
  have hnotLeft (t : ℝ) : (z.re : ℂ) + t * I ≠ p := by
    intro h
    exact (ne_of_lt hzRe) (by simpa using congrArg Complex.re h)
  have hbottom :
      (∫ t : ℝ in z.re..w.re, f ((t : ℂ) + z.im * I)) =
        ∫ t : ℝ in z.re..w.re,
          F ((t : ℂ) + z.im * I) + G ((t : ℂ) + z.im * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotBottom t)
  have htop :
      (∫ t : ℝ in w.re..z.re, f ((t : ℂ) + w.im * I)) =
        ∫ t : ℝ in w.re..z.re,
          F ((t : ℂ) + w.im * I) + G ((t : ℂ) + w.im * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotTop t)
  have hright :
      (∫ t : ℝ in z.im..w.im, f ((w.re : ℂ) + t * I)) =
        ∫ t : ℝ in z.im..w.im,
          F ((w.re : ℂ) + t * I) + G ((w.re : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotRight t)
  have hleft :
      (∫ t : ℝ in w.im..z.im, f ((z.re : ℂ) + t * I)) =
        ∫ t : ℝ in w.im..z.im,
          F ((z.re : ℂ) + t * I) + G ((z.re : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotLeft t)
  have hzw : Complex.wedgeIntegral z w f =
      Complex.wedgeIntegral z w F + Complex.wedgeIntegral z w G := by
    simp only [Complex.wedgeIntegral]
    rw [hbottom, hright,
      intervalIntegral.integral_add hFbottom hGbottom,
      intervalIntegral.integral_add hFright hGright]
    simp only [smul_add]
    abel
  have hwz : Complex.wedgeIntegral w z f =
      Complex.wedgeIntegral w z F + Complex.wedgeIntegral w z G := by
    simp only [Complex.wedgeIntegral]
    rw [htop, hleft,
      intervalIntegral.integral_add hFtop hGtop,
      intervalIntegral.integral_add hFleft hGleft]
    simp only [smul_add]
    abel
  have hFzero : Complex.wedgeIntegral z w F +
      Complex.wedgeIntegral w z F = 0 := by
    have hconservative := hF.differentiableOn.isConservativeOn z w
      (fun _ _ => mem_univ _)
    rw [hconservative]
    simp
  have hGsum : Complex.wedgeIntegral z w G +
      Complex.wedgeIntegral w z G = (2 * Real.pi * I) * c := by
    exact wedgeIntegral_add_wedgeIntegral_div_sub_eq_two_pi_I_mul
      z w p c hzRe hpRe hzIm hpIm
  rw [hzw, hwz]
  calc
    (Complex.wedgeIntegral z w F + Complex.wedgeIntegral z w G) +
        (Complex.wedgeIntegral w z F + Complex.wedgeIntegral w z G) =
      (Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F) +
        (Complex.wedgeIntegral z w G + Complex.wedgeIntegral w z G) := by
          abel
    _ = (2 * Real.pi * I) * c := by rw [hFzero, hGsum, zero_add]

/-- The filled Goldfeld integrand has the exact positive rectangle boundary
integral. The scalar lower and upper paths are both parameterized
left-to-right; the displayed signs encode the positive boundary. -/
theorem goldfeldRegularizedContourIntegrand_rectangle_boundary_eq
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    (∫ sigma in (-1)..2,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I)) -
      (∫ sigma in (-1)..2,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I)) +
      I * (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I)) -
      I * (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I)) =
      (2 * Real.pi * I) *
        goldfeldContourResidue chi1 chi beta x := by
  let z : ℂ := (-1 : ℂ) - T * I
  let w : ℂ := (2 : ℂ) + T * I
  let p : ℂ := goldfeldShiftedZetaPole beta
  let f : ℂ → ℂ := goldfeldRegularizedContourIntegrand chi1 chi beta x
  let F : ℂ → ℂ := goldfeldContourAnalyticRemainder chi1 chi beta x
  let c : ℂ := goldfeldContourResidue chi1 chi beta x
  have hzRe : z.re < p.re := by
    simp [z, p, goldfeldShiftedZetaPole]
    linarith
  have hpRe : p.re < w.re := by
    simp [w, p, goldfeldShiftedZetaPole]
    linarith
  have hzIm : z.im < p.im := by
    simp [z, p, goldfeldShiftedZetaPole]
    linarith
  have hpIm : p.im < w.im := by
    simp [w, p, goldfeldShiftedZetaPole]
    linarith
  have hboundary := rectangle_boundary_eq_two_pi_I_mul_of_decomposition
    f F z w p c
    (differentiable_goldfeldContourAnalyticRemainder
      hchi1 hchi hcross beta hx)
    (fun s hs => goldfeldRegularizedContourIntegrand_eq_remainder_add
      chi1 chi hbeta1 hzero hs)
    hzRe hpRe hzIm hpIm
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at hboundary
  simpa [f, F, c, z, w, p, smul_eq_mul, sub_eq_add_neg] using hboundary

/-- The exact finite source decomposition, with the lower side reversed and
all vertical parameterizations upward. -/
theorem goldfeldContourIntegrand_truncated_rectangle_decomposition
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldTruncatedVerticalIntegral chi1 chi beta x 2 T =
      goldfeldTruncatedLowerIntegral chi1 chi beta x T +
        goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1) T +
        goldfeldTruncatedUpperIntegral chi1 chi beta x T +
        goldfeldContourResidue chi1 chi beta x := by
  have hboundary :=
    goldfeldRegularizedContourIntegrand_rectangle_boundary_eq
      chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hT hzero
  have hhorizontal :=
    goldfeldRegularizedContourIntegrand_eq_intervalIntegral_goldfeldContourIntegrand_horizontal
      (chi1 := chi1) (chi := chi) (x := x) hzero hT
  have hright :
      (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I)) =
      ∫ t in (-T)..T,
        goldfeldContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
      chi1 chi hzero (by
        intro hs
        have hre := congrArg Complex.re hs
        norm_num at hre)
      (by
        intro hs
        have hre := congrArg Complex.re hs
        simp [goldfeldShiftedZetaPole] at hre
        linarith)
  have hleft :
      (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I)) =
      ∫ t in (-T)..T,
        goldfeldContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
      chi1 chi hzero (by
        intro hs
        have hre := congrArg Complex.re hs
        norm_num at hre)
      (by
        intro hs
        have hre := congrArg Complex.re hs
        simp [goldfeldShiftedZetaPole] at hre
        linarith)
  rw [hhorizontal.2, hhorizontal.1, hright, hleft] at hboundary
  let lower : ℂ := ∫ sigma in (-1)..2,
    goldfeldContourIntegrand chi1 chi beta x
      ((sigma : ℂ) - T * I)
  let upper : ℂ := ∫ sigma in (-1)..2,
    goldfeldContourIntegrand chi1 chi beta x
      ((sigma : ℂ) + T * I)
  let right : ℂ := ∫ t in (-T)..T,
    goldfeldContourIntegrand chi1 chi beta x
      ((2 : ℂ) + t * I)
  let left : ℂ := ∫ t in (-T)..T,
    goldfeldContourIntegrand chi1 chi beta x
      ((-1 : ℂ) + t * I)
  change lower - upper + I * right - I * left =
    (2 * Real.pi * I) * goldfeldContourResidue chi1 chi beta x at hboundary
  have hIright :
      I * right =
        (2 * Real.pi * I) * goldfeldContourResidue chi1 chi beta x -
          lower + upper + I * left := by
    linear_combination hboundary
  have hmainMul :
      -I * ((2 * Real.pi * I) *
        goldfeldContourResidue chi1 chi beta x) =
        (((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x := by
    calc
      _ = (-I * I) * ((((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x) := by
        push_cast
        ring
      _ = _ := by rw [neg_mul, I_mul_I]; simp
  have hleftMul : -I * (I * left) = left := by
    rw [← mul_assoc, neg_mul, I_mul_I]
    simp
  have hrightEq :
      right = (((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x +
        I * lower - I * upper + left := by
    calc
      _ = -I * (I * right) := by
        rw [← mul_assoc, neg_mul, I_mul_I]
        simp
      _ = -I * ((2 * Real.pi * I) *
          goldfeldContourResidue chi1 chi beta x -
          lower + upper + I * left) := by rw [hIright]
      _ = _ := by
        rw [mul_add, mul_add, mul_sub, hmainMul, hleftMul]
        ring
  simp only [goldfeldTruncatedVerticalIntegral,
    goldfeldTruncatedLowerIntegral, goldfeldTruncatedUpperIntegral]
  norm_num only [ofReal_neg, ofReal_one]
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹) * right =
    ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) * (-lower) +
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * left +
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) * upper +
      goldfeldContourResidue chi1 chi beta x
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast Real.two_pi_pos.ne'
  rw [hrightEq]
  field_simp [hpi, I_ne_zero]
  simp [mul_add, mul_sub, ← mul_assoc, I_mul_I]
  ring

end

end BoundedGaps.Maynard
