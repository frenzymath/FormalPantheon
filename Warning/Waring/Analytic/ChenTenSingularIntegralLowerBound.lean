import Waring.Analytic.ChenTenCumulativeCount
import Waring.Analytic.ChenTenSingularIntegral
import Waring.Analytic.ChenTenRepresentation
namespace Waring.Analytic
open MeasureTheory
open scoped BigOperators Interval
noncomputable section
/-! Scratch framework for equations (35)--(36) in Chen's Lemma 10. -/
/-- The finite set of positive shift indices from one through `M`. -/
def scratchShiftSet (M : Nat) : Finset Nat := Finset.Icc 1 M
/-- The exponential phase contributed by a single positive shift. -/
def scratchShiftPhase (alpha : Real) (u : Nat) : Complex :=
  Complex.exp
    (2 * Real.pi * Complex.I * (alpha * (u : Real)))
/-- The finite exponential sum over shifts from one through `M`. -/
def scratchShiftKernel (M : Nat) (alpha : Real) : Complex :=
  ∑ u ∈ scratchShiftSet M, scratchShiftPhase alpha u

/-- The representation integrand weighted by the square of the shift kernel. -/
def scratchShiftWeightedIntegrand
    (P N M : Nat) (alpha : Real) : Complex :=
  chenTenRepresentationIntegrand P N alpha * scratchShiftKernel M alpha ^ 2
/-- The double positive-shift count used to approximate the singular integral. -/
def scratchShiftSquareCount (P N M : Nat) : Nat :=
  ∑ u ∈ scratchShiftSet M, ∑ v ∈ scratchShiftSet M,
    positiveFifthPowerRepresentationCount 15 P (N - u - v)

private theorem scratch_representationIntegrand_shift
    {P N M u v : Nat} (hu : u ∈ scratchShiftSet M)
    (hv : v ∈ scratchShiftSet M) (hMN : 2 * M ≤ N)
    (alpha : Real) :
    chenTenRepresentationIntegrand P (N - u - v) alpha =
      chenTenRepresentationIntegrand P N alpha *
        scratchShiftPhase alpha u * scratchShiftPhase alpha v := by
  have huM : u ≤ M := (Finset.mem_Icc.mp hu).2
  have hvM : v ≤ M := (Finset.mem_Icc.mp hv).2
  have huvN : u + v ≤ N := by omega
  unfold chenTenRepresentationIntegrand scratchShiftPhase
  have hphase :
      Complex.exp (-2 * Real.pi * Complex.I *
        (alpha * ((N - u - v : Nat) : Real))) =
        Complex.exp (-2 * Real.pi * Complex.I * (alpha * (N : Real))) *
          Complex.exp (2 * Real.pi * Complex.I * (alpha * (u : Real))) *
            Complex.exp (2 * Real.pi * Complex.I * (alpha * (v : Real))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    have hsub : N - u - v + u + v = N := by omega
    have hsubComplex :
        ((N - u - v : Nat) : Complex) + u + v = N := by
      exact_mod_cast hsub
    rw [← hsubComplex]
    ring
  rw [hphase]
  ring

private theorem scratch_intervalIntegrable_shift_integrand
    (P N u v : Nat) (c : Real) :
    IntervalIntegrable
      (fun alpha : Real =>
        chenTenRepresentationIntegrand P (N - u - v) alpha)
      volume c (c + 1) := by
  exact (continuous_chenTenRepresentationIntegrand P (N - u - v)).intervalIntegrable
    (μ := volume) c (c + 1)

private theorem scratch_count_eq_integral
    (P n : Nat) (c : Real) :
    (positiveFifthPowerRepresentationCount 15 P n : Complex) =
      ∫ alpha in c..c + 1,
        chenTenRepresentationIntegrand P n alpha := by
  simpa [chenTenRepresentationIntegrand] using
    (integral_fifthPowerExponentialSum_pow_eq_count
      15 P n c).symm

/-- The double shift count equals its weighted representation integral on a unit interval. -/
theorem scratch_shift_square_count_eq_integral
    (P N M : Nat) (hMN : 2 * M ≤ N) (c : Real) :
    (scratchShiftSquareCount P N M : Complex) =
      ∫ alpha in c..c + 1,
        chenTenRepresentationIntegrand P N alpha *
          scratchShiftKernel M alpha ^ 2 := by
  unfold scratchShiftSquareCount
  push_cast
  have hcounts :
      (∑ u ∈ scratchShiftSet M,
        ∑ v ∈ scratchShiftSet M,
          (positiveFifthPowerRepresentationCount 15 P (N - u - v) : Complex)) =
        ∑ u ∈ scratchShiftSet M,
          ∑ v ∈ scratchShiftSet M,
            ∫ alpha in c..c + 1,
              chenTenRepresentationIntegrand P (N - u - v) alpha := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact scratch_count_eq_integral P (N - u - v) c
  rw [hcounts]
  have hinner : ∀ u ∈ scratchShiftSet M,
      IntervalIntegrable
        (fun alpha : Real =>
          ∑ v ∈ scratchShiftSet M,
            chenTenRepresentationIntegrand P (N - u - v) alpha)
        volume c (c + 1) := by
    intro u hu
    have hcont : Continuous (fun alpha : Real =>
        ∑ v ∈ scratchShiftSet M,
          chenTenRepresentationIntegrand P (N - u - v) alpha) := by
      apply continuous_finsetSum
      intro v hv
      exact continuous_chenTenRepresentationIntegrand P (N - u - v)
    exact hcont.intervalIntegrable (μ := volume) c (c + 1)
  have hinner_sum (u : Nat) (hu : u ∈ scratchShiftSet M) :
      (∑ v ∈ scratchShiftSet M,
          ∫ alpha in c..c + 1,
            chenTenRepresentationIntegrand P (N - u - v) alpha) =
        ∫ alpha in c..c + 1,
          ∑ v ∈ scratchShiftSet M,
            chenTenRepresentationIntegrand P (N - u - v) alpha := by
    symm
    exact intervalIntegral.integral_finsetSum
      (fun v hv => scratch_intervalIntegrable_shift_integrand P N u v c)
  have houter_sum :
      (∑ u ∈ scratchShiftSet M,
          ∫ alpha in c..c + 1,
            ∑ v ∈ scratchShiftSet M,
              chenTenRepresentationIntegrand P (N - u - v) alpha) =
        ∫ alpha in c..c + 1,
          ∑ u ∈ scratchShiftSet M,
            ∑ v ∈ scratchShiftSet M,
              chenTenRepresentationIntegrand P (N - u - v) alpha := by
    symm
    exact intervalIntegral.integral_finsetSum (fun u hu => hinner u hu)
  have hinner_sums :
      (∑ u ∈ scratchShiftSet M,
          ∑ v ∈ scratchShiftSet M,
            ∫ alpha in c..c + 1,
              chenTenRepresentationIntegrand P (N - u - v) alpha) =
        ∑ u ∈ scratchShiftSet M,
          ∫ alpha in c..c + 1,
            ∑ v ∈ scratchShiftSet M,
              chenTenRepresentationIntegrand P (N - u - v) alpha := by
    apply Finset.sum_congr rfl
    intro u hu
    exact hinner_sum u hu
  rw [hinner_sums, houter_sum]
  apply intervalIntegral.integral_congr
  intro alpha halpha
  change
    (∑ u ∈ scratchShiftSet M,
      ∑ v ∈ scratchShiftSet M,
        chenTenRepresentationIntegrand P (N - u - v) alpha) =
      chenTenRepresentationIntegrand P N alpha * scratchShiftKernel M alpha ^ 2
  unfold scratchShiftKernel
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [scratch_representationIntegrand_shift hu hv hMN alpha]
  ring

/-- Splitting the unit interval expresses the shift count as central plus supplementary pieces. -/
theorem scratch_shift_square_count_eq_central_add_supplementary
    (P N M : Nat) (hMN : 2 * M ≤ N)
    (delta : Real) :
    (scratchShiftSquareCount P N M : Complex) =
      (∫ alpha in -delta..delta,
        scratchShiftWeightedIntegrand P N M alpha) +
        ∫ alpha in delta..1 - delta,
          scratchShiftWeightedIntegrand P N M alpha := by
  have hcont : Continuous (scratchShiftWeightedIntegrand P N M) := by
    unfold scratchShiftWeightedIntegrand scratchShiftKernel scratchShiftPhase
    apply Continuous.mul (continuous_chenTenRepresentationIntegrand P N)
    apply Continuous.pow
    apply continuous_finsetSum
    intro u hu
    fun_prop
  have hleft := hcont.intervalIntegrable (μ := volume) (-delta) delta
  have hright := hcont.intervalIntegrable (μ := volume) delta (1 - delta)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hwhole := scratch_shift_square_count_eq_integral P N M hMN (-delta)
  calc
    (scratchShiftSquareCount P N M : Complex) =
        ∫ alpha in -delta..1 - delta,
          scratchShiftWeightedIntegrand P N M alpha := by
      unfold scratchShiftWeightedIntegrand
      have hend : -delta + 1 = 1 - delta := by ring
      rw [hend] at hwhole
      exact hwhole
    _ = (∫ alpha in -delta..delta,
          scratchShiftWeightedIntegrand P N M alpha) +
          ∫ alpha in delta..1 - delta,
            scratchShiftWeightedIntegrand P N M alpha := by
      simpa using hsplit.symm

/-- Central and supplementary integral errors combine into a bound for the full shift count. -/
theorem scratch_norm_shift_square_sub_singularIntegral_le_of_split
    {P N M : Nat} (hMN : 2 * M ≤ N) (delta : Real)
    {centralError supplementaryError : Real}
    (hcentral :
      ‖(∫ alpha in -delta..delta,
          scratchShiftWeightedIntegrand P N M alpha) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
          centralError * (M : Real) ^ 2)
    (hsupplementary :
      ‖∫ alpha in delta..1 - delta,
          scratchShiftWeightedIntegrand P N M alpha‖ ≤
        supplementaryError * (M : Real) ^ 2) :
    ‖(scratchShiftSquareCount P N M : Complex) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
      (centralError + supplementaryError) * (M : Real) ^ 2 := by
  rw [scratch_shift_square_count_eq_central_add_supplementary P N M hMN delta]
  calc
    ‖(∫ alpha in -delta..delta,
          scratchShiftWeightedIntegrand P N M alpha) +
        (∫ alpha in delta..1 - delta,
          scratchShiftWeightedIntegrand P N M alpha) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ =
      ‖((∫ alpha in -delta..delta,
          scratchShiftWeightedIntegrand P N M alpha) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2) +
        ∫ alpha in delta..1 - delta,
          scratchShiftWeightedIntegrand P N M alpha‖ := by
      congr 1
      ring
    _ ≤ ‖(∫ alpha in -delta..delta,
          scratchShiftWeightedIntegrand P N M alpha) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ +
        ‖∫ alpha in delta..1 - delta,
          scratchShiftWeightedIntegrand P N M alpha‖ := norm_add_le _ _
    _ ≤ centralError * (M : Real) ^ 2 +
        supplementaryError * (M : Real) ^ 2 :=
      add_le_add hcentral hsupplementary
    _ = (centralError + supplementaryError) * (M : Real) ^ 2 := by ring

private theorem scratch_sum_descending_interval
    (f : Nat → Real) {A M : Nat} (hM : M ≤ A) :
    (∑ u ∈ Finset.Icc 1 M, f (A - u)) =
      (∑ n ∈ Finset.range A, f n) -
        (∑ n ∈ Finset.range (A - M), f n) := by
  have hmap :
      (∑ u ∈ Finset.Icc 1 M, f (A - u)) =
        ∑ n ∈ Finset.Ico (A - M) A, f n := by
    apply Finset.sum_bij (fun u _ => A - u)
    · intro u hu
      have hu' := Finset.mem_Icc.mp hu
      rw [Finset.mem_Ico]
      omega
    · intro u hu v hv huv
      have hu' := Finset.mem_Icc.mp hu
      have hv' := Finset.mem_Icc.mp hv
      omega
    · intro n hn
      have hn' := Finset.mem_Ico.mp hn
      refine ⟨A - n, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro u hu
      rfl
  rw [hmap]
  exact Finset.sum_Ico_eq_sub f (Nat.sub_le A M)

/-- The `< X` convention removes predecessor arithmetic. Chen's source
`K15(Y)` uses `<= Y`, so it corresponds to this function at `X = Y + 1`. -/
def scratchCumulativeCount (P X : Nat) : Real :=
  ∑ n ∈ Finset.range X,
    (positiveFifthPowerRepresentationCount 15 P n : Real)

/-- The scratch cumulative count agrees with the project's cumulative count. -/
theorem scratch_cumulative_count_eq_project_count (P X : Nat) :
    scratchCumulativeCount P X =
      (chenTenCumulativeRepresentationCount P X : Real) := by
  unfold scratchCumulativeCount chenTenCumulativeRepresentationCount
  push_cast
  rfl

/-- In the bounded range, the scratch cumulative count equals the predecessor `K15` count. -/
theorem scratch_cumulative_count_eq_K15_pred
    {P X : Nat} (hX : 2 ≤ X) (hXPow : X ≤ (P + 1) ^ 5) :
    scratchCumulativeCount P X = (K15 (X - 1) : Real) := by
  rw [scratch_cumulative_count_eq_project_count]
  rw [chenTenCumulativeRepresentationCount_eq_K15_pred hX hXPow]

/-- The cumulative count inherits the explicit `K15` approximation error. -/
theorem scratch_cumulative_count_error_bound
    {P X : Nat} (hX : 2 ≤ X) (hXPow : X ≤ (P + 1) ^ 5)
    (hroot : (15 : Real) ≤ ((X - 1 : Nat) : Real) ^ (1 / (5 : Real))) :
    |scratchCumulativeCount P X - chenTenT15 * ((X - 1 : Nat) : Real) ^ 3| ≤
      1000 * chenTenT15 * ((X - 1 : Nat) : Real) ^ (14 / (5 : Real)) := by
  rw [scratch_cumulative_count_eq_K15_pred hX hXPow]
  exact K15_error_bound (X - 1) hroot

/-- The natural-valued shift count is nonnegative after casting to `Real`. -/
theorem scratch_shift_square_count_nonneg
    (P N M : Nat) :
    0 ≤ (scratchShiftSquareCount P N M : Real) := by
  exact_mod_cast Nat.zero_le (scratchShiftSquareCount P N M)

/-- The double shift count telescopes into differences of cumulative counts. -/
theorem scratch_shift_square_count_eq_cumulative_difference
    (P N M : Nat) (hMN : 2 * M ≤ N) :
    (∑ u ∈ scratchShiftSet M,
        ∑ v ∈ scratchShiftSet M,
          (positiveFifthPowerRepresentationCount 15 P (N - u - v) : Real)) =
      ∑ v ∈ scratchShiftSet M,
        (scratchCumulativeCount P (N - v) -
          scratchCumulativeCount P (N - v - M)) := by
  apply Finset.sum_congr rfl
  intro v hv
  have hvM : v ≤ M := (Finset.mem_Icc.mp hv).2
  have hA : M ≤ N - v := by omega
  unfold scratchCumulativeCount
  exact scratch_sum_descending_interval
    (fun n => (positiveFifthPowerRepresentationCount 15 P n : Real)) hA

/-- Casting the shift count to `Real` preserves its cumulative-difference identity. -/
theorem scratch_shift_square_count_cast_eq_cumulative_difference
    (P N M : Nat) (hMN : 2 * M ≤ N) :
    (scratchShiftSquareCount P N M : Real) =
      ∑ v ∈ scratchShiftSet M,
        (scratchCumulativeCount P (N - v) -
          scratchCumulativeCount P (N - v - M)) := by
  unfold scratchShiftSquareCount
  push_cast
  exact scratch_shift_square_count_eq_cumulative_difference P N M hMN

/-- The real shift count equals differences of the project's cumulative counts. -/
theorem scratch_shift_square_count_cast_eq_project_cumulative_difference
    (P N M : Nat) (hMN : 2 * M ≤ N) :
    (scratchShiftSquareCount P N M : Real) =
      ∑ v ∈ scratchShiftSet M,
        ((chenTenCumulativeRepresentationCount P (N - v) : Real) -
          (chenTenCumulativeRepresentationCount P (N - v - M) : Real)) := by
  rw [scratch_shift_square_count_cast_eq_cumulative_difference P N M hMN]
  apply Finset.sum_congr rfl
  intro v hv
  rw [scratch_cumulative_count_eq_project_count,
    scratch_cumulative_count_eq_project_count]

/-- Under the power bound, the real shift count equals a difference of `K15` values. -/
theorem scratch_shift_square_count_cast_eq_K15_difference
    (P N M : Nat) (hMN : 2 * M + 2 ≤ N)
    (hNPow : N ≤ (P + 1) ^ 5) :
    (scratchShiftSquareCount P N M : Real) =
      ∑ v ∈ scratchShiftSet M,
        ((K15 (N - v - 1) : Real) -
          (K15 (N - v - M - 1) : Real)) := by
  have hMN' : 2 * M ≤ N := by omega
  rw [scratch_shift_square_count_cast_eq_project_cumulative_difference
    P N M hMN']
  apply Finset.sum_congr rfl
  intro v hv
  have hvM : v ≤ M := (Finset.mem_Icc.mp hv).2
  have hfirst : 2 ≤ N - v := by omega
  have hsecond : 2 ≤ N - v - M := by omega
  have hfirstPow : N - v ≤ (P + 1) ^ 5 := by omega
  have hsecondPow : N - v - M ≤ (P + 1) ^ 5 := by omega
  rw [chenTenCumulativeRepresentationCount_eq_K15_pred hfirst hfirstPow,
    chenTenCumulativeRepresentationCount_eq_K15_pred hsecond hsecondPow]

/-- A count approximation and analytic shift error give a lower bound for the singular integral. -/
theorem scratch_singularIntegral_re_lower_of_shift_average
    {P N M : Nat} {mainTerm analyticError countError : Real}
    (hM : 0 < M)
    (hanalytic :
      ‖(scratchShiftSquareCount P N M : Complex) -
          chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
        analyticError * (M : Real) ^ 2)
    (hcount :
      |(scratchShiftSquareCount P N M : Real) -
          mainTerm * (M : Real) ^ 2| ≤
        countError * (M : Real) ^ 2) :
    mainTerm - countError - analyticError ≤
      (chenTenSingularIntegral P N).re := by
  have hmpos : (0 : Real) < M := by exact_mod_cast hM
  have hm2pos : (0 : Real) < (M : Real) ^ 2 := sq_pos_of_pos hmpos
  have hanalyticRe :
      |(scratchShiftSquareCount P N M : Real) -
          (chenTenSingularIntegral P N).re * (M : Real) ^ 2| ≤
        analyticError * (M : Real) ^ 2 := by
    have hre := (Complex.abs_re_le_norm
      ((scratchShiftSquareCount P N M : Complex) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2)).trans hanalytic
    simpa [Complex.mul_re, pow_two] using hre
  have hcountLower := (abs_le.mp hcount).1
  have hanalyticUpper := (abs_le.mp hanalyticRe).2
  have hscaled :
      (mainTerm - countError) * (M : Real) ^ 2 ≤
        ((chenTenSingularIntegral P N).re + analyticError) *
          (M : Real) ^ 2 := by
    linarith
  have hcancel := le_of_mul_le_mul_right hscaled hm2pos
  linarith

/-- A direct lower bound for the shift count gives the corresponding singular-integral bound. -/
theorem scratch_singularIntegral_re_lower_of_shift_average_lower
    {P N M : Nat} {lowerTerm analyticError : Real}
    (hM : 0 < M)
    (hanalytic :
      ‖(scratchShiftSquareCount P N M : Complex) -
          chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
        analyticError * (M : Real) ^ 2)
    (hcountLower :
      lowerTerm * (M : Real) ^ 2 ≤
        (scratchShiftSquareCount P N M : Real)) :
    lowerTerm - analyticError ≤
      (chenTenSingularIntegral P N).re := by
  have hmpos : (0 : Real) < M := by exact_mod_cast hM
  have hm2pos : (0 : Real) < (M : Real) ^ 2 := sq_pos_of_pos hmpos
  have hanalyticRe :
      |(scratchShiftSquareCount P N M : Real) -
          (chenTenSingularIntegral P N).re * (M : Real) ^ 2| ≤
        analyticError * (M : Real) ^ 2 := by
    have hre := (Complex.abs_re_le_norm
      ((scratchShiftSquareCount P N M : Complex) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2)).trans hanalytic
    simpa [Complex.mul_re, pow_two] using hre
  have hanalyticUpper := (abs_le.mp hanalyticRe).2
  have hscaled :
      lowerTerm * (M : Real) ^ 2 ≤
        ((chenTenSingularIntegral P N).re + analyticError) *
          (M : Real) ^ 2 := by
    linarith
  have hcancel := le_of_mul_le_mul_right hscaled hm2pos
  linarith

/-- The source-scale cumulative and analytic errors yield a symbolic real-part lower bound. -/
theorem scratch_singularIntegral_re_lower_source_errors
    {P N M : Nat} {T : Real} (hM : 0 < M)
    (hanalytic :
      ‖(scratchShiftSquareCount P N M : Complex) -
          chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
        3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) *
          (M : Real) ^ 2)
    (hcumulative :
      |(scratchShiftSquareCount P N M : Real) -
          (3 * T * (N : Real) ^ 2) * (M : Real) ^ 2| ≤
        (1000 * T * (N : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real)) * (M : Real) ^ 2) :
    3 * T * (N : Real) ^ 2 -
          1000 * T * (N : Real) ^ 2 *
            (P : Real) ^ (-1 / 5 : Real) -
        3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) ≤
      (chenTenSingularIntegral P N).re := by
  exact scratch_singularIntegral_re_lower_of_shift_average
    (mainTerm := 3 * T * (N : Real) ^ 2)
    (analyticError := 3 * (10 : Real) ^ 4 *
      (P : Real) ^ (49 / 5 : Real))
    (countError := 1000 * T * (N : Real) ^ 2 *
      (P : Real) ^ (-1 / 5 : Real))
    hM hanalytic hcumulative

/-- Absorbing the source errors gives the explicit `2999 / 1000` lower bound. -/
theorem scratch_singularIntegral_re_lower_2999
    {P N M : Nat} {T : Real} (hM : 0 < M)
    (hanalytic :
      ‖(scratchShiftSquareCount P N M : Complex) -
          chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
        3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) *
          (M : Real) ^ 2)
    (hcumulative :
      |(scratchShiftSquareCount P N M : Real) -
          (3 * T * (N : Real) ^ 2) * (M : Real) ^ 2| ≤
        (1000 * T * (N : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real)) * (M : Real) ^ 2)
    (herrors :
      1000 * T * (N : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real) +
        3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) ≤
          (1 / 1000 : Real) * T * (N : Real) ^ 2) :
    (2999 / 1000 : Real) * T * (N : Real) ^ 2 ≤
      (chenTenSingularIntegral P N).re := by
  have hlower := scratch_singularIntegral_re_lower_source_errors
    (P := P) (N := N) (M := M) (T := T) hM hanalytic hcumulative
  linarith

/-- A nonnegative real part determines the norm of the real singular integral. -/
theorem scratch_norm_chenTenSingularIntegral_eq_re_of_nonneg
    {P N : Nat} (hR : 0 ≤ (chenTenSingularIntegral P N).re) :
    ‖chenTenSingularIntegral P N‖ =
      (chenTenSingularIntegral P N).re := by
  have hreal :
      chenTenSingularIntegral P N =
        ((chenTenSingularIntegral P N).re : Complex) := by
    apply Complex.ext
    · simp
    · simpa using chenTenSingularIntegral_im_eq_zero P N
  calc
    ‖chenTenSingularIntegral P N‖ =
        ‖((chenTenSingularIntegral P N).re : Complex)‖ :=
      congrArg norm hreal
    _ = |(chenTenSingularIntegral P N).re| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = (chenTenSingularIntegral P N).re := abs_of_nonneg hR

end

end Waring.Analytic
