import Waring.Analytic.ChenSevenQuadrature

/-!
# Right-endpoint correction for Chen's quadrature estimate

The residue-class endpoint bookkeeping uses right endpoint samples.  This
file transfers the coefficient bounds from the left-endpoint correction and
packages the corresponding Abel estimate.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The correction between a right endpoint sample and its secant-phase
integral. -/
noncomputable def rightPhaseCorrection (x : Real) : Complex :=
  ⟨1 / 2, phaseCorrectionImag x⟩

/-- Right correction is left correction plus the successive endpoint
difference. -/
theorem rightPhaseCorrection_eq_phaseCorrection_add_one (x : Real) :
    rightPhaseCorrection x = phaseCorrection x + 1 := by
  apply Complex.ext
  · change 1 / 2 = -1 / 2 + 1
    ring
  · simp [rightPhaseCorrection, phaseCorrection]

/-- The right-endpoint correction has norm at most `5/6`. -/
theorem norm_rightPhaseCorrection_le_five_sixths
    {x : Real} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    ‖rightPhaseCorrection x‖ ≤ 5 / 6 := by
  calc
    ‖rightPhaseCorrection x‖ ≤
        |(rightPhaseCorrection x).re| + |(rightPhaseCorrection x).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 1 / 2 + |phaseCorrectionImag x| := by
      simp [rightPhaseCorrection]
    _ = 1 / 2 + phaseCorrectionImag x := by
      rw [abs_of_nonneg (phaseCorrectionImag_nonneg hx hxpi)]
    _ ≤ 1 / 2 + 1 / 3 := by
      gcongr
      exact phaseCorrectionImag_le_one_third hx hxpi
    _ = 5 / 6 := by norm_num

/-- Differences of right corrections equal differences of left corrections. -/
theorem rightPhaseCorrection_sub_eq_phaseCorrection_sub (x y : Real) :
    rightPhaseCorrection y - rightPhaseCorrection x =
      phaseCorrection y - phaseCorrection x := by
  apply Complex.ext
  · change 1 / 2 - 1 / 2 = -1 / 2 - (-1 / 2)
    ring
  · rfl

/-- The total variation of increasing right corrections is at most `1/3`. -/
theorem sum_norm_rightPhaseCorrection_sub_le_one_third
    (delta : Nat → Real) (n : Nat)
    (hpos : ∀ i, i < n → 0 < delta i)
    (hpi : ∀ i, i < n → delta i ≤ Real.pi)
    (hmono : ∀ i, i + 1 < n → delta i ≤ delta (i + 1)) :
    (∑ i ∈ Finset.range (n - 1),
      ‖rightPhaseCorrection (delta (i + 1)) -
        rightPhaseCorrection (delta i)‖) ≤ 1 / 3 := by
  calc
    _ = ∑ i ∈ Finset.range (n - 1),
        ‖phaseCorrection (delta (i + 1)) -
          phaseCorrection (delta i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rightPhaseCorrection_sub_eq_phaseCorrection_sub]
    _ ≤ 1 / 3 :=
      sum_norm_phaseCorrection_sub_le_one_third delta n hpos hpi hmono

/-- Abel summation bounds right-endpoint corrections by two. -/
theorem norm_sum_rightPhaseCorrection_mul_exp_sub_le_two
    (theta delta : Nat → Real) (n : Nat)
    (hpos : ∀ i, i < n → 0 < delta i)
    (hpi : ∀ i, i < n → delta i ≤ Real.pi)
    (hmono : ∀ i, i + 1 < n → delta i ≤ delta (i + 1)) :
    ‖∑ i ∈ Finset.range n,
      rightPhaseCorrection (delta i) *
        (Complex.exp (Complex.I * (theta (i + 1) : Complex)) -
          Complex.exp (Complex.I * (theta i : Complex)))‖ ≤ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  let u : Nat → Complex := fun i =>
    Complex.exp (Complex.I * (theta i : Complex))
  have hab := sum_range_mul_sub_eq_directAbel
    (fun i => rightPhaseCorrection (delta i)) u n
  have hu (i : Nat) : ‖u i‖ = 1 := by
    simp [u, Complex.norm_exp_I_mul_ofReal]
  have hterminal :
      ‖rightPhaseCorrection (delta (n - 1)) * u n‖ ≤ 5 / 6 := by
    rw [norm_mul, hu, mul_one]
    exact norm_rightPhaseCorrection_le_five_sixths
      (hpos (n - 1) (Nat.sub_lt hnPos Nat.one_pos))
      (hpi (n - 1) (Nat.sub_lt hnPos Nat.one_pos))
  have hinitial :
      ‖rightPhaseCorrection (delta 0) * u 0‖ ≤ 5 / 6 := by
    rw [norm_mul, hu, mul_one]
    exact norm_rightPhaseCorrection_le_five_sixths
      (hpos 0 hnPos) (hpi 0 hnPos)
  have hvariation :
      ‖∑ i ∈ Finset.range (n - 1),
          (rightPhaseCorrection (delta (i + 1)) -
            rightPhaseCorrection (delta i)) * u (i + 1)‖ ≤ 1 / 3 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1),
          ‖(rightPhaseCorrection (delta (i + 1)) -
            rightPhaseCorrection (delta i)) * u (i + 1)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (n - 1),
          ‖rightPhaseCorrection (delta (i + 1)) -
            rightPhaseCorrection (delta i)‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, hu, mul_one]
      _ ≤ 1 / 3 := sum_norm_rightPhaseCorrection_sub_le_one_third
        delta n hpos hpi hmono
  rw [show (∑ i ∈ Finset.range n,
      rightPhaseCorrection (delta i) *
        (Complex.exp (Complex.I * (theta (i + 1) : Complex)) -
          Complex.exp (Complex.I * (theta i : Complex)))) =
      rightPhaseCorrection (delta (n - 1)) * u n -
        rightPhaseCorrection (delta 0) * u 0 -
          ∑ i ∈ Finset.range (n - 1),
            (rightPhaseCorrection (delta (i + 1)) -
              rightPhaseCorrection (delta i)) * u (i + 1) by
      simpa [u] using hab]
  calc
    _ ≤ ‖rightPhaseCorrection (delta (n - 1)) * u n‖ +
          ‖rightPhaseCorrection (delta 0) * u 0‖ +
            ‖∑ i ∈ Finset.range (n - 1),
              (rightPhaseCorrection (delta (i + 1)) -
                rightPhaseCorrection (delta i)) * u (i + 1)‖ := by
      calc
        _ ≤ ‖rightPhaseCorrection (delta (n - 1)) * u n -
            rightPhaseCorrection (delta 0) * u 0‖ +
              ‖∑ i ∈ Finset.range (n - 1),
                (rightPhaseCorrection (delta (i + 1)) -
                  rightPhaseCorrection (delta i)) * u (i + 1)‖ :=
          norm_sub_le _ _
        _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ 5 / 6 + 5 / 6 + 1 / 3 :=
      add_le_add (add_le_add hterminal hinitial) hvariation
    _ = 2 := by norm_num

end Waring.Analytic
