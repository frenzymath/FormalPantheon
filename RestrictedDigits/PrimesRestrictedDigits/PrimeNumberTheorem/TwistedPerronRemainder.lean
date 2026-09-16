import PrimesRestrictedDigits.PrimeNumberTheorem.PerronVonMangoldtRemainder
import PrimesRestrictedDigits.PrimeNumberTheorem.TwistedPerron

/-!
# Uniform right-line remainder for twisted Perron integrals

The character bound `|chi(n)| <= 1` lets every absolute Perron error for
`chi(n) * Lambda(n)` be dominated by the corresponding untwisted error.
The domination and resulting explicit coefficient are project-derived from
the kernel-checked untwisted Perron remainder modules.
-/

namespace PrimesRestrictedDigits

private theorem norm_twist_vonMangoldt_le
    {q n : Nat} (chi : DirichletCharacter Complex q) :
    ‖chi n * (ArithmeticFunction.vonMangoldt n : Complex)‖ <=
      ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ := by
  rw [norm_mul]
  calc
    ‖chi n‖ * ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ <=
        1 * ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ := by
      exact mul_le_mul_of_nonneg_right
        (chi.norm_le_one n) (norm_nonneg _)
    _ = ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ := one_mul _

/-- The norm of the twisted half-weight endpoint is at most half the
logarithm of the cutoff. -/
theorem norm_dirichletVonMangoldtPerronEndpoint_le_log
    {q : Nat} (chi : DirichletCharacter Complex q)
    {x : Real} (hx : 1 <= x) :
    ‖dirichletVonMangoldtPerronEndpoint chi x‖ <= Real.log x / 2 := by
  rw [dirichletVonMangoldtPerronEndpoint]
  split_ifs with hfloor
  · have hLambda := ArithmeticFunction.vonMangoldt_le_log
      (n := ⌊x⌋₊)
    rw [hfloor] at hLambda
    have hLambdaNonneg := ArithmeticFunction.vonMangoldt_nonneg
      (n := ⌊x⌋₊)
    rw [norm_div, norm_mul]
    norm_num
    rw [abs_of_nonneg hLambdaNonneg]
    calc
      ‖chi (Nat.floor x)‖ * ArithmeticFunction.vonMangoldt (Nat.floor x) / 2 <=
          1 * ArithmeticFunction.vonMangoldt (Nat.floor x) / 2 := by
        gcongr
        exact chi.norm_le_one _
      _ = ArithmeticFunction.vonMangoldt (Nat.floor x) / 2 := by ring
      _ <= Real.log x / 2 :=
        div_le_div_of_nonneg_right hLambda (by norm_num)
  · rw [norm_zero]
    exact div_nonneg (Real.log_nonneg hx) (by norm_num)

/-- Twisting by a Dirichlet character cannot increase the strict
near-diagonal Perron error. -/
theorem perronNearErrorSum_twist_vonMangoldt_le
    {q : Nat} (chi : DirichletCharacter Complex q)
    {x T : Real} (hx : 0 < x) (hT : 0 < T) :
    perronNearErrorSum
        (fun n => chi n *
          (ArithmeticFunction.vonMangoldt n : Complex)) x T <=
      perronNearErrorSum
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T := by
  rw [perronNearErrorSum, perronNearErrorSum]
  apply (summable_perronNearErrorTerm
    (fun n => chi n * (ArithmeticFunction.vonMangoldt n : Complex))
      x T).tsum_le_tsum
  · intro n
    by_cases hn : n = 0
    · simp [perronNearErrorTerm, hn]
    · rw [perronNearErrorTerm, perronNearErrorTerm, if_neg hn, if_neg hn]
      have hnear : 0 <= perronNearError x T n := by
        have hnonneg := perronNearErrorTerm_nonneg
          (a := fun _ => (1 : Complex)) hx hT n
        simpa [perronNearErrorTerm, hn] using hnonneg
      exact mul_le_mul_of_nonneg_right
        (norm_twist_vonMangoldt_le chi) hnear
  · exact summable_perronNearErrorTerm
      (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T

/-- Twisting by a Dirichlet character cannot increase the absolute
coefficient mass on a line to the right of one. -/
theorem perronCoefficientMass_twist_vonMangoldt_le
    {q : Nat} (chi : DirichletCharacter Complex q)
    {sigma : Real} (hsigma : 1 < sigma) :
    perronCoefficientMass
        (fun n => chi n *
          (ArithmeticFunction.vonMangoldt n : Complex)) sigma <=
      perronCoefficientMass
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma := by
  have htwist : LSeriesSummable
      ((fun n : Nat => chi n) *
        fun n => (ArithmeticFunction.vonMangoldt n : Complex))
      (sigma : Complex) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi
      (by simpa using hsigma)
  have hbase : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
      (sigma : Complex) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt
      (by simpa using hsigma)
  rw [perronCoefficientMass, perronCoefficientMass]
  apply (LSeriesSummable.summable_perronCoefficientMassTerm
    htwist).tsum_le_tsum
  · intro n
    by_cases hn : n = 0
    · simp [perronCoefficientMassTerm, hn]
    · rw [perronCoefficientMassTerm, perronCoefficientMassTerm,
        if_neg hn, if_neg hn]
      exact div_le_div_of_nonneg_right
        (norm_twist_vonMangoldt_le chi)
        (Real.rpow_nonneg (Nat.cast_nonneg n) sigma)
  · exact LSeriesSummable.summable_perronCoefficientMassTerm hbase

/-- The twisted weak sum has the same explicit Perron error expression as
the untwisted von Mangoldt sum. -/
theorem norm_dirichletVonMangoldtSum_sub_integral_le_log
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {x sigma T : Real} (hx : 1 <= x) (hsigma : 1 < sigma)
    (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖dirichletVonMangoldtSum chi x -
        dirichletPerronIntegral chi x sigma T‖ <=
      16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
        Real.log x / 2 := by
  have hmain := norm_dirichletVonMangoldtSum_sub_integral_le
    chi (zero_lt_one.trans_le hx) hsigma hsigma2 hT
  have hnear := perronNearErrorSum_twist_vonMangoldt_le
    chi (zero_lt_one.trans_le hx) hT
  have hmass := perronCoefficientMass_twist_vonMangoldt_le chi hsigma
  have hfactor :
      0 <= ((4 : Real) ^ sigma + x ^ sigma) / T := by positivity
  calc
    ‖dirichletVonMangoldtSum chi x -
        dirichletPerronIntegral chi x sigma T‖ <=
      16 * (perronNearErrorSum
          (fun n => chi n *
            (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => chi n *
              (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
        ‖dirichletVonMangoldtPerronEndpoint chi x‖ := hmain
    _ <= 16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
        Real.log x / 2 := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add hnear
          (mul_le_mul_of_nonneg_left hmass hfactor)
      · exact norm_dirichletVonMangoldtPerronEndpoint_le_log chi hx

/-- On the standard line `sigma = 1 + 1 / log x`, one absolute Perron
coefficient works for every positive level and every Dirichlet character. -/
theorem exists_norm_dirichletVonMangoldtSum_sub_integral_rightLine_le :
    ∃ P : Real, 0 < P ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
        (x T : Real),
        4 <= x -> 2 <= T -> T <= x ->
        ‖dirichletVonMangoldtSum chi x -
            dirichletPerronIntegral chi x
              (1 + 1 / Real.log x) T‖ <=
          P * x * Real.log x ^ 2 / T := by
  obtain ⟨B, hB, hMass⟩ := exists_perronCoefficientMass_vonMangoldt_bound
  refine ⟨289 + 96 * B, by nlinarith, ?_⟩
  intro q inst chi x T hx hTLower hTx
  let L : Real := Real.log x
  let sigma : Real := 1 + 1 / L
  let Q : Real := x * L ^ 2 / T
  have hxPos : 0 < x := by linarith
  have hxNeOne : x ≠ 1 := by linarith
  have hTPos : 0 < T := by linarith
  have hLogFour : 1 < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three.trans (by norm_num)
  have hLOne : 1 <= L := by
    have hLogMonotone : Real.log 4 <= Real.log x :=
      Real.log_le_log (by norm_num) hx
    dsimp [L]
    exact (hLogFour.trans_le hLogMonotone).le
  have hLPos : 0 < L := lt_of_lt_of_le zero_lt_one hLOne
  have hInvLPos : 0 < 1 / L := one_div_pos.mpr hLPos
  have hSigmaOne : 1 < sigma := by
    dsimp [sigma]
    linarith
  have hSigmaTwo : sigma <= 2 := by
    dsimp [sigma]
    have hInvLLe : 1 / L <= 1 :=
      (div_le_iff₀ hLPos).2 (by linarith)
    linarith
  have hRatioOne : 1 <= x / T := (one_le_div hTPos).2 hTx
  have hNear :
      perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T <=
        12 * Q := by
    have h := perronNearErrorSum_vonMangoldt_le hx hTPos hTx
    calc
      perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T <=
          12 * x * Real.log x ^ 2 / T := h
      _ = 12 * Q := by dsimp [Q, L]; ring
  have hMassAtLine :
      perronCoefficientMass
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma <=
        (B + 1) * L ^ 2 := by
    have hDelta := hMass (1 / L) hInvLPos
      ((div_le_iff₀ hLPos).2 (by linarith))
    have hMassRaw :
        perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
              (1 + 1 / L) <= 1 / (1 / L) + B := by
      simpa [sigma] using hDelta
    have hMassLB :
        perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma <=
          L + B := by
      calc
        perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma <=
            1 / (1 / L) + B := by simpa [sigma] using hMassRaw
        _ = L + B := by field_simp [hLPos.ne']
    have hLSq : L <= L ^ 2 := by nlinarith
    have hOneLSq : 1 <= L ^ 2 := by nlinarith
    have hBLSq : B <= B * L ^ 2 := by
      calc
        B = B * 1 := by ring
        _ <= B * L ^ 2 :=
          mul_le_mul_of_nonneg_left hOneLSq hB.le
    calc
      perronCoefficientMass
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma <=
          L + B := hMassLB
      _ <= L ^ 2 + B * L ^ 2 := add_le_add hLSq hBLSq
      _ = (B + 1) * L ^ 2 := by ring
  have hPower : x ^ sigma < 3 * x := by
    dsimp [sigma]
    rw [Real.rpow_add hxPos, Real.rpow_one, one_div,
      Real.rpow_inv_log hxPos hxNeOne]
    nlinarith [Real.exp_one_lt_three]
  have hSigmaNonneg : 0 <= sigma := by linarith
  have hFourPower : (4 : Real) ^ sigma <= x ^ sigma :=
    Real.rpow_le_rpow (by norm_num) hx hSigmaNonneg
  have hPowerSum : (4 : Real) ^ sigma + x ^ sigma <= 6 * x := by
    nlinarith
  have hGlobal :
      (((4 : Real) ^ sigma + x ^ sigma) / T) *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma <=
        6 * (B + 1) * Q := by
    have hFactorNonneg :
        0 <= ((4 : Real) ^ sigma + x ^ sigma) / T := by positivity
    have hCoeffNonneg : 0 <= (B + 1) * L ^ 2 := by positivity
    have hFactor :
        ((4 : Real) ^ sigma + x ^ sigma) / T <= 6 * x / T :=
      div_le_div_of_nonneg_right hPowerSum hTPos.le
    calc
      (((4 : Real) ^ sigma + x ^ sigma) / T) *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma <=
          (((4 : Real) ^ sigma + x ^ sigma) / T) *
            ((B + 1) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hMassAtLine hFactorNonneg
      _ <= (6 * x / T) * ((B + 1) * L ^ 2) :=
        mul_le_mul_of_nonneg_right hFactor hCoeffNonneg
      _ = 6 * (B + 1) * Q := by dsimp [Q]; ring
  have hLogEndpoint : Real.log x / 2 <= Q := by
    have hLSq : L <= L ^ 2 := by nlinarith
    have hScaled : L ^ 2 <= (x / T) * L ^ 2 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hRatioOne (sq_nonneg L)
    calc
      Real.log x / 2 <= L ^ 2 := by dsimp [L]; nlinarith
      _ <= (x / T) * L ^ 2 := hScaled
      _ = Q := by dsimp [Q]; ring
  have hPerron := norm_dirichletVonMangoldtSum_sub_integral_le_log
    chi (by linarith : 1 <= x) hSigmaOne hSigmaTwo hTPos
  have hInside :
      perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma <=
        12 * Q + 6 * (B + 1) * Q := add_le_add hNear hGlobal
  have hScaledInside :
      16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) <=
        16 * (12 * Q + 6 * (B + 1) * Q) :=
    mul_le_mul_of_nonneg_left hInside (by norm_num)
  have hFinal :
      ‖dirichletVonMangoldtSum chi x -
          dirichletPerronIntegral chi x sigma T‖ <=
        (289 + 96 * B) * Q := by
    calc
      ‖dirichletVonMangoldtSum chi x -
          dirichletPerronIntegral chi x sigma T‖ <=
        16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
          Real.log x / 2 := by simpa [sigma] using hPerron
      _ <= 16 * (12 * Q + 6 * (B + 1) * Q) + Q :=
        add_le_add hScaledInside hLogEndpoint
      _ = (289 + 96 * B) * Q := by ring
  dsimp [Q, L, sigma] at hFinal
  calc
    ‖dirichletVonMangoldtSum chi x -
        dirichletPerronIntegral chi x (1 + 1 / Real.log x) T‖ <=
      (289 + 96 * B) * (x * Real.log x ^ 2 / T) := hFinal
    _ = (289 + 96 * B) * x * Real.log x ^ 2 / T := by ring

end PrimesRestrictedDigits
