import PrimesRestrictedDigits.PrimeNumberTheorem.PerronNearErrorBounds
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronVonMangoldtMass

/-!
# The quantitative right-line Perron remainder

This specializes the corrected Perron estimate to the line
`sigma = 1 + 1 / log x`, following the calculation after Eq. (6.16) in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, pp. 180--181.  The half-weight
von Mangoldt endpoint is kept outside the factor sixteen and is absorbed only
after the hypothesis `T <= x` is used.
-/

namespace PrimesRestrictedDigits

/--
The corrected weak Perron error is uniformly `O(x (log x)^2 / T)` on the right line `1 + 1 /
log x`. The absolute constant is chosen before `x` and `T`; the endpoint correction is
included.
-/
theorem exists_norm_psi_sub_zetaPerronIntegral_rightLine_le :
    ∃ P : Real, 0 < P ∧
      ∀ x T : Real, 4 <= x -> 2 <= T -> T <= x ->
        ‖(Chebyshev.psi x : Complex) -
            zetaPerronIntegral x (1 + 1 / Real.log x) T‖ <=
          P * x * Real.log x ^ 2 / T := by
  obtain ⟨B, hB, hMass⟩ := exists_perronCoefficientMass_vonMangoldt_bound
  refine ⟨289 + 96 * B, by nlinarith, ?_⟩
  intro x T hx hTLower hTx
  let L : Real := Real.log x
  let sigma : Real := 1 + 1 / L
  let Q : Real := x * L ^ 2 / T
  have hxOne : 1 <= x := by linarith
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
  have hFourPower : (4 : Real) ^ sigma <= x ^ sigma := by
    exact Real.rpow_le_rpow (by norm_num) hx hSigmaNonneg
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
          (((4 : Real) ^ sigma + x ^ sigma) / T) * ((B + 1) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hMassAtLine hFactorNonneg
      _ <= (6 * x / T) * ((B + 1) * L ^ 2) :=
        mul_le_mul_of_nonneg_right hFactor hCoeffNonneg
      _ = 6 * (B + 1) * Q := by
        dsimp [Q]
        ring
  have hEndpoint :
      vonMangoldtPerronEndpoint x <= Q := by
    have hEndpointLog := vonMangoldtPerronEndpoint_le_log hxOne
    have hLSq : L <= L ^ 2 := by nlinarith
    have hScaled : L ^ 2 <= (x / T) * L ^ 2 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hRatioOne (sq_nonneg L)
    calc
      vonMangoldtPerronEndpoint x <= L / 2 := by simpa [L] using hEndpointLog
      _ <= L ^ 2 := by nlinarith
      _ <= (x / T) * L ^ 2 := hScaled
      _ = Q := by dsimp [Q]; ring
  have hPerron :
      ‖(Chebyshev.psi x : Complex) -
          zetaPerronIntegral x sigma T‖ <=
        16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
          vonMangoldtPerronEndpoint x := by
    simpa [sigma] using
      (norm_psi_sub_zetaPerronIntegral_le
        (x := x) (sigma := sigma) (T := T) hxPos hSigmaOne hSigmaTwo hTPos)
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
      ‖(Chebyshev.psi x : Complex) -
          zetaPerronIntegral x sigma T‖ <=
        (289 + 96 * B) * Q := by
    calc
      ‖(Chebyshev.psi x : Complex) -
          zetaPerronIntegral x sigma T‖ <=
        16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
          vonMangoldtPerronEndpoint x := hPerron
      _ <= 16 * (12 * Q + 6 * (B + 1) * Q) + Q :=
        add_le_add hScaledInside hEndpoint
      _ = (289 + 96 * B) * Q := by ring
  dsimp [Q, L, sigma] at hFinal
  calc
    ‖(Chebyshev.psi x : Complex) -
        zetaPerronIntegral x (1 + 1 / Real.log x) T‖ <=
        (289 + 96 * B) * (x * Real.log x ^ 2 / T) := hFinal
    _ = (289 + 96 * B) * x * Real.log x ^ 2 / T := by ring

end PrimesRestrictedDigits
