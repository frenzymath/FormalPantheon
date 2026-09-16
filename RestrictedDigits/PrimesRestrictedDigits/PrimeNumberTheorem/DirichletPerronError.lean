import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronComposition
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronLevelHeight

/-!
# The source-facing Dirichlet Perron error

This module simplifies the exact raw branch bounds under explicit comparisons
between the level, height, and cutoff.  The result is the decimal-smooth,
no-exceptional-zero version of `MONTGOMERY-VAUGHAN-MNT-I`, Eq. (11.26),
printed p. 378.
-/

namespace PrimesRestrictedDigits

/-- There are common constants for the principal and nonprincipal repaired
forms of the source's free-height Dirichlet Perron estimate. -/
theorem exists_norm_dirichletVonMangoldtSum_source_branches_le :
    ∃ c K : Real,
      IsRiemannZetaZeroFreeConstant c ∧ 0 < K ∧
      (∀ {q : Nat} [NeZero q]
          (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q → chi ≠ 1 →
        ∀ x T : Real,
          4 ≤ x → 2 ≤ T → T ≤ x → (q : Real) ≤ x →
          norm (dirichletVonMangoldtSum chi x) ≤
            K * x * Real.log x ^ 2 *
              (1 / T + Real.exp
                (-c * Real.log x /
                  (5 * Real.log ((q : Real) * (T + 4)))))) ∧
      (∀ {q : Nat} [NeZero q],
        IsDecimalSmooth q →
        ∀ x T : Real,
          4 ≤ x → 2 ≤ T → T ≤ x → (q : Real) ≤ x →
          norm (dirichletVonMangoldtSum
              (1 : DirichletCharacter Complex q) x - (x : Complex)) ≤
            K * x * Real.log x ^ 2 *
              (1 / T + Real.exp
                (-c * Real.log x /
                  (5 * Real.log ((q : Real) * (T + 4)))))) := by
  obtain ⟨c, C, h⟩ := exists_dirichletPerronLogDerivBounds
  obtain ⟨P, hP, hNonprincipalRaw, hPrincipalRaw⟩ :=
    h.exists_norm_dirichletVonMangoldtSum_branches_le
  let A : Real := C + 8 * Real.log 5
  let K : Real := P + 50 * A + 125 / c
  have hcPos : 0 < c := h.riemannZetaZeroFree.1
  have hCPos : 0 < C := h.bound_pos
  have hAPos : 0 < A := by
    dsimp [A]
    positivity
  have hInvTermPos : 0 < 125 / c := div_pos (by norm_num) hcPos
  have hKPos : 0 < K := by
    dsimp [K]
    nlinarith
  have hSource :
      ∀ {q : Nat} [NeZero q] (z : Complex) (D E x T : Real),
        4 ≤ x → 2 ≤ T → T ≤ x → (q : Real) ≤ x →
        0 ≤ D → 0 ≤ E →
        P + 18 * D ≤ K → (25 / 4 : Real) * E ≤ K →
        norm z ≤
          P * x * Real.log x ^ 2 / T +
            (1 / (2 * Real.pi)) *
              (6 * D * x / T *
                  (Real.log ((q : Real) * (T + 4)) /
                      Real.log x + c / 5) +
                E * x ^ dirichletPerronLeftLine c q T *
                  Real.log ((q : Real) * (T + 4)) ^ 2) →
        norm z ≤
          K * x * Real.log x ^ 2 *
            (1 / T + Real.exp
              (-c * Real.log x /
                (5 * Real.log ((q : Real) * (T + 4))))) := by
    intro q inst z D E x T hx hT hTx hqx hD hE hCoeffQ hCoeffR hRaw
    let ell : Real := Real.log x
    let L : Real := Real.log ((q : Real) * (T + 4))
    let decay : Real := Real.exp (-c * ell / (5 * L))
    let Q : Real := x * ell ^ 2 / T
    let R : Real := x * ell ^ 2 * decay
    have hxPos : 0 < x := by linarith
    have hTPos : 0 < T := by linarith
    have hqPos : (0 : Real) < q := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hEllFour : Real.log 4 ≤ ell := by
      dsimp [ell]
      exact Real.log_le_log (by norm_num) hx
    have hLogFour : 1 < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three.trans (by norm_num)
    have hEllOne : 1 ≤ ell := (hLogFour.trans_le hEllFour).le
    have hEllPos : 0 < ell := lt_of_lt_of_le zero_lt_one hEllOne
    have hArgumentFour :
        (4 : Real) ≤ (q : Real) * (T + 4) := by
      have hqOne : (1 : Real) ≤ q := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      calc
        (4 : Real) = 1 * 4 := by ring
        _ ≤ (q : Real) * (T + 4) :=
          mul_le_mul hqOne (by linarith) (by norm_num) hqPos.le
    have hArgumentPos : 0 < (q : Real) * (T + 4) := by
      linarith
    have hLOne : 1 < L := by
      dsimp [L]
      rw [Real.lt_log_iff_exp_lt hArgumentPos]
      exact Real.exp_one_lt_three.trans (by linarith)
    have hLPos : 0 < L := zero_lt_one.trans hLOne
    have hLUpper : L ≤ (5 / 2 : Real) * ell := by
      dsimp [L, ell]
      exact log_level_mul_height_add_four_le_five_halves_log
        hx hT hTx hqx
    have hLDiv : L / ell ≤ (5 / 2 : Real) := by
      exact (div_le_iff₀ hEllPos).2 (by simpa [mul_comm] using hLUpper)
    have hcFifth : c / 5 ≤ (1 / 2 : Real) := by
      nlinarith [h.riemannZetaZeroFree.2.1]
    have hWidth : L / ell + c / 5 ≤ 3 := by linarith
    have hWidthNonneg : 0 ≤ L / ell + c / 5 := by positivity
    have hEllSqOne : 1 ≤ ell ^ 2 := by nlinarith
    have hLBoundNonneg : 0 ≤ (5 / 2 : Real) * ell := by positivity
    have hLSqRaw : L ^ 2 ≤ ((5 / 2 : Real) * ell) ^ 2 :=
      (sq_le_sq₀ hLPos.le hLBoundNonneg).2 hLUpper
    have hLSq : L ^ 2 ≤ (25 / 4 : Real) * ell ^ 2 := by
      nlinarith
    have hDecayPos : 0 < decay := by
      dsimp [decay]
      positivity
    have hQNonneg : 0 ≤ Q := by
      dsimp [Q]
      positivity
    have hRNonneg : 0 ≤ R := by
      dsimp [R]
      positivity
    have hDivNonneg : 0 ≤ x / T := div_nonneg hxPos.le hTPos.le
    have hDivLeQ : x / T ≤ Q := by
      calc
        x / T = (x / T) * 1 := by ring
        _ ≤ (x / T) * ell ^ 2 :=
          mul_le_mul_of_nonneg_left hEllSqOne hDivNonneg
        _ = Q := by dsimp [Q]; ring
    have hAlphaLe : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 2 * Real.pi)]
      nlinarith [Real.pi_gt_three]
    have hHorizontalNonneg :
        0 ≤ 6 * D * x / T * (L / ell + c / 5) := by positivity
    have hHorizontalCore :
        6 * D * x / T * (L / ell + c / 5) ≤ 18 * D * Q := by
      calc
        6 * D * x / T * (L / ell + c / 5) =
            (6 * D * (x / T)) * (L / ell + c / 5) := by ring
        _ ≤ (6 * D * (x / T)) * 3 :=
          mul_le_mul_of_nonneg_left hWidth (by positivity)
        _ = 18 * D * (x / T) := by ring
        _ ≤ 18 * D * Q :=
          mul_le_mul_of_nonneg_left hDivLeQ (by positivity)
    have hHorizontal :
        (1 / (2 * Real.pi)) *
            (6 * D * x / T * (L / ell + c / 5)) ≤
          18 * D * Q := by
      calc
        (1 / (2 * Real.pi)) *
            (6 * D * x / T * (L / ell + c / 5)) ≤
            1 * (6 * D * x / T * (L / ell + c / 5)) :=
          mul_le_mul_of_nonneg_right hAlphaLe hHorizontalNonneg
        _ ≤ 18 * D * Q := by simpa using hHorizontalCore
    have hPower :
        x ^ dirichletPerronLeftLine c q T = x * decay := by
      simpa [decay, ell, L] using
        (rpow_dirichletPerronLeftLine_eq_mul_exp
          (c := c) (q := q) (T := T) hxPos)
    have hLeftNonneg :
        0 ≤ E * x ^ dirichletPerronLeftLine c q T * L ^ 2 := by positivity
    have hLeftCore :
        E * x ^ dirichletPerronLeftLine c q T * L ^ 2 ≤
          (25 / 4 : Real) * E * R := by
      calc
        E * x ^ dirichletPerronLeftLine c q T * L ^ 2 =
            (E * x * decay) * L ^ 2 := by rw [hPower]; ring
        _ ≤ (E * x * decay) * ((25 / 4 : Real) * ell ^ 2) :=
          mul_le_mul_of_nonneg_left hLSq (by positivity)
        _ = (25 / 4 : Real) * E * R := by
          dsimp [R]
          ring
    have hLeft :
        (1 / (2 * Real.pi)) *
            (E * x ^ dirichletPerronLeftLine c q T * L ^ 2) ≤
          (25 / 4 : Real) * E * R := by
      calc
        (1 / (2 * Real.pi)) *
            (E * x ^ dirichletPerronLeftLine c q T * L ^ 2) ≤
            1 * (E * x ^ dirichletPerronLeftLine c q T * L ^ 2) :=
          mul_le_mul_of_nonneg_right hAlphaLe hLeftNonneg
        _ ≤ (25 / 4 : Real) * E * R := by simpa using hLeftCore
    have hRaw' :
        norm z ≤ P * Q +
          (1 / (2 * Real.pi)) *
            (6 * D * x / T * (L / ell + c / 5) +
              E * x ^ dirichletPerronLeftLine c q T * L ^ 2) := by
      calc
        norm z ≤
            P * x * Real.log x ^ 2 / T +
              (1 / (2 * Real.pi)) *
                (6 * D * x / T *
                    (Real.log ((q : Real) * (T + 4)) /
                        Real.log x + c / 5) +
                  E * x ^ dirichletPerronLeftLine c q T *
                    Real.log ((q : Real) * (T + 4)) ^ 2) := hRaw
        _ = P * Q +
            (1 / (2 * Real.pi)) *
              (6 * D * x / T * (L / ell + c / 5) +
                E * x ^ dirichletPerronLeftLine c q T * L ^ 2) := by
          dsimp [Q, L, ell]
          ring
    calc
      norm z ≤ P * Q +
          (1 / (2 * Real.pi)) *
            (6 * D * x / T * (L / ell + c / 5) +
              E * x ^ dirichletPerronLeftLine c q T * L ^ 2) := hRaw'
      _ = P * Q +
          ((1 / (2 * Real.pi)) *
              (6 * D * x / T * (L / ell + c / 5)) +
            (1 / (2 * Real.pi)) *
              (E * x ^ dirichletPerronLeftLine c q T * L ^ 2)) := by ring
      _ ≤ P * Q + (18 * D * Q + (25 / 4 : Real) * E * R) :=
        add_le_add le_rfl (add_le_add hHorizontal hLeft)
      _ = (P + 18 * D) * Q + ((25 / 4 : Real) * E) * R := by ring
      _ ≤ K * Q + K * R :=
        add_le_add
          (mul_le_mul_of_nonneg_right hCoeffQ hQNonneg)
          (mul_le_mul_of_nonneg_right hCoeffR hRNonneg)
      _ = K * x * Real.log x ^ 2 *
          (1 / T + Real.exp
            (-c * Real.log x /
              (5 * Real.log ((q : Real) * (T + 4))))) := by
        dsimp [Q, R, decay, ell, L]
        ring
  refine ⟨c, K, h.riemannZetaZeroFree, hKPos, ?_, ?_⟩
  · intro q inst chi hq hchi x T hx hT hTx hqx
    have hD : 0 ≤ C := hCPos.le
    have hE : 0 ≤ 8 * C := by positivity
    have hCoeffQ : P + 18 * C ≤ K := by
      dsimp [K, A]
      nlinarith [Real.log_pos (by norm_num : (1 : Real) < 5), hInvTermPos]
    have hCoeffR : (25 / 4 : Real) * (8 * C) ≤ K := by
      dsimp [K, A]
      nlinarith [Real.log_pos (by norm_num : (1 : Real) < 5), hInvTermPos]
    exact hSource (z := dirichletVonMangoldtSum chi x)
      C (8 * C) x T hx hT hTx hqx hD hE hCoeffQ hCoeffR
      (hNonprincipalRaw chi hq hchi x T hx hT hTx)
  · intro q inst hq x T hx hT hTx hqx
    have hE : 0 ≤ 8 * A + 20 / c := by positivity
    have hCoeffQ : P + 18 * A ≤ K := by
      dsimp [K]
      nlinarith
    have hCoeffR :
        (25 / 4 : Real) * (8 * A + 20 / c) ≤ K := by
      dsimp [K]
      ring_nf
      linarith
    exact hSource
      (z := dirichletVonMangoldtSum
        (1 : DirichletCharacter Complex q) x - (x : Complex))
      A (8 * A + 20 / c) x T hx hT hTx hqx hAPos.le hE hCoeffQ hCoeffR
      (hPrincipalRaw hq x T hx hT hTx)

end PrimesRestrictedDigits
