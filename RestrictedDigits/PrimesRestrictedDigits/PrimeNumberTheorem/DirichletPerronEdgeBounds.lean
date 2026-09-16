import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronHorizontalBound
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronLeftBound
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrincipalPerronContour

/-!
# Quantitative bounds for the Dirichlet Perron contour

This module combines the horizontal and left-edge estimates with the exact
nonprincipal and principal contour identities from the proof of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16, printed pp. 378--379.
The free-height level logarithm and the factor `1 / (2 * pi)` remain explicit.
-/

open Complex

namespace PrimesRestrictedDigits

/-- The normalized nonprincipal Perron integral is bounded by both horizontal
edges and the complete upward left edge. -/
theorem DirichletPerronLogDerivBounds.norm_nonprincipalDirichletPerronIntegral_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hq : IsDecimalSmooth q) (hchi : chi ≠ 1)
    {x T : Real} (hx : 4 <= x) (hT : 2 <= T) :
    norm (dirichletPerronIntegral chi x
      (1 + 1 / Real.log x) T) <=
      (1 / (2 * Real.pi)) *
        (6 * C * x / T *
            (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) +
          8 * C * x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2) := by
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hLogPos : 0 < Real.log x := Real.log_pos hxOne
  have hSigma : 1 < 1 + 1 / Real.log x := by
    have hInvLogPos : 0 < 1 / Real.log x := one_div_pos.mpr hLogPos
    linarith
  have hTPos : 0 < T := by linarith
  have hTSplit : 7 / 8 <= T := by linarith
  have hBottom :
      norm (dirichletPerronHorizontalIntegral chi x
        (dirichletPerronLeftLine c q T) (1 + 1 / Real.log x) (-T)) <=
        3 * C * x / T *
          (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) := by
    apply h.norm_nonprincipalDirichletPerronHorizontalIntegral_le
      chi hq hchi hx hT
    simp [abs_of_nonneg hTPos.le]
  have hTop :
      norm (dirichletPerronHorizontalIntegral chi x
        (dirichletPerronLeftLine c q T) (1 + 1 / Real.log x) T) <=
        3 * C * x / T *
          (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) := by
    apply h.norm_nonprincipalDirichletPerronHorizontalIntegral_le
      chi hq hchi hx hT
    exact abs_of_nonneg hTPos.le
  have hLeft :
      norm (dirichletPerronVerticalIntegral chi x
        (dirichletPerronLeftLine c q T) T) <=
        8 * C * x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) ^ 2 :=
    h.norm_nonprincipalDirichletPerronLeftIntegral_le
      chi hq hchi hxPos hTSplit
  rw [dirichletPerronIntegral_eq_edges h.nonprincipalZeroFree chi hq hchi
    hxPos hSigma hTPos]
  have hEdges :
      norm
          (Complex.I *
              (dirichletPerronHorizontalIntegral chi x
                  (dirichletPerronLeftLine c q T)
                  (1 + 1 / Real.log x) (-T) -
                dirichletPerronHorizontalIntegral chi x
                  (dirichletPerronLeftLine c q T)
                  (1 + 1 / Real.log x) T) +
            dirichletPerronVerticalIntegral chi x
              (dirichletPerronLeftLine c q T) T) <=
        6 * C * x / T *
            (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) +
          8 * C * x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 := by
    calc
      _ <= norm
            (Complex.I *
              (dirichletPerronHorizontalIntegral chi x
                  (dirichletPerronLeftLine c q T)
                  (1 + 1 / Real.log x) (-T) -
                dirichletPerronHorizontalIntegral chi x
                  (dirichletPerronLeftLine c q T)
                  (1 + 1 / Real.log x) T)) +
          norm (dirichletPerronVerticalIntegral chi x
            (dirichletPerronLeftLine c q T) T) := norm_add_le _ _
      _ = norm
            (dirichletPerronHorizontalIntegral chi x
                (dirichletPerronLeftLine c q T)
                (1 + 1 / Real.log x) (-T) -
              dirichletPerronHorizontalIntegral chi x
                (dirichletPerronLeftLine c q T)
                (1 + 1 / Real.log x) T) +
          norm (dirichletPerronVerticalIntegral chi x
            (dirichletPerronLeftLine c q T) T) := by
        rw [norm_mul, Complex.norm_I, one_mul]
      _ <=
          (norm (dirichletPerronHorizontalIntegral chi x
              (dirichletPerronLeftLine c q T)
              (1 + 1 / Real.log x) (-T)) +
            norm (dirichletPerronHorizontalIntegral chi x
              (dirichletPerronLeftLine c q T)
              (1 + 1 / Real.log x) T)) +
          norm (dirichletPerronVerticalIntegral chi x
            (dirichletPerronLeftLine c q T) T) := by
        gcongr
        exact norm_sub_le _ _
      _ <=
          (3 * C * x / T *
                (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) +
            3 * C * x / T *
                (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5)) +
          8 * C * x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 :=
        add_le_add (add_le_add hBottom hTop) hLeft
      _ = 6 * C * x / T *
            (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) +
          8 * C * x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 := by ring
  have hScalePos : 0 < 1 / (2 * Real.pi) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hScalePos]
  exact mul_le_mul_of_nonneg_left hEdges hScalePos.le

/-- The normalized principal Perron integral differs from its residue `x` by
the two horizontal edges and the complete upward left edge. -/
theorem DirichletPerronLogDerivBounds.norm_principalDirichletPerronIntegral_sub_self_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q)
    {x T : Real} (hx : 4 <= x) (hT : 2 <= T) :
    norm (dirichletPerronIntegral
      (1 : DirichletCharacter Complex q) x
      (1 + 1 / Real.log x) T - (x : Complex)) <=
      (1 / (2 * Real.pi)) *
        (6 * (C + 8 * Real.log 5) * x / T *
            (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) +
          (8 * (C + 8 * Real.log 5) + 20 / c) *
            x ^ dirichletPerronLeftLine c q T *
              Real.log ((q : Real) * (T + 4)) ^ 2) := by
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hLogPos : 0 < Real.log x := Real.log_pos hxOne
  have hSigma : 1 < 1 + 1 / Real.log x := by
    have hInvLogPos : 0 < 1 / Real.log x := one_div_pos.mpr hLogPos
    linarith
  have hTPos : 0 < T := by linarith
  have hTSplit : 7 / 8 <= T := by linarith
  have hBottom :
      norm (dirichletPerronHorizontalIntegral
        (1 : DirichletCharacter Complex q) x
        (dirichletPerronLeftLine c q T) (1 + 1 / Real.log x) (-T)) <=
        3 * (C + 8 * Real.log 5) * x / T *
          (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) := by
    apply h.norm_principalDirichletPerronHorizontalIntegral_le hq hx hT
    simp [abs_of_nonneg hTPos.le]
  have hTop :
      norm (dirichletPerronHorizontalIntegral
        (1 : DirichletCharacter Complex q) x
        (dirichletPerronLeftLine c q T) (1 + 1 / Real.log x) T) <=
        3 * (C + 8 * Real.log 5) * x / T *
          (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) := by
    apply h.norm_principalDirichletPerronHorizontalIntegral_le hq hx hT
    exact abs_of_nonneg hTPos.le
  have hLeft :
      norm (dirichletPerronVerticalIntegral
        (1 : DirichletCharacter Complex q) x
        (dirichletPerronLeftLine c q T) T) <=
        (8 * (C + 8 * Real.log 5) + 20 / c) *
          x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 :=
    h.norm_principalDirichletPerronLeftIntegral_le hq hxPos hTSplit
  rw [principalDirichletPerronIntegral_sub_self_eq_edges
    h.riemannZetaZeroFree hxPos hSigma hTPos]
  have hEdges :
      norm
          (Complex.I *
              (dirichletPerronHorizontalIntegral
                  (1 : DirichletCharacter Complex q) x
                  (dirichletPerronLeftLine c q T)
                  (1 + 1 / Real.log x) (-T) -
                dirichletPerronHorizontalIntegral
                  (1 : DirichletCharacter Complex q) x
                  (dirichletPerronLeftLine c q T)
                  (1 + 1 / Real.log x) T) +
            dirichletPerronVerticalIntegral
              (1 : DirichletCharacter Complex q) x
              (dirichletPerronLeftLine c q T) T) <=
        6 * (C + 8 * Real.log 5) * x / T *
            (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) +
          (8 * (C + 8 * Real.log 5) + 20 / c) *
            x ^ dirichletPerronLeftLine c q T *
              Real.log ((q : Real) * (T + 4)) ^ 2 := by
    calc
      _ <= norm
            (Complex.I *
              (dirichletPerronHorizontalIntegral
                  (1 : DirichletCharacter Complex q) x
                  (dirichletPerronLeftLine c q T)
                  (1 + 1 / Real.log x) (-T) -
                dirichletPerronHorizontalIntegral
                  (1 : DirichletCharacter Complex q) x
                  (dirichletPerronLeftLine c q T)
                  (1 + 1 / Real.log x) T)) +
          norm (dirichletPerronVerticalIntegral
            (1 : DirichletCharacter Complex q) x
            (dirichletPerronLeftLine c q T) T) := norm_add_le _ _
      _ = norm
            (dirichletPerronHorizontalIntegral
                (1 : DirichletCharacter Complex q) x
                (dirichletPerronLeftLine c q T)
                (1 + 1 / Real.log x) (-T) -
              dirichletPerronHorizontalIntegral
                (1 : DirichletCharacter Complex q) x
                (dirichletPerronLeftLine c q T)
                (1 + 1 / Real.log x) T) +
          norm (dirichletPerronVerticalIntegral
            (1 : DirichletCharacter Complex q) x
            (dirichletPerronLeftLine c q T) T) := by
        rw [norm_mul, Complex.norm_I, one_mul]
      _ <=
          (norm (dirichletPerronHorizontalIntegral
              (1 : DirichletCharacter Complex q) x
              (dirichletPerronLeftLine c q T)
              (1 + 1 / Real.log x) (-T)) +
            norm (dirichletPerronHorizontalIntegral
              (1 : DirichletCharacter Complex q) x
              (dirichletPerronLeftLine c q T)
              (1 + 1 / Real.log x) T)) +
          norm (dirichletPerronVerticalIntegral
            (1 : DirichletCharacter Complex q) x
            (dirichletPerronLeftLine c q T) T) := by
        gcongr
        exact norm_sub_le _ _
      _ <=
          (3 * (C + 8 * Real.log 5) * x / T *
                (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) +
            3 * (C + 8 * Real.log 5) * x / T *
                (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5)) +
          (8 * (C + 8 * Real.log 5) + 20 / c) *
            x ^ dirichletPerronLeftLine c q T *
              Real.log ((q : Real) * (T + 4)) ^ 2 :=
        add_le_add (add_le_add hBottom hTop) hLeft
      _ = 6 * (C + 8 * Real.log 5) * x / T *
            (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) +
          (8 * (C + 8 * Real.log 5) + 20 / c) *
            x ^ dirichletPerronLeftLine c q T *
              Real.log ((q : Real) * (T + 4)) ^ 2 := by ring
  have hScalePos : 0 < 1 / (2 * Real.pi) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hScalePos]
  exact mul_le_mul_of_nonneg_left hEdges hScalePos.le

end PrimesRestrictedDigits
