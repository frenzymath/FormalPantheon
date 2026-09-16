import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletNonprincipalPerronContour
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronIntegrability
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronLeftHigh
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronLeftMiddle

/-!
# The left edge of the Dirichlet Perron contour

The complete upward left edge is split at heights `-7 / 8` and `7 / 8` only
after genuine integrability has been established. The estimates implement the
edge argument used after Eq. (11.25) of `MONTGOMERY-VAUGHAN-MNT-I`, printed
pp. 378--379.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private theorem norm_dirichletPerronVerticalIntegral_le_of_pieces
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {x sigma T Bneg Bmid Bpos : Real} (hT : 7 / 8 <= T)
    (hIntegrable : IntervalIntegrable
      (fun t : Real => logDerivPerronIntegrand chi.LFunction x
        ((sigma : Complex) + Complex.I * (t : Complex))) volume (-T) T)
    (hneg : norm (∫ t in -T..(-7 / 8 : Real),
      logDerivPerronIntegrand chi.LFunction x
        ((sigma : Complex) + Complex.I * (t : Complex))) <= Bneg)
    (hmid : norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real),
      logDerivPerronIntegrand chi.LFunction x
        ((sigma : Complex) + Complex.I * (t : Complex))) <= Bmid)
    (hpos : norm (∫ t in (7 / 8 : Real)..T,
      logDerivPerronIntegrand chi.LFunction x
        ((sigma : Complex) + Complex.I * (t : Complex))) <= Bpos) :
    norm (dirichletPerronVerticalIntegral chi x sigma T) <=
      Bneg + Bmid + Bpos := by
  let f : Real -> Complex := fun t => logDerivPerronIntegrand chi.LFunction x
    ((sigma : Complex) + Complex.I * (t : Complex))
  have hOrder : -T <= T := by linarith
  have hIntegrableF : IntervalIntegrable f volume (-T) T := by
    simpa only [f] using hIntegrable
  have hMinusMem : (-7 / 8 : Real) ∈ Set.uIcc (-T) T := by
    rw [uIcc_of_le hOrder, Set.mem_Icc]
    constructor <;> linarith
  have hNegRest := (IntervalIntegrable.trans_iff hMinusMem).1 hIntegrableF
  have hPlusMem : (7 / 8 : Real) ∈ Set.uIcc (-7 / 8) T := by
    rw [uIcc_of_le (by linarith : (-7 / 8 : Real) <= T), Set.mem_Icc]
    constructor <;> linarith
  have hMiddlePos := (IntervalIntegrable.trans_iff hPlusMem).1 hNegRest.2
  have hDecomposition :
      (∫ t in -T..T, f t) =
        (∫ t in -T..(-7 / 8 : Real), f t) +
          (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) +
            ∫ t in (7 / 8 : Real)..T, f t := by
    calc
      (∫ t in -T..T, f t) =
          (∫ t in -T..(-7 / 8 : Real), f t) +
            ∫ t in (-7 / 8 : Real)..T, f t :=
        (intervalIntegral.integral_add_adjacent_intervals
          hNegRest.1 hNegRest.2).symm
      _ = _ := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hMiddlePos.1 hMiddlePos.2]
        ring
  rw [dirichletPerronVerticalIntegral, logDerivPerronVerticalIntegral]
  change norm (∫ t in -T..T, f t) <= _
  rw [hDecomposition]
  calc
    norm ((∫ t in -T..(-7 / 8 : Real), f t) +
        (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) +
          ∫ t in (7 / 8 : Real)..T, f t) <=
        (norm (∫ t in -T..(-7 / 8 : Real), f t) +
          norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t)) +
            norm (∫ t in (7 / 8 : Real)..T, f t) := by
      calc
        norm ((∫ t in -T..(-7 / 8 : Real), f t) +
            (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) +
              ∫ t in (7 / 8 : Real)..T, f t) <=
            norm ((∫ t in -T..(-7 / 8 : Real), f t) +
              ∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) +
                norm (∫ t in (7 / 8 : Real)..T, f t) := norm_add_le _ _
        _ <= _ := by
          gcongr
          exact norm_add_le _ _
    _ <= (Bneg + Bmid) + Bpos := by
      simpa only [f] using add_le_add (add_le_add hneg hmid) hpos
    _ = Bneg + Bmid + Bpos := by ring

/-- The complete upward left edge for a decimal-smooth nonprincipal
character has the explicit q-dependent square-logarithm bound. -/
theorem DirichletPerronLogDerivBounds.norm_nonprincipalDirichletPerronLeftIntegral_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hq : IsDecimalSmooth q) (hchi : chi ≠ 1)
    {x T : Real} (hx : 0 < x) (hT : 7 / 8 <= T) :
    norm (dirichletPerronVerticalIntegral chi x
      (dirichletPerronLeftLine c q T) T) <=
      8 * C * x ^ dirichletPerronLeftLine c q T *
        Real.log ((q : Real) * (T + 4)) ^ 2 := by
  let f : Real -> Complex := fun t => logDerivPerronIntegrand chi.LFunction x
    ((dirichletPerronLeftLine c q T : Complex) +
      Complex.I * (t : Complex))
  have hTPos : 0 < T := by linarith
  have hIntegrable : IntervalIntegrable f volume (-T) T := by
    simpa only [f] using
      h.intervalIntegrable_dirichletPerronIntegrand_left chi hq hx hTPos
  have hNegative :
      norm (∫ t in -T..(-7 / 8 : Real), f t) <=
        2 * C * x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by
    have hTail :=
      DirichletPerronLeftPieces.norm_nonprincipalDirichletPerronHighTail_le
        h chi hq hchi hx hT (epsilon := -1) (Or.inr rfl)
    have hReflect := intervalIntegral.integral_comp_neg
      (f := f) (a := (7 / 8 : Real)) (b := T)
    rw [show (-7 / 8 : Real) = -(7 / 8 : Real) by ring, ← hReflect]
    simpa only [f, neg_mul, one_mul, Complex.ofReal_neg] using hTail
  have hPositive :
      norm (∫ t in (7 / 8 : Real)..T, f t) <=
        2 * C * x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by
    simpa only [f, one_mul] using
      (DirichletPerronLeftPieces.norm_nonprincipalDirichletPerronHighTail_le
        h chi hq hchi hx hT (epsilon := 1) (Or.inl rfl))
  have hMiddle :
      norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) <=
        4 * C * x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by
    simpa only [f] using
      DirichletPerronLeftPieces.norm_nonprincipalDirichletPerronMiddle_le
        h chi hq hchi hx hT
  have hPieces := norm_dirichletPerronVerticalIntegral_le_of_pieces chi hT
    (by simpa only [f] using hIntegrable) hNegative hMiddle hPositive
  calc
    norm (dirichletPerronVerticalIntegral chi x
        (dirichletPerronLeftLine c q T) T) <=
        2 * C * x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 +
          4 * C * x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 +
          2 * C * x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 := hPieces
    _ = 8 * C * x ^ dirichletPerronLeftLine c q T *
        Real.log ((q : Real) * (T + 4)) ^ 2 := by ring

/-- The complete upward left edge for the principal character includes the
explicit distance-to-pole contribution. -/
theorem DirichletPerronLogDerivBounds.norm_principalDirichletPerronLeftIntegral_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q)
    {x T : Real} (hx : 0 < x) (hT : 7 / 8 <= T) :
    norm (dirichletPerronVerticalIntegral
      (1 : DirichletCharacter Complex q) x
      (dirichletPerronLeftLine c q T) T) <=
      (8 * (C + 8 * Real.log 5) + 20 / c) *
        x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by
  let f : Real -> Complex := fun t => logDerivPerronIntegrand
    (1 : DirichletCharacter Complex q).LFunction x
      ((dirichletPerronLeftLine c q T : Complex) +
        Complex.I * (t : Complex))
  have hTPos : 0 < T := by linarith
  have hIntegrable : IntervalIntegrable f volume (-T) T := by
    simpa only [f] using h.intervalIntegrable_dirichletPerronIntegrand_left
      (1 : DirichletCharacter Complex q) hq hx hTPos
  have hNegative :
      norm (∫ t in -T..(-7 / 8 : Real), f t) <=
        2 * (C + 8 * Real.log 5) *
          x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 := by
    have hTail :=
      DirichletPerronLeftPieces.norm_principalDirichletPerronHighTail_le
        h hq hx hT (epsilon := -1) (Or.inr rfl)
    have hReflect := intervalIntegral.integral_comp_neg
      (f := f) (a := (7 / 8 : Real)) (b := T)
    rw [show (-7 / 8 : Real) = -(7 / 8 : Real) by ring, ← hReflect]
    simpa only [f, neg_mul, one_mul, Complex.ofReal_neg] using hTail
  have hPositive :
      norm (∫ t in (7 / 8 : Real)..T, f t) <=
        2 * (C + 8 * Real.log 5) *
          x ^ dirichletPerronLeftLine c q T *
            Real.log ((q : Real) * (T + 4)) ^ 2 := by
    simpa only [f, one_mul] using
      (DirichletPerronLeftPieces.norm_principalDirichletPerronHighTail_le
        h hq hx hT (epsilon := 1) (Or.inl rfl))
  have hMiddle :
      norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) <=
        4 * x ^ dirichletPerronLeftLine c q T *
          (C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c) := by
    simpa only [f] using
      DirichletPerronLeftPieces.norm_principalDirichletPerronMiddle_le
        h hq hx hT
  have hPieces := norm_dirichletPerronVerticalIntegral_le_of_pieces
    (1 : DirichletCharacter Complex q) hT
    (by simpa only [f] using hIntegrable) hNegative hMiddle hPositive
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqOne : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLogOne : 1 < Real.log ((q : Real) * (T + 4)) := by
    have hArgument : (4 : Real) <= (q : Real) * (T + 4) := by
      calc
        (4 : Real) = 1 * 4 := by ring
        _ <= (q : Real) * (T + 4) :=
          mul_le_mul hqOne (by linarith) (by norm_num) hqPos.le
    rw [Real.lt_log_iff_exp_lt (mul_pos hqPos (by linarith))]
    exact Real.exp_one_lt_three.trans (by linarith)
  have hPowerNonneg : 0 <= x ^ dirichletPerronLeftLine c q T :=
    Real.rpow_nonneg hx.le _
  have hCoefficientNonneg : 0 <= C + 8 * Real.log 5 := by
    exact add_nonneg h.bound_pos.le
      (mul_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
  have hInvCPos : 0 < 1 / c := one_div_pos.mpr h.riemannZetaZeroFree.1
  have hLogNonneg : 0 <= Real.log ((q : Real) * (T + 4)) :=
    zero_le_one.trans hLogOne.le
  have hLogLeSq :
      Real.log ((q : Real) * (T + 4)) <=
        Real.log ((q : Real) * (T + 4)) ^ 2 := by
    nlinarith [mul_nonneg hLogNonneg (sub_nonneg.mpr hLogOne.le)]
  have hOneLeSq :
      1 <= Real.log ((q : Real) * (T + 4)) ^ 2 := by nlinarith
  have hPoleTerm :
      5 * Real.log ((q : Real) * (T + 4)) / c <=
        5 * (1 / c) * Real.log ((q : Real) * (T + 4)) ^ 2 := by
    have hScale := mul_le_mul_of_nonneg_left hLogLeSq hInvCPos.le
    calc
      5 * Real.log ((q : Real) * (T + 4)) / c =
          5 * ((1 / c) * Real.log ((q : Real) * (T + 4))) := by ring
      _ <= 5 * ((1 / c) * Real.log ((q : Real) * (T + 4)) ^ 2) :=
        mul_le_mul_of_nonneg_left hScale (by norm_num)
      _ = 5 * (1 / c) * Real.log ((q : Real) * (T + 4)) ^ 2 := by ring
  have hCoefficientTerm :
      C + 8 * Real.log 5 <=
        (C + 8 * Real.log 5) *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by
    calc
      C + 8 * Real.log 5 = (C + 8 * Real.log 5) * 1 := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hOneLeSq hCoefficientNonneg
  have hMiddleCoefficient :
      C + 8 * Real.log 5 +
          5 * Real.log ((q : Real) * (T + 4)) / c <=
        ((C + 8 * Real.log 5) + 5 * (1 / c)) *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by
    calc
      C + 8 * Real.log 5 +
          5 * Real.log ((q : Real) * (T + 4)) / c <=
        (C + 8 * Real.log 5) *
            Real.log ((q : Real) * (T + 4)) ^ 2 +
          5 * (1 / c) * Real.log ((q : Real) * (T + 4)) ^ 2 :=
        add_le_add hCoefficientTerm hPoleTerm
      _ = ((C + 8 * Real.log 5) + 5 * (1 / c)) *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by ring
  have hMiddleTerm :
      4 * x ^ dirichletPerronLeftLine c q T *
          (C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c) <=
        4 * x ^ dirichletPerronLeftLine c q T *
          (((C + 8 * Real.log 5) + 5 * (1 / c)) *
            Real.log ((q : Real) * (T + 4)) ^ 2) :=
    mul_le_mul_of_nonneg_left hMiddleCoefficient
      (mul_nonneg (by norm_num) hPowerNonneg)
  calc
    norm (dirichletPerronVerticalIntegral
        (1 : DirichletCharacter Complex q) x
        (dirichletPerronLeftLine c q T) T) <=
        2 * (C + 8 * Real.log 5) *
            x ^ dirichletPerronLeftLine c q T *
              Real.log ((q : Real) * (T + 4)) ^ 2 +
          4 * x ^ dirichletPerronLeftLine c q T *
            (C + 8 * Real.log 5 +
              5 * Real.log ((q : Real) * (T + 4)) / c) +
          2 * (C + 8 * Real.log 5) *
            x ^ dirichletPerronLeftLine c q T *
              Real.log ((q : Real) * (T + 4)) ^ 2 := hPieces
    _ <= 2 * (C + 8 * Real.log 5) *
            x ^ dirichletPerronLeftLine c q T *
              Real.log ((q : Real) * (T + 4)) ^ 2 +
          4 * x ^ dirichletPerronLeftLine c q T *
            (((C + 8 * Real.log 5) + 5 * (1 / c)) *
              Real.log ((q : Real) * (T + 4)) ^ 2) +
          2 * (C + 8 * Real.log 5) *
            x ^ dirichletPerronLeftLine c q T *
              Real.log ((q : Real) * (T + 4)) ^ 2 := by
      gcongr
    _ = (8 * (C + 8 * Real.log 5) + 20 / c) *
        x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by ring

end PrimesRestrictedDigits
