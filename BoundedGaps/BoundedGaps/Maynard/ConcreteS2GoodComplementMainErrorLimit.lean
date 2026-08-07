import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics
import BoundedGaps.Maynard.ConcreteS2CoordinateOneComplementKernelLimit
import BoundedGaps.Maynard.ConcreteS2GoodComplementScaleBridge
import BoundedGaps.Maynard.ConcreteS2YFaceSupport

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

/-!
# Complementary S2 main error

SEM-398 factors the exact difference between the restricted S2 main and the
complementary main through SEM-396's exponent-106 coordinate error. Its limit
remains conditional on the displayed shifted-prime PNT input.
-/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem engelsmaMaynardS2Main_sub_goodComplementMain_div_scale_eq
    {alpha : ℝ} {N : ℕ}
    (hN : 0 < N)
    (hR : 1 < engelsmaMaynardRadius alpha N)
    (hRreal : 1 < engelsmaMaynardRealRadius alpha N) :
    (engelsmaMaynardS2Main alpha N -
        engelsmaMaynardS2GoodComplementMain alpha N) /
        engelsmaMaynardScale alpha N =
      ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
        ((engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
          Real.log (engelsmaMaynardRadius alpha N)) *
        (((engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
              engelsmaMaynardS2RestrictedCrossCorrection alpha N m) -
            preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
              engelsmaS2CoordinateFiberGoodComplementOuterMoment
                (engelsmaMaynardRadius alpha N)
                (tripleLogCutoff (N - 1)) m) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N)) ^ 106) *
        (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
  let W := engelsmaMaynardModulus N
  let D := tripleLogCutoff (N - 1)
  let R := engelsmaMaynardRadius alpha N
  let Rreal := engelsmaMaynardRealRadius alpha N
  let L := Real.log R
  let Lreal := Real.log Rreal
  let S := preSieveSingularSeries D
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hWnat : 0 < W := by
    dsimp [W]
    exact primorial_pos _
  have hW : (0 : ℝ) < W := by exact_mod_cast hWnat
  have hphi : (0 : ℝ) < Nat.totient W := by
    exact_mod_cast Nat.totient_pos.mpr hWnat
  have hL : 0 < L := by
    dsimp [L, R]
    exact Real.log_pos (by exact_mod_cast hR)
  have hLreal : 0 < Lreal := by
    dsimp [Lreal, Rreal]
    exact Real.log_pos hRreal
  rw [engelsmaMaynardS2Main_eq_invTotient_mul_coordinateOne_sub_cross_sum]
  unfold engelsmaMaynardS2GoodComplementMain
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  unfold engelsmaMaynardScale maynardSieveScale
  apply Finset.sum_congr rfl
  intro m hm
  rw [show
      (engelsmaShiftedPrimeIntervalCount N m *
            ((Nat.totient W : ℝ)⁻¹ *
              (engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
                engelsmaMaynardS2RestrictedCrossCorrection alpha N m)) -
        engelsmaShiftedPrimeIntervalCount N m *
            ((Nat.totient W : ℝ)⁻¹ *
              (S ^ 2 *
                engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m))) /
          (((Nat.totient W : ℝ) ^ 105 * (N : ℝ) *
              Lreal ^ 105) / (W : ℝ) ^ 106) =
      ((engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) * L) *
        (((engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
              engelsmaMaynardS2RestrictedCrossCorrection alpha N m) -
            S ^ 2 *
              engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m) /
          (S * L) ^ 106) *
        (L / Lreal) ^ 105 by
      rw [show S = (Nat.totient W : ℝ) / (W : ℝ) by
        rw [show W = primorial D by rfl]
        simpa [S] using preSieveSingularSeries_eq_totient_div D]
      field_simp [hNreal.ne', hW.ne', hphi.ne', hL.ne', hLreal.ne']]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem tendsto_engelsmaMaynardS2Main_sub_goodComplementMain_div_scale_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (hprime : ∀ m : BoundedGaps.engelsmaTuple,
      Tendsto
        (fun N : ℕ =>
          (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
            Real.log (engelsmaMaynardRadius alpha N))
        atTop (nhds alpha)) :
    Tendsto
      (fun N : ℕ =>
        (engelsmaMaynardS2Main alpha N -
          engelsmaMaynardS2GoodComplementMain alpha N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  have hratio :=
    (tendsto_log_engelsmaMaynardRadius_div_realRadius halpha).pow 105
  have hterm : ∀ m : BoundedGaps.engelsmaTuple,
      Tendsto
        (fun N : ℕ =>
          ((engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
            Real.log (engelsmaMaynardRadius alpha N)) *
          (((engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
                engelsmaMaynardS2RestrictedCrossCorrection alpha N m) -
              preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
                engelsmaS2CoordinateFiberGoodComplementOuterMoment
                  (engelsmaMaynardRadius alpha N)
                  (tripleLogCutoff (N - 1)) m) /
            (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
              Real.log (engelsmaMaynardRadius alpha N)) ^ 106) *
          (Real.log (engelsmaMaynardRadius alpha N) /
            Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop (nhds 0) := by
    intro m
    have hkernel :=
      tendsto_normalizedEngelsmaS2CoordinateOneKernel_sub_complementOuterMoment_zero
        halpha m
    have hmul := ((hprime m).mul hkernel).mul hratio
    simpa [mul_assoc] using hmul
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
            ((engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
              Real.log (engelsmaMaynardRadius alpha N)) *
            (((engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
                  engelsmaMaynardS2RestrictedCrossCorrection alpha N m) -
                preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
                  engelsmaS2CoordinateFiberGoodComplementOuterMoment
                    (engelsmaMaynardRadius alpha N)
                    (tripleLogCutoff (N - 1)) m) /
              (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
                Real.log (engelsmaMaynardRadius alpha N)) ^ 106) *
            (Real.log (engelsmaMaynardRadius alpha N) /
              Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop (nhds 0) := by
    have hs : Tendsto
        (fun N : ℕ =>
          ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
            ((engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
              Real.log (engelsmaMaynardRadius alpha N)) *
            (((engelsmaMaynardS2CoordinateOneYDiagonal alpha N m -
                  engelsmaMaynardS2RestrictedCrossCorrection alpha N m) -
                preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
                  engelsmaS2CoordinateFiberGoodComplementOuterMoment
                    (engelsmaMaynardRadius alpha N)
                    (tripleLogCutoff (N - 1)) m) /
              (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
                Real.log (engelsmaMaynardRadius alpha N)) ^ 106) *
            (Real.log (engelsmaMaynardRadius alpha N) /
              Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop
        (nhds (∑ _m ∈ BoundedGaps.engelsmaTuple.attach, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro m hm
      exact hterm m
    simpa using hs
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1,
      eventually_one_lt_engelsmaMaynardRadius halpha,
      eventually_ge_atTop 3] with N hN hR hN3
  have hNpos : 0 < N := by omega
  have hRreal : 1 < engelsmaMaynardRealRadius alpha N := by
    unfold engelsmaMaynardRealRadius maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  exact
    (engelsmaMaynardS2Main_sub_goodComplementMain_div_scale_eq
      hNpos hR hRreal).symm

end BoundedGaps.Maynard
