import BoundedGaps.Maynard.ConcreteS2GoodComplementNormalization
import BoundedGaps.Maynard.ConcreteS2ShiftKernel

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

/-!
# Good-complement S2 main term and Maynard scale

The finite main sum uses the raw complementary full-face moment produced by
the direct Wirsing path. Division by the concrete Maynard scale is an exact
algebraic identity; no prime-count or moment limit is asserted. See
Maynard2013v3, Section 5, equations (5.18), (5.26)--(5.27), and Section 6,
equations (6.13)--(6.16), (6.21).
-/

noncomputable def engelsmaMaynardS2GoodComplementMain
    (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
    engelsmaShiftedPrimeIntervalCount N m *
      ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
          engelsmaS2CoordinateFiberGoodComplementOuterMoment
            (engelsmaMaynardRadius alpha N)
            (tripleLogCutoff (N - 1)) m))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem engelsmaMaynardS2GoodComplementMain_div_scale_eq
    {alpha : ℝ} {N : ℕ}
    (hN : 0 < N)
    (hR : 1 < engelsmaMaynardRadius alpha N)
    (hRreal : 1 < engelsmaMaynardRealRadius alpha N) :
    engelsmaMaynardS2GoodComplementMain alpha N /
        engelsmaMaynardScale alpha N =
      ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
        (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
          normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
            alpha N m *
          Real.log (engelsmaMaynardRadius alpha N) *
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
  have hS : 0 < S := by
    dsimp [S, D]
    exact preSieveSingularSeries_pos _
  have hL : 0 < L := by
    dsimp [L, R]
    exact Real.log_pos (by exact_mod_cast hR)
  have hLreal : 0 < Lreal := by
    dsimp [Lreal, Rreal]
    exact Real.log_pos hRreal
  have hLn : Real.log (engelsmaMaynardRadius alpha N) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast hR)).ne'
  have hLrn : Real.log (engelsmaMaynardRealRadius alpha N) ≠ 0 :=
    (Real.log_pos hRreal).ne'
  unfold engelsmaMaynardS2GoodComplementMain
    engelsmaMaynardScale maynardSieveScale
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hcard : (BoundedGaps.engelsmaTuple.attach.erase m).card = 104 := by
    rw [Finset.card_erase_of_mem hm]
    simpa using BoundedGaps.engelsmaTuple_card
  rw [show
      engelsmaShiftedPrimeIntervalCount N m *
          ((Nat.totient W : ℝ)⁻¹ *
            (S ^ 2 *
              engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m)) /
          (((Nat.totient W : ℝ) ^ 105 * (N : ℝ) *
              Real.log Rreal ^ 105) / (W : ℝ) ^ 106) =
      (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
          normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
            alpha N m *
          Real.log R * (Real.log R / Real.log Rreal) ^ 105 by
        unfold normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
        dsimp [S]
        rw [show W = primorial D by rfl]
        rw [preSieveSingularSeries_eq_totient_div]
        have hW' : (W : ℝ) ≠ 0 := ne_of_gt hW
        have hphi' : (Nat.totient W : ℝ) ≠ 0 := ne_of_gt hphi
        have hS' : S ≠ 0 := ne_of_gt hS
        have hL' : L ≠ 0 := ne_of_gt hL
        have hLreal' : Lreal ≠ 0 := ne_of_gt hLreal
        rw [hcard]
        field_simp [hW', hphi', hS', hL', hLreal']
        dsimp [R, D, Rreal, L, Lreal, S, W]]

end BoundedGaps.Maynard
