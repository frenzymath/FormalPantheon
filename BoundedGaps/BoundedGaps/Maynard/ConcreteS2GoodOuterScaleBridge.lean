import BoundedGaps.Maynard.ConcreteS2CoordinateOneMainComposition
import BoundedGaps.Maynard.ConcreteS2GoodComplementExpansion

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

/-!
# Good-outer S2 main term and Maynard scale

The exact good-outer main sum is rewritten by the concrete Maynard scale. The
natural and real radius logarithms remain distinct, so the finite identity
retains their ratio to the 105th power.
-/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem engelsmaMaynardS2GoodOuterMain_div_scale_eq
    {alpha : ℝ} {N : ℕ}
    (hN : 0 < N)
    (hR : 1 < engelsmaMaynardRadius alpha N)
    (hRreal : 1 < engelsmaMaynardRealRadius alpha N) :
    engelsmaMaynardS2GoodOuterMain alpha N /
        engelsmaMaynardScale alpha N =
      ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
        (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
          normalizedEngelsmaS2CoordinateFiberGoodOuterMoment alpha N m *
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
  unfold engelsmaMaynardS2GoodOuterMain
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
            (S ^ 2 * engelsmaS2CoordinateFiberGoodOuterMoment R D m)) /
          (((Nat.totient W : ℝ) ^ 105 * (N : ℝ) *
              Real.log Rreal ^ 105) / (W : ℝ) ^ 106) =
      (engelsmaShiftedPrimeIntervalCount N m / (N : ℝ)) *
          normalizedEngelsmaS2CoordinateFiberGoodOuterMoment alpha N m *
          Real.log R * (Real.log R / Real.log Rreal) ^ 105 by
        unfold normalizedEngelsmaS2CoordinateFiberGoodOuterMoment
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
