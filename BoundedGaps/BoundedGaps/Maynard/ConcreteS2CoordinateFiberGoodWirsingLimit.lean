import BoundedGaps.Maynard.ConcreteS2OuterFaceBoxLimit
import BoundedGaps.Maynard.MaynardS2CoordinateFiberGoodWirsingSum

set_option maxRecDepth 8000

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

/-!
# Normalized good-fiber Wirsing error

SEM-394 specializes the SEM-393 finite error majorant to the concrete
Maynard parameters. The explicit scalar error is negligible relative to two
logarithmic fiber powers, and the remaining normalized face-box mass tends to
one.
-/

theorem tendsto_engelsmaS2WirsingSquareFactor_div_log_sq_zero
    {alpha : ℝ} (halpha : 0 < alpha) (K C : ℝ) :
    Tendsto (fun N : ℕ =>
      (smallKCandidateBound ^ 2 *
        (132 * (K + Real.log (tripleLogCutoff (N - 1)) +
          (Real.log (Real.log (engelsmaMaynardRadius alpha N)) + C + 2) +
          Real.log 2) + Real.log 3) *
        (2 * Real.log (engelsmaMaynardRadius alpha N) +
          (132 * (K + Real.log (tripleLogCutoff (N - 1)) +
            (Real.log (Real.log (engelsmaMaynardRadius alpha N)) + C + 2) +
            Real.log 2) + Real.log 3))) /
        Real.log (engelsmaMaynardRadius alpha N) ^ 2)
      atTop (nhds 0) := by
  let L := fun N : ℕ => Real.log (engelsmaMaynardRadius alpha N)
  let D := fun N : ℕ => tripleLogCutoff (N - 1)
  let B := fun N : ℕ =>
    K + Real.log (D N) + (Real.log (L N) + C + 2) + Real.log 2
  let H := fun N : ℕ => 132 * B N + Real.log 3
  have hL : Tendsto L atTop atTop := by
    simpa [L] using tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hK : Tendsto (fun N : ℕ => K / L N) atTop (nhds 0) :=
    hL.const_div_atTop K
  have hD : Tendsto (fun N : ℕ => Real.log (D N) / L N)
      atTop (nhds 0) := by
    simpa [D, L] using tendsto_log_tripleLogCutoff_div_logRadius_zero halpha
  have hlogL : Tendsto (fun N : ℕ => Real.log (L N) / L N)
      atTop (nhds 0) := by
    simpa using
      (Real.isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero
  have hC : Tendsto (fun N : ℕ => C / L N) atTop (nhds 0) :=
    hL.const_div_atTop C
  have htwo : Tendsto (fun N : ℕ => (2 : ℝ) / L N)
      atTop (nhds 0) := hL.const_div_atTop 2
  have hlog2 : Tendsto (fun N : ℕ => Real.log 2 / L N)
      atTop (nhds 0) := hL.const_div_atTop (Real.log 2)
  have hlog3 : Tendsto (fun N : ℕ => Real.log 3 / L N)
      atTop (nhds 0) := hL.const_div_atTop (Real.log 3)
  have hBratio : Tendsto (fun N : ℕ => B N / L N)
      atTop (nhds 0) := by
    have hsum := (((hK.add hD).add ((hlogL.add hC).add htwo)).add hlog2)
    convert hsum using 1
    · funext N
      dsimp [B]
      ring
    · norm_num
  have hHratio : Tendsto (fun N : ℕ => H N / L N)
      atTop (nhds 0) := by
    have hsum := hBratio.const_mul (132 : ℝ) |>.add hlog3
    convert hsum using 1
    · funext N
      dsimp [H]
      ring
    · norm_num
  have hsecond : Tendsto (fun N : ℕ => 2 + H N / L N)
      atTop (nhds 2) := by
    simpa using tendsto_const_nhds.add hHratio
  have hscaled : Tendsto (fun N : ℕ =>
      smallKCandidateBound ^ 2 *
        ((H N / L N) * (2 + H N / L N))) atTop (nhds 0) := by
    simpa using (hHratio.mul hsecond).const_mul (smallKCandidateBound ^ 2)
  apply hscaled.congr'
  filter_upwards [hL.eventually (eventually_ne_atTop 0)] with N hLN
  have hLN' : Real.log (engelsmaMaynardRadius alpha N) ≠ 0 := by
    simpa [L] using hLN
  dsimp [H, B, D, L]
  field_simp [hLN']

theorem tendsto_normalizedEngelsmaS2CoordinateFiberGoodSquareDiagonal_sub_complementOuterMoment_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      (engelsmaS2CoordinateFiberGoodSquareDiagonal
          (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) ^ 2 *
          engelsmaS2CoordinateFiberGoodComplementOuterMoment
            (engelsmaMaynardRadius alpha N)
            (tripleLogCutoff (N - 1)) m) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) ^ 106)
      atTop (nhds 0) := by
  obtain ⟨K, C, hK, hC, hsum⟩ :=
    exists_uniform_abs_engelsmaS2CoordinateFiberGoodSquareDiagonal_sub_complementOuterMoment_le_wirsing
  have hscalar :=
    tendsto_engelsmaS2WirsingSquareFactor_div_log_sq_zero halpha K C
  have hbox :=
    tendsto_normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve
      halpha m
  let E := fun N : ℕ =>
    (smallKCandidateBound ^ 2 *
        (132 * (K + Real.log (tripleLogCutoff (N - 1)) +
          (Real.log (Real.log (engelsmaMaynardRadius alpha N)) + C + 2) +
          Real.log 2) + Real.log 3) *
        (2 * Real.log (engelsmaMaynardRadius alpha N) +
          (132 * (K + Real.log (tripleLogCutoff (N - 1)) +
            (Real.log (Real.log (engelsmaMaynardRadius alpha N)) + C + 2) +
            Real.log 2) + Real.log 3))) /
          Real.log (engelsmaMaynardRadius alpha N) ^ 2
  have hscalar' : Tendsto E atTop (nhds 0) := by
    simpa [E] using hscalar
  have hupper : Tendsto (fun N : ℕ => E N *
        normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve
          alpha N m)
      atTop (nhds 0) := by
    simpa using hscalar'.mul hbox
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hupper
  have hLtop := tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hlarge : ∀ᶠ N : ℕ in atTop,
      2 ≤ Real.log (engelsmaMaynardRadius alpha N) :=
    hLtop.eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge] with N hLN
  let R := engelsmaMaynardRadius alpha N
  let D := tripleLogCutoff (N - 1)
  let S := preSieveSingularSeries D
  let L := Real.log R
  let k := ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card
  let P := ∏ _h ∈ (Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m,
    maynardS2OuterSquarefreeMean (primorial D) R
  let H := 132 * (K + Real.log D + (Real.log L + C + 2) + Real.log 2) +
    Real.log 3
  let T := smallKCandidateBound ^ 2 * H * (2 * L + H)
  have hL : 0 < L := by dsimp [L]; linarith
  have hS : 0 < S := by dsimp [S]; exact preSieveSingularSeries_pos D
  have hk : k = 104 := by
    dsimp [k]
    rw [Finset.card_erase_of_mem (by simp)]
    simpa using BoundedGaps.engelsmaTuple_card
  have hden : 0 < (S * L) ^ 106 := pow_pos (mul_pos hS hL) _
  have hdiff := hsum (R := R) (D := D) m (by simpa [L, R] using hLN)
  have hdiff' :
      |engelsmaS2CoordinateFiberGoodSquareDiagonal R D m -
          S ^ 2 * engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m| ≤
        S ^ 2 * T * P := by
    simpa [R, D, S, L, H, T, P, mul_assoc] using hdiff
  have hdiv :
      |(engelsmaS2CoordinateFiberGoodSquareDiagonal R D m -
          S ^ 2 * engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m) /
            (S * L) ^ 106| ≤
        (T / L ^ 2) * (P / (S * L) ^ k) := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    calc
      |engelsmaS2CoordinateFiberGoodSquareDiagonal R D m -
          S ^ 2 * engelsmaS2CoordinateFiberGoodComplementOuterMoment R D m| ≤
          S ^ 2 * T * P := hdiff'
      _ = ((T / L ^ 2) * (P / (S * L) ^ k)) * (S * L) ^ 106 := by
        rw [hk]
        field_simp [hL.ne', hS.ne']
  have hboxEq :
      normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve alpha N m =
        P / (S * L) ^ k := by
    unfold normalizedEngelsmaS2OuterCoordinateOneFaceBoxMassPreSieve
      engelsmaS2OuterCoordinateOneFaceBoxMass
    unfold engelsmaMaynardModulus
    rw [maynardS2OuterCoordinateOneFaceBox_sum_eq_erase_prod_mean]
  rw [hboxEq]
  simpa [E, R, D, S, L, H, T, P, k] using hdiv

end BoundedGaps.Maynard
