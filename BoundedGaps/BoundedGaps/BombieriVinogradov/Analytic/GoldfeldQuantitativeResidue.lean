import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldContourLimit
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLValueUpper
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldMellinPositiveBound
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldSmoothedSumLowerBound

/-!
# Quantitative bounds for Goldfeld's contour residue

The exact contour identity first gives a lower bound for the residue after the
left line is made small.  The residue's four explicit factors then give the
matching upper bound used in Koukoulopoulos Theorem 12.9.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 126.
Semantic review: `SEM-560`.
-/

noncomputable section

open Complex
open scoped ComplexOrder

namespace BoundedGaps.Maynard

/-- If the complete left line costs at most one half, positivity of the
smoothed sum forces the exact shifted-zeta residue to have norm at least one
half. -/
theorem half_le_norm_goldfeldContourResidue_of_leftLine
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hleft : ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖goldfeldContourResidue chi1 chi beta x‖ := by
  have hsumOrder := one_le_goldfeldSmoothedSum
    chi1 chi hsquare1 hsquare (beta := beta) hx
  have hsumRe : 1 ≤ (goldfeldSmoothedSum chi1 chi beta x).re := by
    have hre := Complex.re_le_re hsumOrder
    simpa using hre
  have hsumNorm : 1 ≤ ‖goldfeldSmoothedSum chi1 chi beta x‖ :=
    hsumRe.trans (Complex.re_le_norm _)
  rw [goldfeldSmoothedSum_eq_residue_add_verticalIntegral_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hzero] at hsumNorm
  have htriangle :
      1 ≤ ‖goldfeldContourResidue chi1 chi beta x‖ +
        ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ :=
    hsumNorm.trans (norm_add_le _ _)
  linarith

/-- Explicit upper bound for the residue after applying equation (12.11), the
cross-character value estimate, and the positive-real Mellin estimate. -/
theorem norm_goldfeldContourResidue_le
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    ‖goldfeldContourResidue chi1 chi beta x‖ ≤
      65536 * x ^ (1 - beta) *
        (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
  let delta : ℝ := 1 - beta
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta ≤ 1 := by dsimp [delta]; linarith
  have hdeltaNonneg : 0 ≤ delta := hdelta0.le
  have hq1Pos : 0 < (q1 : ℝ) := by positivity
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hlogq1Nonneg : 0 ≤ Real.log (q1 : ℝ) :=
    (Real.log_pos (by exact_mod_cast hq1)).le
  have hlogq1q : Real.log (q1 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hq1Pos hq1qReal
  have hqpow :
      (q1 : ℝ) ^ (delta / 2) ≤ (q : ℝ) ^ (delta / 2) :=
    Real.rpow_le_rpow hq1Pos.le hq1qReal (by positivity)
  have hlogpow :
      (Real.log (q1 : ℝ)) ^ 2 ≤ (Real.log (q : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlogq1Nonneg hlogq1q 2
  have hLone := norm_LFunction_one_of_real_zero_le
    hq1 chi1 hchi1 hbeta1.le hzero
  have hLoneQ :
      ‖DirichletCharacter.LFunction chi1 (1 : ℂ)‖ ≤
        512 * delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 2 := by
    calc
      ‖DirichletCharacter.LFunction chi1 (1 : ℂ)‖ ≤
          512 * delta * (q1 : ℝ) ^ (delta / 2) *
            (Real.log (q1 : ℝ)) ^ 2 := by simpa [delta] using hLone
      _ ≤ 512 * delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 2 := by
        gcongr
  letI : NeZero (Nat.lcm q1 q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩
  have hlcmPos : 0 < Nat.lcm q1 q := NeZero.pos _
  have hq1lcm : q1 ≤ Nat.lcm q1 q :=
    Nat.le_of_dvd hlcmPos (Nat.dvd_lcm_left q1 q)
  have hlcmOne : 1 < Nat.lcm q1 q := hq1.trans_le hq1lcm
  have hlcmNat : Nat.lcm q1 q ≤ q ^ 2 := by
    calc
      Nat.lcm q1 q ≤ q1 * q :=
        Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
          (Nat.lcm_dvd_mul q1 q)
      _ ≤ q * q := Nat.mul_le_mul_right q hq1q
      _ = q ^ 2 := by ring
  have hlcmReal : (Nat.lcm q1 q : ℝ) ≤ (q : ℝ) ^ 2 := by
    exact_mod_cast hlcmNat
  have hlcmLog :
      Real.log (Nat.lcm q1 q : ℝ) ≤ 2 * Real.log (q : ℝ) := by
    calc
      Real.log (Nat.lcm q1 q : ℝ) ≤ Real.log ((q : ℝ) ^ 2) :=
        Real.log_le_log (by exact_mod_cast hlcmPos) hlcmReal
      _ = 2 * Real.log (q : ℝ) := by rw [Real.log_pow]; norm_num
  have hcrossValue := norm_LFunction_near_one_le hlcmOne
    (DirichletCharacter.mul chi1 chi) hcross (s := (1 : ℂ))
    (by
      exact sub_le_self 1 (div_nonneg (by norm_num) (by positivity)))
    (by norm_num)
  have hcrossQ :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
          (1 : ℂ)‖ ≤ 64 * Real.log (q : ℝ) := by
    nlinarith
  have hPhi :=
    norm_goldfeldMellinContinuationData_Phi_ofReal_le_two_div
      hdelta0 hdelta1
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hxpow :
      ‖(x : ℂ) ^ goldfeldShiftedZetaPole beta‖ = x ^ delta := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
    simp [goldfeldShiftedZetaPole, delta]
  rw [goldfeldContourResidue]
  simp only [norm_mul]
  rw [hxpow]
  calc
    x ^ delta * ‖DirichletCharacter.LFunction chi1 1‖ *
          ‖DirichletCharacter.LFunction chi 1‖ *
          ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) 1‖ *
          ‖goldfeldMellinContinuationData.Phi
            (goldfeldShiftedZetaPole beta)‖ ≤
        x ^ delta *
          (512 * delta * (q : ℝ) ^ (delta / 2) *
            (Real.log (q : ℝ)) ^ 2) *
          ‖DirichletCharacter.LFunction chi 1‖ *
          (64 * Real.log (q : ℝ)) * (2 / delta) := by
      have hPhi' :
          ‖goldfeldMellinContinuationData.Phi
              (goldfeldShiftedZetaPole beta)‖ ≤ 2 / delta := by
        simpa [goldfeldShiftedZetaPole, delta] using hPhi
      gcongr
    _ = 65536 * x ^ (1 - beta) *
        (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
      have hbetaNe : 1 - beta ≠ 0 := by linarith
      dsimp [delta]
      field_simp [hbetaNe]
      ring

end BoundedGaps.Maynard
