import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldFourFactorClosedStrip

/-!
# Goldfeld bounds on the left contour line

The shifted four-factor function is controlled at every height on
`Re(s) = -1`.  At low height ordinary zeta is recovered from its entire
regularization using the fixed distance from the pole.  Combining this with
the fixed-line Mellin decay retains the exact source factor `x⁻¹`.

Source: Koukoulopoulos, printed p. 126, proof of Theorem 12.9.
Semantic review: `SEM-558`.
-/

namespace BoundedGaps.Maynard

open Complex

noncomputable section

private instance goldfeldLeftLineBoundsLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

/-- One absolute exponent controls the complete Goldfeld four-factor
function at every height on the shifted left contour line. -/
theorem exists_norm_goldfeldFourFactorLFunction_leftLine_le_pow :
    ∃ A : ℕ, 57 ≤ A ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta t : ℝ),
            0 ≤ beta → beta ≤ 1 →
            ‖goldfeldFourFactorLFunction chi1 chi
                (((-1 : ℂ) + t * I) + (beta : ℂ))‖ ≤
              ((q : ℝ) * (|t| + 2)) ^ A := by
  obtain ⟨L, hLexp, hL⟩ := exists_norm_LFunction_closedStrip_le_pow
  obtain ⟨E, hEexp, hZetaOne⟩ :=
    exists_norm_riemannZeta₁_closedStrip_le_pow
  refine ⟨E + 4 * L, by omega, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta t hbeta0 hbeta1
  let w : ℂ := ((-1 : ℂ) + t * I) + (beta : ℂ)
  let T : ℝ := |t| + 2
  let B : ℝ := (q : ℝ) * T
  have hwre : w.re = -1 + beta := by simp [w]
  have hwim : w.im = t := by simp [w]
  have hwlo : -(1 : ℝ) ≤ w.re := by rw [hwre]; linarith
  have hwhi : w.re ≤ 3 := by rw [hwre]; linarith
  have hq : 1 < q := hq1.trans_le hq1q
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1r : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1r
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ T := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hwOne : w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hwre] at hre
    norm_num at hre
    linarith
  have hwSubNorm : (1 : ℝ) ≤ ‖w - 1‖ := by
    have hre : (w - 1).re ≤ -1 := by
      simp only [sub_re, one_re]
      rw [hwre]
      linarith
    have habs : (1 : ℝ) ≤ |(w - 1).re| := by
      rw [abs_of_nonpos (hre.trans (by norm_num))]
      linarith
    exact habs.trans (Complex.abs_re_le_norm (w - 1))
  have hZetaInv : ‖(w - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hwOne))).2 hwSubNorm
  have hZetaBound : ‖riemannZeta w‖ ≤ B ^ E := by
    have hregular := hZetaOne w hwlo hwhi
    have hTB : T ≤ B := by
      dsimp [B]
      nlinarith
    rw [riemannZeta_eq_inv_sub_mul hwOne, norm_mul]
    calc
      ‖(w - 1)⁻¹‖ * ‖riemannZeta₁ w‖ ≤
          1 * ‖riemannZeta₁ w‖ :=
        mul_le_mul_of_nonneg_right hZetaInv (norm_nonneg _)
      _ ≤ T ^ E := by simpa [T, hwim] using hregular
      _ ≤ B ^ E := pow_le_pow_left₀ hT0 hTB E
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hchi1Bound :
      ‖DirichletCharacter.LFunction chi1 w‖ ≤ B ^ L := by
    have h := hL q1 hq1 chi1 hchi1 w hwlo hwhi
    have hbase : (q1 : ℝ) * (|w.im| + 2) ≤ B := by
      dsimp [B, T]
      rw [hwim]
      gcongr
    exact h.trans (pow_le_pow_left₀ (by positivity) hbase L)
  have hchiBound :
      ‖DirichletCharacter.LFunction chi w‖ ≤ B ^ L := by
    simpa [B, T, hwim] using hL q hq chi hchi w hwlo hwhi
  let m := Nat.lcm q1 q
  have hmpos : 0 < m := Nat.lcm_pos (NeZero.pos q1) (NeZero.pos q)
  letI : NeZero m := ⟨hmpos.ne'⟩
  have hqm : q ≤ m := Nat.le_of_dvd hmpos (Nat.dvd_lcm_right q1 q)
  have hm1 : 1 < m := hq.trans_le hqm
  have hmqq : m ≤ q1 * q :=
    Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
      (Nat.lcm_dvd_mul q1 q)
  have hmqqReal : (m : ℝ) ≤ (q : ℝ) ^ 2 := by
    calc
      (m : ℝ) ≤ ((q1 * q : ℕ) : ℝ) := by exact_mod_cast hmqq
      _ = (q1 : ℝ) * (q : ℝ) := by norm_num
      _ ≤ (q : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hq1qReal hq0
      _ = (q : ℝ) ^ 2 := by ring
  have hmBase : (m : ℝ) * (|w.im| + 2) ≤ B ^ 2 := by
    rw [hwim]
    dsimp [B, T]
    calc
      (m : ℝ) * (|t| + 2) ≤
          (q : ℝ) ^ 2 * (|t| + 2) :=
        mul_le_mul_of_nonneg_right hmqqReal (by positivity)
      _ ≤ (q : ℝ) ^ 2 * (|t| + 2) ^ 2 := by
        gcongr
        nlinarith
      _ = ((q : ℝ) * (|t| + 2)) ^ 2 := by ring
  have hcrossBound :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
        B ^ (2 * L) := by
    have h := hL m hm1 (DirichletCharacter.mul chi1 chi) hcross
      w hwlo hwhi
    calc
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
          ((m : ℝ) * (|w.im| + 2)) ^ L := h
      _ ≤ (B ^ 2) ^ L := pow_le_pow_left₀ (by positivity) hmBase L
      _ = B ^ (2 * L) := by rw [pow_mul]
  rw [goldfeldFourFactorLFunction, norm_mul, norm_mul, norm_mul]
  calc
    ‖riemannZeta w‖ * ‖DirichletCharacter.LFunction chi1 w‖ *
          ‖DirichletCharacter.LFunction chi w‖ *
        ‖DirichletCharacter.LFunction
            (DirichletCharacter.mul chi1 chi) w‖ ≤
      B ^ E * B ^ L * B ^ L * B ^ (2 * L) := by gcongr
    _ = B ^ (E + 4 * L) := by ring

private lemma goldfeld_leftLine_decay_product_le
    {q u x C : ℝ} {A : ℕ}
    (hq : 0 ≤ q) (hu : 0 ≤ u) (hx : 0 < x) (hC : 0 ≤ C) :
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ ≤
      (C * (2 : ℝ) ^ A) * q ^ A /
        (x * (1 + u) ^ 2) := by
  have hbase : u + 2 ≤ 2 * (1 + u) := by linarith
  have hpow : (u + 2) ^ A ≤ (2 * (1 + u)) ^ A :=
    pow_le_pow_left₀ (by linarith) hbase A
  have hqpow : 0 ≤ q ^ A := pow_nonneg hq A
  have hprod :
      q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ ≤
        q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := by
    gcongr
  calc
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ =
        q ^ A * (u + 2) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := by rw [mul_pow]
    _ ≤ q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := hprod
    _ = (C * (2 : ℝ) ^ A) * q ^ A /
          (x * (1 + u) ^ 2) := by
      rw [mul_pow]
      field_simp
      ring

/-- The raw contour integrand retains the exact `x⁻¹` scale and two
integrable powers of ordinate decay on the complete left line. -/
theorem exists_norm_goldfeldContourIntegrand_leftLine_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x t : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            ‖goldfeldContourIntegrand chi1 chi beta x
                ((-1 : ℂ) + t * I)‖ ≤
              C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := by
  obtain ⟨A, hA, hF⟩ :=
    exists_norm_goldfeldFourFactorLFunction_leftLine_le_pow
  obtain ⟨Cphi, hCphi, hPhi⟩ :=
    goldfeldMellinContinuationData.decay_on_neg_one (A + 2) (by omega)
  let C : ℝ := Cphi * (2 : ℝ) ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x t hbeta0 hbeta1 hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hF' := hF q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
    beta t hbeta0 hbeta1
  have hPhi' := hPhi t
  have hxpow : ‖(x : ℂ) ^ ((-1 : ℂ) + t * I)‖ = x⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp [Real.rpow_neg_one]
  rw [goldfeldContourIntegrand, norm_mul, norm_mul, hxpow]
  calc
    ‖goldfeldFourFactorLFunction chi1 chi
          (((-1 : ℂ) + t * I) + (beta : ℂ))‖ *
        ‖goldfeldMellinContinuationData.Phi ((-1 : ℂ) + t * I)‖ * x⁻¹ ≤
      ((q : ℝ) * (|t| + 2)) ^ A *
        (Cphi / (1 + |t|) ^ (A + 2)) * x⁻¹ := by gcongr
    _ ≤ (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A /
          (x * (1 + |t|) ^ 2) :=
      goldfeld_leftLine_decay_product_le hq0 (abs_nonneg t)
        hxpos hCphi.le
    _ = C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := by rfl

end

end BoundedGaps.Maynard
