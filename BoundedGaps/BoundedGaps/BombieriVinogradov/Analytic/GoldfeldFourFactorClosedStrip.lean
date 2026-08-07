import BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionClosedStripGrowth
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldSmoothedSum
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaClosedStripGrowth

/-!
# Goldfeld's four-factor function on the contour strip

This file combines the ordinary-zeta and arbitrary-character growth bounds at
the original character levels.  In particular, the cross character remains
at level `lcm(q1,q)` and may be imprimitive.

Source: Koukoulopoulos, printed p. 126, proof of Theorem 12.9.
Semantic review: `SEM-556`.
-/

namespace BoundedGaps.Maynard

open Complex

private instance goldfeldClosedStripLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

/-- One absolute natural exponent controls Goldfeld's complete four-factor
function uniformly across the high-ordinate closed contour strip. -/
theorem exists_norm_goldfeldFourFactorLFunction_closedStrip_le_pow :
    ∃ A : ℕ, 57 ≤ A ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta : ℝ) (s : ℂ),
            0 ≤ beta → beta ≤ 1 →
            -(1 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
            ‖goldfeldFourFactorLFunction chi1 chi
                (s + (beta : ℂ))‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨L, hLexp, hL⟩ := exists_norm_LFunction_closedStrip_le_pow
  obtain ⟨E, hEexp, hZeta⟩ := exists_norm_riemannZeta_closedStrip_le_pow
  refine ⟨E + 4 * L, by omega, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross beta s
    hbeta0 hbeta1 hslo hshi hheight
  have hq : 1 < q := hq1.trans_le hq1q
  let w : ℂ := s + (beta : ℂ)
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hwre : w.re = s.re + beta := by simp [w]
  have hwim : w.im = s.im := by simp [w]
  have hwlo : -(1 : ℝ) ≤ w.re := by rw [hwre]; linarith
  have hwhi : w.re ≤ 3 := by rw [hwre]; linarith
  have hwheight : 1 ≤ |w.im| := by simpa [hwim] using hheight
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1r : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1r
  have hT3 : (3 : ℝ) ≤ T := by
    dsimp [T]
    linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hZetaBound : ‖riemannZeta w‖ ≤ B ^ E := by
    have hz := hZeta w hwlo hwhi hwheight
    have hTB : T ≤ B := by
      dsimp [B]
      nlinarith
    exact hz.trans (by
      simpa [T, hwim] using pow_le_pow_left₀ hT0 hTB E)
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
      (m : ℝ) * (|s.im| + 2) ≤
          (q : ℝ) ^ 2 * (|s.im| + 2) :=
        mul_le_mul_of_nonneg_right hmqqReal (by positivity)
      _ ≤ (q : ℝ) ^ 2 * (|s.im| + 2) ^ 2 := by
        gcongr
        nlinarith
      _ = ((q : ℝ) * (|s.im| + 2)) ^ 2 := by ring
  have hcrossBound :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
        B ^ (2 * L) := by
    have h := hL m hm1 (DirichletCharacter.mul chi1 chi) hcross w hwlo hwhi
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

end BoundedGaps.Maynard
