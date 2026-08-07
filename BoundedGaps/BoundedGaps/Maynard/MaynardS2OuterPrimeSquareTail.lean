import BoundedGaps.Maynard.MaynardS2OuterGamma
import BoundedGaps.Maynard.MaynardReciprocalSquareTail

noncomputable section

/-!
# Prime square tail for the S2 outer weight

Maynard2013v3, source lines 540--546, bounds the incompatible-coordinate
error by a rough prime tail of `phi(p)^4/(g(p)^2*p^4)`.  This is dominated
by the audited reciprocal-totient square tail.
-/

namespace BoundedGaps.Maynard

theorem maynardS2OuterScalarWeight_prime_sq_le_primeTotientSquareWeight
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (maynardS2OuterScalarWeight p) ^ 2 ≤ primeTotientSquareWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp2 : 2 ≤ p := by omega
  have hpG : (maynardS2G p : ℝ) = p - 2 := by
    rw [maynardS2G_prime hp]
    norm_num [Nat.cast_sub hp2]
  have hpPhi : (Nat.totient p : ℝ) = p - 1 := by
    rw [Nat.totient_prime hp]
    norm_num [Nat.cast_sub hp.one_le]
  have hpm1 : 0 < (p : ℝ) - 1 := by nlinarith [hp3R]
  have hpm2 : 0 < (p : ℝ) - 2 := by nlinarith [hp3R]
  have hbase : ((p : ℝ) - 1) ^ 3 ≤ ((p : ℝ) - 2) * p ^ 2 := by
    have hprod : 0 ≤ (p : ℝ) * ((p : ℝ) - 3) :=
      mul_nonneg hpR.le (sub_nonneg.mpr hp3R)
    nlinarith [hprod]
  have hpow : ((p : ℝ) - 1) ^ 6 ≤
      (((p : ℝ) - 2) * p ^ 2) ^ 2 := by
    have hsquare := (sq_le_sq₀ (by positivity)
      (mul_nonneg hpm2.le (sq_nonneg (p : ℝ)))).2 hbase
    nlinarith [hsquare]
  unfold maynardS2OuterScalarWeight primeTotientSquareWeight
  rw [hpG, hpPhi]
  have hden : 0 < ((p : ℝ) - 2) * p ^ 2 :=
    mul_pos hpm2 (sq_pos_of_pos hpR)
  rw [div_pow]
  rw [div_le_iff₀ (sq_pos_of_pos hden)]
  rw [show (1 / ((p : ℝ) - 1) ^ 2) *
      (((p : ℝ) - 2) * p ^ 2) ^ 2 =
      (((p : ℝ) - 2) * p ^ 2) ^ 2 / ((p : ℝ) - 1) ^ 2 by ring]
  rw [le_div_iff₀ (sq_pos_of_pos hpm1)]
  nlinarith [hpow]

theorem sum_maynardS2OuterScalarWeight_sq_prime_tail_le
    {D Q : ℕ} (hD : 2 ≤ D) :
    (∑ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
      (maynardS2OuterScalarWeight p) ^ 2) ≤
      8 / (D : ℝ) := by
  calc
    (∑ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
        (maynardS2OuterScalarWeight p) ^ 2) ≤
        ∑ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
          primeTotientSquareWeight p := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hpLower : D + 1 ≤ p :=
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hpMem).1).1
      exact maynardS2OuterScalarWeight_prime_sq_le_primeTotientSquareWeight
        (Finset.mem_filter.mp hpMem).2 (by omega)
    _ = primeTotientSquareTail D Q := by
      rfl
    _ ≤ 8 / (D : ℝ) := primeTotientSquareTail_le (by omega)

end BoundedGaps.Maynard
