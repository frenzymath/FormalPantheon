import BoundedGaps.Maynard.MaynardS2ReciprocalGSquarefreeFunction
import BoundedGaps.Maynard.ReciprocalTotientCorrection

noncomputable section

/-!
# Prime-local correction for the reciprocal-g S2 weight

The squarefree reciprocal-`g` weight is divided, in the Dirichlet-convolution
sense, by the coprime harmonic function. The prime value is an explicit
reciprocal-square correction. See `SEM-351`.
-/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction

noncomputable def maynardS2ReciprocalGCorrectionAF
    (W : ℕ) : ArithmeticFunction ℝ :=
  maynardS2ReciprocalGSquarefreeAF W * coprimeMobiusInvAF W

theorem maynardS2ReciprocalGCorrectionAF_isMultiplicative (W : ℕ) :
    (maynardS2ReciprocalGCorrectionAF W).IsMultiplicative := by
  unfold maynardS2ReciprocalGCorrectionAF
  exact (maynardS2ReciprocalGSquarefreeAF_isMultiplicative W).mul
    (coprimeMobiusInvAF_isMultiplicative W)

theorem maynardS2ReciprocalGCorrectionAF_apply_prime
    (W : ℕ) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    maynardS2ReciprocalGCorrectionAF W p =
      if p ∣ W then 0 else
        (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
  unfold maynardS2ReciprocalGCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      maynardS2ReciprocalGSquarefreeAF W x * coprimeMobiusInvAF W y)]
  have hdiv : p.divisors = {1, p} := by
    ext d
    simp [Nat.mem_divisors, hp.ne_zero, Nat.dvd_prime hp]
  have h1p : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    simpa using hp.ne_one.symm
  rw [hdiv, Finset.sum_insert h1p, Finset.sum_singleton]
  have hweightOne : maynardS2ReciprocalGSquarefreeAF W 1 = 1 :=
    (maynardS2ReciprocalGSquarefreeAF_isMultiplicative W).map_one
  have hinvOne : coprimeMobiusInvAF W 1 = 1 :=
    (coprimeMobiusInvAF_isMultiplicative W).map_one
  rw [hweightOne, Nat.div_one, Nat.div_self hp.pos, hinvOne, one_mul,
    maynardS2ReciprocalGSquarefreeAF_apply_prime W hp,
    coprimeMobiusInvAF_apply]
  by_cases hpW : p ∣ W
  · have hpc : ¬Nat.Coprime p W := by
      exact fun h => (hp.coprime_iff_not_dvd.mp h) hpW
    simp [hpW, hpc]
  · have hpc : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpW
    rw [if_neg hpW, if_neg hp.ne_zero, if_pos hpc,
      ArithmeticFunction.moebius_apply_prime hp]
    rw [Nat.cast_sub hp.two_le]
    simp only [hpW, if_false]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpM : (p : ℝ) - 2 ≠ 0 := by
      have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    field_simp [hpR, hpM]
    ring

end BoundedGaps.Maynard
