import BoundedGaps.Maynard.MaynardS2OuterSquarefreeFunction
import BoundedGaps.Maynard.ReciprocalTotientCorrection

noncomputable section

/-!
# Prime-local correction for the S2 outer weight

The outer squarefree summand is compared with the coprime harmonic function
through `coprimeMobiusInvAF`.  Maynard2013v3 source lines 552--560 use exactly
this kind of convergent local correction behind the singular series.
-/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction

noncomputable def maynardS2OuterCorrectionAF (W : ℕ) : ArithmeticFunction ℝ :=
  maynardS2OuterSquarefreeAF W * coprimeMobiusInvAF W

theorem maynardS2OuterCorrectionAF_isMultiplicative (W : ℕ) :
    (maynardS2OuterCorrectionAF W).IsMultiplicative := by
  unfold maynardS2OuterCorrectionAF
  exact (maynardS2OuterSquarefreeAF_isMultiplicative W).mul
    (coprimeMobiusInvAF_isMultiplicative W)

theorem maynardS2OuterCorrectionAF_apply_prime
    (W : ℕ) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    maynardS2OuterCorrectionAF W p =
      if p ∣ W then 0 else
        (1 : ℝ) / ((p : ℝ) ^ 2 * ((p : ℝ) - 2)) := by
  unfold maynardS2OuterCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      maynardS2OuterSquarefreeAF W x * coprimeMobiusInvAF W y)]
  have hdiv : p.divisors = {1, p} := by
    ext d
    simp [Nat.mem_divisors, hp.ne_zero, Nat.dvd_prime hp]
  have h1p : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    simpa using hp.ne_one.symm
  rw [hdiv, Finset.sum_insert h1p, Finset.sum_singleton]
  have houterOne : maynardS2OuterSquarefreeAF W 1 = 1 := by
    exact (maynardS2OuterSquarefreeAF_isMultiplicative W).map_one
  have hinvOne : coprimeMobiusInvAF W 1 = 1 :=
    (coprimeMobiusInvAF_isMultiplicative W).map_one
  have houterPrime : maynardS2OuterSquarefreeAF W p =
      if p ∣ W then 0 else maynardS2OuterScalarWeight p := by
    unfold maynardS2OuterSquarefreeAF
    rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
    have hmu : (ArithmeticFunction.moebius p : ℝ) ^ 2 = 1 := by
      exact_mod_cast (squarefree_iff_moebius_sq_eq_one p).mp hp.squarefree
    calc
      (ArithmeticFunction.moebius p : ℝ) * ArithmeticFunction.moebius p *
          maynardS2OuterWeightAF W p =
          (ArithmeticFunction.moebius p : ℝ) ^ 2 *
            maynardS2OuterWeightAF W p := by ring
      _ = maynardS2OuterWeightAF W p := by rw [hmu, one_mul]
      _ = if p ∣ W then 0 else maynardS2OuterScalarWeight p :=
        maynardS2OuterWeightAF_apply_prime W hp
  rw [houterOne, Nat.div_one, Nat.div_self hp.pos, hinvOne, one_mul, houterPrime,
    coprimeMobiusInvAF_apply]
  by_cases hpW : p ∣ W
  · have hpc : ¬Nat.Coprime p W := by
      exact fun h => (hp.coprime_iff_not_dvd.mp h) hpW
    simp [hpW, hpc]
  · have hpc : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpW
    rw [if_neg hpW, if_neg hp.ne_zero, if_pos hpc,
      ArithmeticFunction.moebius_apply_prime hp]
    unfold maynardS2OuterScalarWeight
    rw [maynardS2G_prime hp, Nat.totient_prime hp,
      Nat.cast_sub hp.one_le, Nat.cast_sub hp.two_le]
    simp only [hpW, if_false]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpM : (p : ℝ) - 2 ≠ 0 := by
      have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    field_simp [hpR, hpM]
    ring

end BoundedGaps.Maynard
