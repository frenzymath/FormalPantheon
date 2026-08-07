import BoundedGaps.Maynard.MaynardS2OuterMultiplicativeFunction

noncomputable section

/-!
# Squarefree multiplicative S2 outer weight

Maynard2013v3 and GGPY2009 use the squarefree factor `mu(n)^2` in the outer
summatory weight.  The pointwise Moebius square below records that support
exactly while retaining the modulus-excluded prime-local factors.
-/

namespace BoundedGaps.Maynard

open ArithmeticFunction

noncomputable def maynardS2OuterSquarefreeAF (W : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    (ArithmeticFunction.pmul
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
    (maynardS2OuterWeightAF W)

theorem maynardS2OuterSquarefreeAF_isMultiplicative (W : ℕ) :
    (maynardS2OuterSquarefreeAF W).IsMultiplicative := by
  unfold maynardS2OuterSquarefreeAF
  exact (ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
    ArithmeticFunction.isMultiplicative_moebius.intCast).pmul
      (maynardS2OuterWeightAF_isMultiplicative W)

theorem maynardS2OuterSquarefreeAF_apply_squarefree_of_coprime
    {W n : ℕ} (hn : Squarefree n) (hcop : Nat.Coprime n W) :
    maynardS2OuterSquarefreeAF W n =
      (Nat.totient n : ℝ) ^ 2 /
        ((maynardS2G n : ℝ) * (n : ℝ) ^ 2) := by
  unfold maynardS2OuterSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  have hmu : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
    exact_mod_cast (squarefree_iff_moebius_sq_eq_one n).mp hn
  calc
    (ArithmeticFunction.moebius n : ℝ) * ArithmeticFunction.moebius n *
        maynardS2OuterWeightAF W n =
        (ArithmeticFunction.moebius n : ℝ) ^ 2 *
          maynardS2OuterWeightAF W n := by ring
    _ = maynardS2OuterWeightAF W n := by rw [hmu, one_mul]
    _ = (Nat.totient n : ℝ) ^ 2 /
        ((maynardS2G n : ℝ) * (n : ℝ) ^ 2) :=
      maynardS2OuterWeightAF_apply_squarefree_of_coprime hn hcop

end BoundedGaps.Maynard
