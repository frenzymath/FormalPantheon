import BoundedGaps.Maynard.AugmentedPreSieveLocalSeries
import BoundedGaps.Maynard.ReciprocalTotientCorrection

noncomputable section

/-!
# Reciprocal-totient arithmetic function for the augmented modulus

The concrete squarefree reciprocal-totient weight is exposed as public
multiplicative data and matched to the augmented gamma prime weight.
-/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction

theorem squarefreeCoprimeInvTotientAF_isMultiplicative (W : ℕ) :
    (squarefreeCoprimeInvTotientAF W).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [squarefreeCoprimeInvTotientAF]
  · intro m n hm hn hmn
    rw [squarefreeCoprimeInvTotientAF_apply,
      squarefreeCoprimeInvTotientAF_apply,
      squarefreeCoprimeInvTotientAF_apply]
    simp only [mul_ne_zero hm hn, hm, hn, ↓reduceIte]
    simp only [Nat.squarefree_mul hmn, Nat.coprime_mul_iff_left]
    by_cases hms : Squarefree m
    · by_cases hns : Squarefree n
      · by_cases hmc : Nat.Coprime m W
        · by_cases hnc : Nat.Coprime n W
          · rw [Nat.totient_mul hmn]
            push_cast
            rw [if_pos ⟨⟨hms, hns⟩, ⟨hmc, hnc⟩⟩,
              if_pos ⟨hms, hmc⟩, if_pos ⟨hns, hnc⟩]
            simp only [one_div, mul_inv_rev]
            ring_nf
          · have hnCond : ¬(Squarefree n ∧ Nat.Coprime n W) :=
              fun h => hnc h.2
            rw [if_neg (fun h => hnc h.2.2), if_neg hnCond]
            ring_nf
        · have hmCond : ¬(Squarefree m ∧ Nat.Coprime m W) :=
            fun h => hmc h.2
          rw [if_neg (fun h => hmc h.2.1), if_neg hmCond]
          ring_nf
      · simp [hms, hns]
    · simp [hms]

theorem squarefreeCoprimeInvTotientAF_apply_prime
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    squarefreeCoprimeInvTotientAF W p =
      if p ∣ W then 0 else (1 : ℝ) / (p - 1 : ℕ) := by
  rw [squarefreeCoprimeInvTotientAF_apply]
  simp only [hp.ne_zero, ↓reduceIte, hp.squarefree, true_and,
    hp.coprime_iff_not_dvd, Nat.totient_prime hp]
  by_cases hpW : p ∣ W <;> simp [hpW]

theorem squarefreeCoprimeInvTotientAF_prime_eq_augmentedGammaWeight
    (D P : ℕ) {p : ℕ} (hp : p.Prime) :
    squarefreeCoprimeInvTotientAF (primorial D * P) p =
      augmentedPreSieveGamma D P p /
        ((p : ℝ) - augmentedPreSieveGamma D P p) := by
  rw [squarefreeCoprimeInvTotientAF_apply_prime _ hp,
    augmentedPreSieveGamma_prime_weight D P hp]

theorem sum_squarefreeCoprimeInvTotientAF_eq_mean (W Q : ℕ) :
    (∑ n ∈ Finset.Icc 0 Q, squarefreeCoprimeInvTotientAF W n) =
      squarefreeCoprimeInvTotientMean W Q := by
  classical
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le Q), Finset.sum_cons]
  rw [show squarefreeCoprimeInvTotientAF W 0 = 0 by
    exact (squarefreeCoprimeInvTotientAF W).map_zero, zero_add]
  rw [← Finset.Icc_add_one_left_eq_Ioc]
  unfold squarefreeCoprimeInvTotientMean
  apply Finset.sum_congr rfl
  intro n hn
  rw [squarefreeCoprimeInvTotientAF_apply]
  have hnPos : 0 < n := zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1
  rw [if_neg hnPos.ne']

end BoundedGaps.Maynard
