import BoundedGaps.Maynard.CoprimeHarmonicErrorBound

noncomputable section

/-!
# Reciprocal-divisor envelope for squarefree moduli

The exact divisor Euler product turns the floor term in SEM-291 into a smooth
bound controlled by the predecessor prime-log mass.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real ArithmeticFunction

theorem sum_reciprocal_divisors_eq_primeFactors
    {W : ℕ} (hSq : Squarefree W) :
    (∑ d ∈ W.divisors, (1 : ℝ) / d) =
      ∏ p ∈ W.primeFactors, (1 + (1 : ℝ) / p) := by
  let invId : ArithmeticFunction ℝ :=
    ArithmeticFunction.pdiv (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      (ArithmeticFunction.id : ArithmeticFunction ℝ)
  have hinvId (n : ℕ) : invId n = (1 : ℝ) / n := by
    unfold invId
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.id_apply]
    by_cases hn : n = 0
    · simp [hn]
    · rw [ArithmeticFunction.zeta_apply_ne hn]
      norm_num
  have hmult : invId.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.pdiv
      ArithmeticFunction.isMultiplicative_id.natCast
  have hEuler := hmult.prodPrimeFactors_one_add_of_squarefree hSq
  simpa only [hinvId] using hEuler.symm

theorem sum_reciprocal_divisors_mul_prime
    {W p : ℕ} (hW : 0 < W) (hSq : Squarefree W)
    (hp : p.Prime) (hpW : Nat.Coprime p W) :
    (∑ d ∈ (W * p).divisors, (1 : ℝ) / d) =
      (1 + (1 : ℝ) / p) * ∑ d ∈ W.divisors, (1 : ℝ) / d := by
  have hSqMul : Squarefree (W * p) :=
    (Nat.squarefree_mul hpW.symm).2 ⟨hSq, hp.squarefree⟩
  rw [sum_reciprocal_divisors_eq_primeFactors hSqMul,
    sum_reciprocal_divisors_eq_primeFactors hSq]
  have hpNotMem : p ∉ W.primeFactors := by
    intro hpMem
    have hpdvd := Nat.dvd_of_mem_primeFactors hpMem
    exact (hp.coprime_iff_not_dvd.mp hpW) hpdvd
  have hdisj : Disjoint W.primeFactors ({p} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]
    exact hpNotMem
  rw [Nat.primeFactors_mul hW.ne' hp.ne_zero, hp.primeFactors,
    Finset.prod_union hdisj, Finset.prod_singleton]
  ring

theorem prod_one_add_primeReciprocal_le_exp (W : ℕ) :
    (∏ p ∈ W.primeFactors, (1 + (1 : ℝ) / p)) ≤
      Real.exp (∑ p ∈ W.primeFactors, (1 : ℝ) / p) := by
  calc
    (∏ p ∈ W.primeFactors, (1 + (1 : ℝ) / p)) ≤
        ∏ p ∈ W.primeFactors, Real.exp ((1 : ℝ) / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa [add_comm] using Real.add_one_le_exp ((1 : ℝ) / p)
    _ = Real.exp (∑ p ∈ W.primeFactors, (1 : ℝ) / p) := by
      rw [← Real.exp_sum]

theorem sum_primeReciprocal_le_predecessorMass_div_log_two (W : ℕ) :
    (∑ p ∈ W.primeFactors, (1 : ℝ) / p) ≤
      primeLogPredecessorDivisorMass W / Real.log 2 := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlogTwoPos).2
  unfold primeLogPredecessorDivisorMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hpPredPos : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hpPrime.one_lt
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
  have hlog : Real.log 2 ≤ Real.log p := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; norm_num)
      (by simp only [Set.mem_Ioi]; exact hpPos) hpTwo
  have hinv : (1 : ℝ) / p ≤ (1 : ℝ) / (p - 1 : ℕ) := by
    apply one_div_le_one_div_of_le hpPredPos
    exact_mod_cast Nat.sub_le p 1
  calc
    (1 : ℝ) / p * Real.log 2 ≤ (1 : ℝ) / p * Real.log p := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (1 : ℝ) / (p - 1 : ℕ) * Real.log p := by
      exact mul_le_mul_of_nonneg_right hinv (Real.log_natCast_nonneg p)
    _ = Real.log p / (p - 1 : ℕ) := by ring

theorem sum_reciprocal_divisors_le_exp_predecessorMass
    {W : ℕ} (hSq : Squarefree W) :
    (∑ d ∈ W.divisors, (1 : ℝ) / d) ≤
      Real.exp (primeLogPredecessorDivisorMass W / Real.log 2) := by
  rw [sum_reciprocal_divisors_eq_primeFactors hSq]
  exact (prod_one_add_primeReciprocal_le_exp W).trans
    (Real.exp_le_exp.mpr
      (sum_primeReciprocal_le_predecessorMass_div_log_two W))

theorem abs_coprimeHarmonicError_le_smooth_envelope
    {W Q : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hWQ : W ≤ Q) :
    |coprimeHarmonicError W Q| ≤
      2 * (W : ℝ) / Q +
        Real.log 2 *
          Real.exp (primeLogPredecessorDivisorMass W / Real.log 2) := by
  have hError := abs_coprimeHarmonicError_le_divisor_envelope hW hSq hWQ
  have hCard : (W.divisors.card : ℝ) ≤ W := by
    exact_mod_cast Nat.card_divisors_le_self W
  have hFirst : 2 * (W.divisors.card : ℝ) / Q ≤ 2 * (W : ℝ) / Q := by
    gcongr
  have hSecond := mul_le_mul_of_nonneg_left
    (sum_reciprocal_divisors_le_exp_predecessorMass hSq)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  exact hError.trans (add_le_add hFirst hSecond)

end BoundedGaps.Maynard
