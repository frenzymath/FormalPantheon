import BoundedGaps.Maynard.WirsingLogMomentBalance

noncomputable section

/-!
# Quotient-floor balance for the squarefree reciprocal-totient mean

This is the finite logarithmic balance below GGPY2009, Lemma `L:Wirsing`,
source lines 803--842. It converts the natural quotient in SEM-378 to the real
logarithmic complement and absorbs the bounded prime-square correction. No
cumulative asymptotic is asserted here.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real
open scoped BigOperators

noncomputable def squarefreeCoprimeInvTotientRealQuotientLogMean
    (W Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Q).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W),
    ((1 : ℝ) / Nat.totient n) * Real.log ((Q : ℝ) / n)

private theorem squarefreeCoprimeInvTotientMean_eq_supported_sum
    (W Q : ℕ) :
    squarefreeCoprimeInvTotientMean W Q =
      ∑ n ∈ (Finset.Icc 1 Q).filter (fun n =>
        Squarefree n ∧ Nat.Coprime n W),
        (1 : ℝ) / Nat.totient n := by
  classical
  unfold squarefreeCoprimeInvTotientMean
  rw [← Finset.sum_filter]

private theorem squarefreeCoprimeInvTotientMean_nonneg
    (W Q : ℕ) :
    0 ≤ squarefreeCoprimeInvTotientMean W Q := by
  rw [squarefreeCoprimeInvTotientMean_eq_supported_sum]
  positivity

theorem squarefreeCoprimeInvTotientRealQuotientLogMean_eq_log_mul_mean_sub_logMean
    {W Q : ℕ} (hQ : 0 < Q) :
    squarefreeCoprimeInvTotientRealQuotientLogMean W Q =
      Real.log Q * squarefreeCoprimeInvTotientMean W Q -
        squarefreeCoprimeInvTotientLogMean W Q := by
  classical
  let S := (Finset.Icc 1 Q).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W)
  rw [squarefreeCoprimeInvTotientMean_eq_supported_sum]
  unfold squarefreeCoprimeInvTotientRealQuotientLogMean
    squarefreeCoprimeInvTotientLogMean
  rw [show (Finset.Icc 1 Q).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W) = S by rfl]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnBounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hnPos : 0 < n := Nat.zero_lt_of_lt hnBounds.1
  have hQReal : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [Real.log_div hQReal hnReal]
  ring

theorem abs_squarefreeCoprimeInvTotientQuotientLogMean_sub_real_le
    {W Q : ℕ} :
    |squarefreeCoprimeInvTotientQuotientLogMean W Q -
        squarefreeCoprimeInvTotientRealQuotientLogMean W Q| ≤
      Real.log 2 * squarefreeCoprimeInvTotientMean W Q := by
  classical
  let S := (Finset.Icc 1 Q).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W)
  have hmean : squarefreeCoprimeInvTotientMean W Q =
      ∑ n ∈ S, (1 : ℝ) / Nat.totient n := by
    simpa [S] using squarefreeCoprimeInvTotientMean_eq_supported_sum W Q
  unfold squarefreeCoprimeInvTotientQuotientLogMean
    squarefreeCoprimeInvTotientRealQuotientLogMean
  rw [show (Finset.Icc 1 Q).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W) = S by rfl]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ n ∈ S,
        (((1 : ℝ) / Nat.totient n) * Real.log (Q / n : ℕ) -
          ((1 : ℝ) / Nat.totient n) * Real.log ((Q : ℝ) / n))| ≤
        ∑ n ∈ S,
          |((1 : ℝ) / Nat.totient n) * Real.log (Q / n : ℕ) -
            ((1 : ℝ) / Nat.totient n) *
              Real.log ((Q : ℝ) / n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S,
        Real.log 2 * ((1 : ℝ) / Nat.totient n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnBounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      have hnPos : 0 < n := Nat.zero_lt_of_lt hnBounds.1
      have hendpoint := abs_log_natDiv_sub_log_div_le_log_two
        hnPos hnBounds.2
      have hweight : 0 ≤ (1 : ℝ) / Nat.totient n := by positivity
      calc
        |((1 : ℝ) / Nat.totient n) * Real.log (Q / n : ℕ) -
            ((1 : ℝ) / Nat.totient n) *
              Real.log ((Q : ℝ) / n)| =
            ((1 : ℝ) / Nat.totient n) *
              |Real.log (Q / n : ℕ) -
                Real.log ((Q : ℝ) / n)| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hweight]
        _ ≤ ((1 : ℝ) / Nat.totient n) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hendpoint hweight
        _ = Real.log 2 * ((1 : ℝ) / Nat.totient n) := by ring
    _ = Real.log 2 * squarefreeCoprimeInvTotientMean W Q := by
      rw [← Finset.mul_sum, ← hmean]

theorem exists_uniform_abs_twoLogMean_sub_log_mul_mean_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ {D P Q : ℕ}, 0 < P → 0 < Q →
        |2 * squarefreeCoprimeInvTotientLogMean
              (primorial D * P) Q -
            Real.log Q * squarefreeCoprimeInvTotientMean
              (primorial D * P) Q| ≤
          (K + Real.log D + primeLogDivisorMass P) *
            squarefreeCoprimeInvTotientMean (primorial D * P) Q := by
  obtain ⟨K₀, hK₀, hconvolution⟩ :=
    exists_uniform_abs_primeConvolution_sub_quotientLogMean_le
  obtain ⟨C, hC, hcorrection⟩ :=
    exists_uniform_primeLogPredecessorCorrection_bound
  let K := K₀ + 2 * Real.log 2 + C
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : 0 < K := by
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro D P Q hP hQ
  let W := primorial D * P
  let M := squarefreeCoprimeInvTotientMean W Q
  let L := squarefreeCoprimeInvTotientLogMean W Q
  let A := squarefreeCoprimeInvTotientPrimeConvolution W Q
  let T := squarefreeCoprimeInvTotientQuotientLogMean W Q
  let U := squarefreeCoprimeInvTotientRealQuotientLogMean W Q
  let R := squarefreeCoprimeInvTotientPrimeSquareRemainder W Q
  let E := K₀ + Real.log D + primeLogDivisorMass P + Real.log 2
  have hM : 0 ≤ M := squarefreeCoprimeInvTotientMean_nonneg W Q
  have hbalance : L = A + R := by
    simpa [L, A, R] using
      squarefreeCoprimeInvTotientLogMean_eq_prime_balance W Q
  have hreal : U = Real.log Q * M - L := by
    simpa [U, M, L] using
      squarefreeCoprimeInvTotientRealQuotientLogMean_eq_log_mul_mean_sub_logMean
        (W := W) hQ
  have hconv : |A - T| ≤ E * M := by
    simpa [W, A, T, E, M] using
      hconvolution (D := D) (P := P) (Q := Q) hP
  have hfloor : |T - U| ≤ Real.log 2 * M := by
    simpa [T, U, M] using
      abs_squarefreeCoprimeInvTotientQuotientLogMean_sub_real_le
        (W := W)
  have hRnonneg : 0 ≤ R := by
    simpa [R] using
      squarefreeCoprimeInvTotientPrimeSquareRemainder_nonneg W Q
  have hRle : R ≤ primeLogPredecessorCorrection Q * M := by
    simpa [R, M] using
      squarefreeCoprimeInvTotientPrimeSquareRemainder_le W Q
  have hcorr : primeLogPredecessorCorrection Q ≤ C := hcorrection Q
  calc
    |2 * squarefreeCoprimeInvTotientLogMean W Q -
        Real.log Q * squarefreeCoprimeInvTotientMean W Q| =
        |R + (A - T) + (T - U)| := by
      rw [show squarefreeCoprimeInvTotientLogMean W Q = L by rfl,
        show squarefreeCoprimeInvTotientMean W Q = M by rfl]
      congr 1
      calc
        2 * L - Real.log Q * M = L - U := by rw [hreal]; ring
        _ = R + (A - T) + (T - U) := by rw [hbalance]; ring
    _ ≤ |R| + |A - T| + |T - U| := by
      calc
        |R + (A - T) + (T - U)| ≤
        |R + (A - T)| + |T - U| := abs_add_le _ _
        _ ≤ |R| + |A - T| + |T - U| := by
          calc
            |R + (A - T)| + |T - U| =
                |T - U| + |R + (A - T)| := by ring
            _ ≤ |T - U| + (|R| + |A - T|) := by
              linarith [abs_add_le R (A - T)]
            _ = |R| + |A - T| + |T - U| := by ring
    _ ≤ R + E * M + Real.log 2 * M := by
      rw [abs_of_nonneg hRnonneg]
      exact add_le_add (add_le_add le_rfl hconv) hfloor
    _ ≤ primeLogPredecessorCorrection Q * M + E * M +
        Real.log 2 * M := by linarith
    _ = (K₀ + Real.log D + primeLogDivisorMass P +
          2 * Real.log 2 + primeLogPredecessorCorrection Q) * M := by
      dsimp [E]
      ring
    _ ≤ (K + Real.log D + primeLogDivisorMass P) * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      dsimp [K]
      linarith

end BoundedGaps.Maynard
