import BoundedGaps.Maynard.WirsingPrimeDivisorReindex
import BoundedGaps.Maynard.ConcreteRoughModulusPrimeLogMass
import BoundedGaps.Maynard.PrimePredecessorMertens
import BoundedGaps.Maynard.CoprimeHarmonicQuotientEndpoint

noncomputable section

/-!
# Finite logarithmic balance for the squarefree reciprocal-totient mean

This is the next finite arithmetic step below GGPY2009, Lemma `L:Wirsing`.
It isolates the prime-prefix convolution and its squarefree correction; no
uniform cumulative asymptotic is asserted here.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real
open scoped BigOperators

noncomputable def squarefreeCoprimePrimeLogPrefix
    (W X : ℕ) : ℝ :=
  ∑ p ∈ X.primesLE.filter (fun p => ¬p ∣ W),
    Real.log p / (p : ℝ)

noncomputable def squarefreeCoprimeInvTotientPrimeConvolution
    (W Q : ℕ) : ℝ :=
  ∑ p ∈ Q.primesLE.filter (fun p => ¬p ∣ W),
    (Real.log p / (p : ℝ)) *
      squarefreeCoprimeInvTotientMean W (Q / p)

noncomputable def squarefreeCoprimeInvTotientPrimeSquareRemainder
    (W Q : ℕ) : ℝ :=
  ∑ p ∈ Q.primesLE.filter (fun p => ¬p ∣ W),
    (Real.log p / ((p : ℝ) * Nat.totient p)) *
      (squarefreeCoprimeInvTotientMean (W * p) (Q / p) -
        squarefreeCoprimeInvTotientMean (W * p) (Q / (p * p)))

private theorem squarefreeCoprimeInvTotientMean_nonneg
    (W Q : ℕ) :
    0 ≤ squarefreeCoprimeInvTotientMean W Q := by
  classical
  unfold squarefreeCoprimeInvTotientMean
  apply Finset.sum_nonneg
  intro n hn
  split_ifs <;> positivity

private theorem squarefreeCoprimeInvTotientMean_mono
    {W A B : ℕ} (hAB : A ≤ B) :
    squarefreeCoprimeInvTotientMean W A ≤
      squarefreeCoprimeInvTotientMean W B := by
  classical
  unfold squarefreeCoprimeInvTotientMean
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hAB⟩
  · intro n hn hnNot
    split_ifs <;> positivity

private theorem squarefreeCoprimeInvTotientMean_mul_prime_le
    {W Q p : ℕ} (hp : p.Prime) (hpW : Nat.Coprime p W) :
    squarefreeCoprimeInvTotientMean (W * p) Q ≤
      squarefreeCoprimeInvTotientMean W Q := by
  have hrec := squarefreeCoprimeInvTotientMean_mul_prime
    (W := W) (Q := Q) hp hpW
  have hcoef : 0 ≤ (1 : ℝ) / Nat.totient p := by positivity
  have hmean : 0 ≤ squarefreeCoprimeInvTotientMean (W * p) (Q / p) :=
    squarefreeCoprimeInvTotientMean_nonneg _ _
  have hprod : 0 ≤ (1 : ℝ) / Nat.totient p *
      squarefreeCoprimeInvTotientMean (W * p) (Q / p) :=
    mul_nonneg hcoef hmean
  linarith

private theorem squarefreeCoprimeInvTotientMean_prime_diff_nonneg
    {W Q p : ℕ} :
    0 ≤ squarefreeCoprimeInvTotientMean (W * p) (Q / p) -
      squarefreeCoprimeInvTotientMean (W * p) (Q / (p * p)) := by
  apply sub_nonneg.mpr
  apply squarefreeCoprimeInvTotientMean_mono
  rw [← Nat.div_div_eq_div_mul]
  exact Nat.div_le_self _ _

private theorem squarefreeCoprimeInvTotientMean_prime_diff_le
    {W Q p : ℕ} (hp : p.Prime) (hpW : Nat.Coprime p W) :
    squarefreeCoprimeInvTotientMean (W * p) (Q / p) -
        squarefreeCoprimeInvTotientMean (W * p) (Q / (p * p)) ≤
      squarefreeCoprimeInvTotientMean W Q := by
  have hdiff := squarefreeCoprimeInvTotientMean_prime_diff_nonneg
    (W := W) (Q := Q) (p := p)
  have hsmall := squarefreeCoprimeInvTotientMean_nonneg
    (W * p) (Q / (p * p))
  have hleft := squarefreeCoprimeInvTotientMean_mul_prime_le
    (W := W) (Q := Q / p) hp hpW
  have hmono := squarefreeCoprimeInvTotientMean_mono
    (W := W) (A := Q / p) (B := Q) (Nat.div_le_self Q p)
  linarith

private theorem squarefreeCoprimeInvTotientMean_eq_Icc_mul_le
    {W Q p : ℕ} (hp : 0 < p) :
    squarefreeCoprimeInvTotientMean W (Q / p) =
      ∑ n ∈ Finset.Icc 1 Q,
        if Squarefree n ∧ Nat.Coprime n W ∧ n * p ≤ Q then
          (1 : ℝ) / Nat.totient n else 0 := by
  classical
  let S := (Finset.Icc 1 (Q / p)).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W)
  let T := Finset.Icc 1 Q
  have hfilter : S = T.filter (fun n =>
      Squarefree n ∧ Nat.Coprime n W ∧ n * p ≤ Q) := by
    ext n
    simp only [S, T, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hnPos, hnQ⟩, hnData⟩
      have hnp : n * p ≤ Q := (Nat.le_div_iff_mul_le hp).mp hnQ
      exact ⟨⟨hnPos,
          (Nat.le_mul_of_pos_right n hp).trans hnp⟩,
        hnData.1, hnData.2, hnp⟩
    · rintro ⟨⟨hnPos, hnQ⟩, hnSq, hnCop, hnp⟩
      have hnDiv : n ≤ Q / p := (Nat.le_div_iff_mul_le hp).mpr hnp
      exact ⟨⟨hnPos, hnDiv⟩, hnSq, hnCop⟩
  unfold squarefreeCoprimeInvTotientMean
  rw [← Finset.sum_filter]
  have hfilter' :
      (Finset.Icc 1 (Q / p)).filter (fun n =>
        Squarefree n ∧ Nat.Coprime n W) =
        (Finset.Icc 1 Q).filter (fun n =>
          Squarefree n ∧ Nat.Coprime n W ∧ n * p ≤ Q) := by
    simpa [S, T] using hfilter
  rw [hfilter', Finset.sum_filter]

theorem squarefreeCoprimeInvTotientPrimeConvolution_eq_prefix_sum
    (W Q : ℕ) :
    squarefreeCoprimeInvTotientPrimeConvolution W Q =
      ∑ n ∈ (Finset.Icc 1 Q).filter (fun n =>
        Squarefree n ∧ Nat.Coprime n W),
        ((1 : ℝ) / Nat.totient n) *
          squarefreeCoprimePrimeLogPrefix W (Q / n) := by
  classical
  let P := Q.primesLE.filter (fun p => ¬p ∣ W)
  let N := Finset.Icc 1 Q
  let S := N.filter (fun n => Squarefree n ∧ Nat.Coprime n W)
  unfold squarefreeCoprimeInvTotientPrimeConvolution
  have hswap :
      (∑ p ∈ P,
        (Real.log p / (p : ℝ)) *
          squarefreeCoprimeInvTotientMean W (Q / p)) =
        ∑ n ∈ N,
          ∑ p ∈ P,
            if Squarefree n ∧ Nat.Coprime n W ∧ n * p ≤ Q then
              (Real.log p / (p : ℝ)) *
                ((1 : ℝ) / Nat.totient n) else 0 := by
    calc
      _ = ∑ p ∈ P, ∑ n ∈ N,
          if Squarefree n ∧ Nat.Coprime n W ∧ n * p ≤ Q then
            (Real.log p / (p : ℝ)) * ((1 : ℝ) / Nat.totient n) else 0 := by
        apply Finset.sum_congr rfl
        intro p hpMem
        rw [squarefreeCoprimeInvTotientMean_eq_Icc_mul_le
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hpMem).1).pos]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hcond : Squarefree n ∧ Nat.Coprime n W ∧ n * p ≤ Q
        · simp [hcond]
        · simp [hcond]
      _ = _ := Finset.sum_comm
  have hSsum :
      (∑ n ∈ S, ((1 : ℝ) / Nat.totient n) *
          squarefreeCoprimePrimeLogPrefix W (Q / n)) =
        ∑ n ∈ N, if Squarefree n ∧ Nat.Coprime n W then
          ((1 : ℝ) / Nat.totient n) *
            squarefreeCoprimePrimeLogPrefix W (Q / n) else 0 := by
    unfold S
    rw [Finset.sum_filter]
  rw [hswap, hSsum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsupport : Squarefree n ∧ Nat.Coprime n W
  · have hprefix :
        squarefreeCoprimePrimeLogPrefix W (Q / n) =
          ∑ p ∈ P, if n * p ≤ Q then Real.log p / (p : ℝ) else 0 := by
      have hset :
          (Q / n).primesLE.filter (fun p => ¬p ∣ W) =
            P.filter (fun p => n * p ≤ Q) := by
        ext p
        simp only [P, Finset.mem_filter, Nat.mem_primesLE]
        have hnPos : 0 < n := (Finset.mem_Icc.mp hn).1
        constructor
        · rintro ⟨⟨hpQn, hp⟩, hpW⟩
          have hpQ : p ≤ Q := hpQn.trans (Nat.div_le_self Q n)
          have hnp : n * p ≤ Q :=
            by simpa [Nat.mul_comm] using
              (Nat.le_div_iff_mul_le hnPos).mp hpQn
          exact ⟨⟨⟨hpQ, hp⟩, hpW⟩, hnp⟩
        · rintro ⟨⟨⟨hpQ, hp⟩, hpW⟩, hnp⟩
          have hpn : p * n ≤ Q := by simpa [Nat.mul_comm] using hnp
          have hpQn : p ≤ Q / n :=
            (Nat.le_div_iff_mul_le hnPos).mpr hpn
          exact ⟨⟨hpQn, hp⟩, hpW⟩
      unfold squarefreeCoprimePrimeLogPrefix
      rw [hset, Finset.sum_filter]
    rw [if_pos hsupport, hprefix, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hpMem
    by_cases hnp : n * p ≤ Q <;>
      simp [hsupport.1, hsupport.2, hnp, mul_comm]
  · rw [if_neg hsupport]
    apply Finset.sum_eq_zero
    intro p hpMem
    rw [if_neg]
    intro hcond
    exact hsupport ⟨hcond.1, hcond.2.1⟩

private theorem squarefreeCoprimePrimeLogPrefix_eq_augmented
    (D P X : ℕ) :
    squarefreeCoprimePrimeLogPrefix (primorial D * P) X =
      augmentedPreSievedPrimeLogIntervalSum D P 2 X := by
  unfold squarefreeCoprimePrimeLogPrefix
    augmentedPreSievedPrimeLogIntervalSum
  have hs : X.primesLE \ Nat.primesLE (2 - 1) = X.primesLE := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpX, hp⟩, hpNot⟩
      exact ⟨hpX, hp⟩
    · rintro ⟨hpX, hp⟩
      refine ⟨⟨hpX, hp⟩, ?_⟩
      have hpTwo := hp.two_le
      omega
  rw [hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p ∣ primorial D * P <;> simp [h]

theorem exists_uniform_squarefreeCoprimePrimeLogPrefix_sub_log_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ {D P X : ℕ}, 0 < P →
        |squarefreeCoprimePrimeLogPrefix (primorial D * P) X -
            Real.log X| ≤
          K + Real.log D + primeLogDivisorMass P + Real.log 2 := by
  obtain ⟨K, hK, hinterval⟩ :=
    exists_uniform_augmentedPreSievedPrimeLogInterval_bounds
  refine ⟨K, hK, ?_⟩
  intro D P X hP
  have hlogD : 0 ≤ Real.log D := Real.log_natCast_nonneg D
  have hmass : 0 ≤ primeLogDivisorMass P := by
    unfold primeLogDivisorMass
    positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hX : X < 2
  · have hXcases : X = 0 ∨ X = 1 := by omega
    rcases hXcases with rfl | rfl <;>
      simp [squarefreeCoprimePrimeLogPrefix] <;> linarith
  · have hX2 : 2 ≤ X := by omega
    have hbound := hinterval (D := D) (P := P) (w := 2) (z := X)
      hP (by norm_num) hX2
    have hprefix := squarefreeCoprimePrimeLogPrefix_eq_augmented D P X
    have hlogX : (0 : ℝ) < X := by exact_mod_cast (Nat.zero_lt_of_lt hX2)
    have hlogDiv : Real.log ((X : ℝ) / (2 : ℝ)) =
        Real.log X - Real.log 2 := by
      rw [Real.log_div (ne_of_gt hlogX) (by norm_num)]
    have hupper :
        squarefreeCoprimePrimeLogPrefix (primorial D * P) X -
            Real.log X ≤ K + Real.log D + primeLogDivisorMass P + Real.log 2 := by
      rw [hprefix]
      norm_num only [Nat.cast_ofNat] at hbound
      rw [hlogDiv] at hbound
      linarith [hbound.2]
    have hlower :
        -(K + Real.log D + primeLogDivisorMass P + Real.log 2) ≤
          squarefreeCoprimePrimeLogPrefix (primorial D * P) X -
            Real.log X := by
      rw [hprefix]
      norm_num only [Nat.cast_ofNat] at hbound
      rw [hlogDiv] at hbound
      linarith [hbound.1]
    exact abs_le.mpr ⟨hlower, hupper⟩

noncomputable def squarefreeCoprimeInvTotientQuotientLogMean
    (W Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Q).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W),
    ((1 : ℝ) / Nat.totient n) * Real.log (Q / n : ℕ)

theorem exists_uniform_abs_primeConvolution_sub_quotientLogMean_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ {D P Q : ℕ}, 0 < P →
        |squarefreeCoprimeInvTotientPrimeConvolution
              (primorial D * P) Q -
            squarefreeCoprimeInvTotientQuotientLogMean
              (primorial D * P) Q| ≤
          (K + Real.log D + primeLogDivisorMass P + Real.log 2) *
            squarefreeCoprimeInvTotientMean (primorial D * P) Q := by
  obtain ⟨K, hK, hprefixBound⟩ :=
    exists_uniform_squarefreeCoprimePrimeLogPrefix_sub_log_bound
  refine ⟨K, hK, ?_⟩
  intro D P Q hP
  let W := primorial D * P
  let S := (Finset.Icc 1 Q).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W)
  let E := K + Real.log D + primeLogDivisorMass P + Real.log 2
  have hmean :
      squarefreeCoprimeInvTotientMean W Q =
        ∑ n ∈ S, (1 : ℝ) / Nat.totient n := by
    unfold squarefreeCoprimeInvTotientMean
    rw [show S = (Finset.Icc 1 Q).filter (fun n =>
      Squarefree n ∧ Nat.Coprime n W) by rfl, Finset.sum_filter]
  rw [squarefreeCoprimeInvTotientPrimeConvolution_eq_prefix_sum]
  unfold squarefreeCoprimeInvTotientQuotientLogMean
  rw [show (primorial D * P) = W by rfl]
  rw [show (Finset.Icc 1 Q).filter (fun n =>
    Squarefree n ∧ Nat.Coprime n W) = S by rfl]
  rw [← Finset.sum_sub_distrib]
  calc
    |(∑ n ∈ S, (
        ((1 : ℝ) / Nat.totient n) *
            squarefreeCoprimePrimeLogPrefix W (Q / n) -
          ((1 : ℝ) / Nat.totient n) * Real.log (Q / n : ℕ)))| ≤
        ∑ n ∈ S,
          |((1 : ℝ) / Nat.totient n) *
              squarefreeCoprimePrimeLogPrefix W (Q / n) -
            ((1 : ℝ) / Nat.totient n) *
              Real.log (Q / n : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, E * ((1 : ℝ) / Nat.totient n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hprefix := hprefixBound (D := D) (P := P) (X := Q / n) hP
      have hweight : 0 ≤ (1 : ℝ) / Nat.totient n := by positivity
      calc
        |((1 : ℝ) / Nat.totient n) *
              squarefreeCoprimePrimeLogPrefix W (Q / n) -
            ((1 : ℝ) / Nat.totient n) *
              Real.log (Q / n : ℕ)| =
            ((1 : ℝ) / Nat.totient n) *
              |squarefreeCoprimePrimeLogPrefix W (Q / n) -
                Real.log (Q / n : ℕ)| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hweight]
        _ ≤ ((1 : ℝ) / Nat.totient n) * E :=
          mul_le_mul_of_nonneg_left (by simpa [W, E] using hprefix) hweight
        _ = E * ((1 : ℝ) / Nat.totient n) := by ring
    _ = E * squarefreeCoprimeInvTotientMean W Q := by
      rw [← Finset.mul_sum, hmean]
    _ = _ := by rfl

theorem squarefreeCoprimeInvTotientLogMean_eq_prime_balance
    (W Q : ℕ) :
    squarefreeCoprimeInvTotientLogMean W Q =
      squarefreeCoprimeInvTotientPrimeConvolution W Q +
        squarefreeCoprimeInvTotientPrimeSquareRemainder W Q := by
  classical
  rw [squarefreeCoprimeInvTotientLogMean_eq_prime_sum]
  unfold squarefreeCoprimeInvTotientPrimeConvolution
    squarefreeCoprimeInvTotientPrimeSquareRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpMem
  have hpData := Finset.mem_filter.mp hpMem
  have hp := Nat.prime_of_mem_primesLE hpData.1
  have hpW : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpData.2
  have hrec := squarefreeCoprimeInvTotientMean_mul_prime
    (W := W) (Q := Q / p) hp hpW
  rw [Nat.div_div_eq_div_mul] at hrec
  have htot := Nat.totient_prime hp
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlocal :
      (Real.log p / Nat.totient p) *
          squarefreeCoprimeInvTotientMean (W * p) (Q / p) =
        (Real.log p / (p : ℝ)) *
            squarefreeCoprimeInvTotientMean W (Q / p) +
          (Real.log p / ((p : ℝ) * Nat.totient p)) *
            (squarefreeCoprimeInvTotientMean (W * p) (Q / p) -
              squarefreeCoprimeInvTotientMean (W * p) (Q / (p * p))) := by
    rw [htot] at hrec ⊢
    have hpredCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_le]
      norm_num
    rw [hpredCast] at hrec ⊢
    have hC : squarefreeCoprimeInvTotientMean W (Q / p) =
        squarefreeCoprimeInvTotientMean (W * p) (Q / p) +
          (1 : ℝ) / ((p : ℝ) - 1) *
            squarefreeCoprimeInvTotientMean (W * p) (Q / (p * p)) := by
      linarith [hrec]
    rw [hC]
    have hpPredR : (p : ℝ) - 1 ≠ 0 := by
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    field_simp [hpR, hpPredR]
    ring
  exact hlocal

theorem squarefreeCoprimeInvTotientPrimeSquareRemainder_nonneg
    (W Q : ℕ) :
    0 ≤ squarefreeCoprimeInvTotientPrimeSquareRemainder W Q := by
  classical
  unfold squarefreeCoprimeInvTotientPrimeSquareRemainder
  apply Finset.sum_nonneg
  intro p hpMem
  have hpData := Finset.mem_filter.mp hpMem
  have hp := Nat.prime_of_mem_primesLE hpData.1
  have hpW : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpData.2
  apply mul_nonneg
  · positivity
  · exact squarefreeCoprimeInvTotientMean_prime_diff_nonneg
      (W := W) (Q := Q) (p := p)

theorem squarefreeCoprimeInvTotientPrimeSquareRemainder_le
    (W Q : ℕ) :
    squarefreeCoprimeInvTotientPrimeSquareRemainder W Q ≤
      primeLogPredecessorCorrection Q *
        squarefreeCoprimeInvTotientMean W Q := by
  classical
  unfold squarefreeCoprimeInvTotientPrimeSquareRemainder
  let S := Q.primesLE.filter (fun p => ¬p ∣ W)
  have hsum :
      (∑ p ∈ S,
        (Real.log p / ((p : ℝ) * Nat.totient p)) *
          (squarefreeCoprimeInvTotientMean (W * p) (Q / p) -
            squarefreeCoprimeInvTotientMean (W * p) (Q / (p * p)))) ≤
        ∑ p ∈ S,
          Real.log p / ((p : ℝ) * Nat.totient p) *
            squarefreeCoprimeInvTotientMean W Q := by
    apply Finset.sum_le_sum
    intro p hpMem
    have hpData := Finset.mem_filter.mp hpMem
    have hp := Nat.prime_of_mem_primesLE hpData.1
    have hpW : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpData.2
    apply mul_le_mul_of_nonneg_left
      (squarefreeCoprimeInvTotientMean_prime_diff_le hp hpW)
    positivity
  have hsubset : S ⊆ Q.primesLE := Finset.filter_subset _ _
  have hcoeff :
      (∑ p ∈ S, Real.log p / ((p : ℝ) * Nat.totient p)) ≤
        primeLogPredecessorCorrection Q := by
    calc
      (∑ p ∈ S, Real.log p / ((p : ℝ) * Nat.totient p)) =
          ∑ p ∈ S, Real.log p / ((p : ℝ) * (p - 1 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro p hpMem
        rw [Nat.totient_prime (Nat.prime_of_mem_primesLE
          (hsubset hpMem))]
      _ ≤ ∑ p ∈ Q.primesLE,
          Real.log p / ((p : ℝ) * (p - 1 : ℕ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro p hpMem hpNot
        positivity
      _ = primeLogPredecessorCorrection Q := by rfl
  calc
    _ ≤ ∑ p ∈ S,
        Real.log p / ((p : ℝ) * Nat.totient p) *
          squarefreeCoprimeInvTotientMean W Q := hsum
    _ = (∑ p ∈ S, Real.log p / ((p : ℝ) * Nat.totient p)) *
        squarefreeCoprimeInvTotientMean W Q := by rw [Finset.sum_mul]
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right hcoeff
        (squarefreeCoprimeInvTotientMean_nonneg W Q)

end BoundedGaps.Maynard
