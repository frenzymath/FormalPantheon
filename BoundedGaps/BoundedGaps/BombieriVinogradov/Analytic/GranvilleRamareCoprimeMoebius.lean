import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthCoefficient

namespace BoundedGaps.Maynard

open scoped BigOperators

private theorem sum_moebius_divisors_gcd
    {m P : ℕ} :
    (∑ d ∈ (m.gcd P).divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      if Nat.Coprime m P then 1 else 0 := by
  have hInteger :
      (∑ d ∈ (m.gcd P).divisors, ArithmeticFunction.moebius d) =
        if Nat.Coprime m P then (1 : ℤ) else 0 := by
    calc
      (∑ d ∈ (m.gcd P).divisors, ArithmeticFunction.moebius d) =
          (ArithmeticFunction.moebius * ArithmeticFunction.zeta) (m.gcd P) := by
        rw [ArithmeticFunction.coe_mul_zeta_apply]
      _ = (1 : ArithmeticFunction ℤ) (m.gcd P) := by
        rw [ArithmeticFunction.moebius_mul_coe_zeta]
      _ = if Nat.Coprime m P then 1 else 0 := by
        by_cases hCoprime : Nat.Coprime m P <;> simp [hCoprime]
  exact_mod_cast hInteger

/-!
`GranvilleRamare1996`, Section 10, Lemma 10.2 (manuscript p. 42).  The proof
below uses the same finite inclusion-exclusion argument as the source.
Instead of first replacing `D` by a product of primes, it takes the product
of all admissible indices; this gives the same divisor incidence relation on
`(0, N]`.
-/
theorem abs_sum_moebius_div_coprime_le_one (D N : ℕ) :
    |∑ n ∈ (Finset.Ioc 0 N).filter (fun n => Nat.Coprime n D),
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)| ≤ 1 := by
  classical
  by_cases hN : N = 0
  · subst N
    simp
  have hNPos : 0 < N := Nat.pos_of_ne_zero hN
  let S : Finset ℕ :=
    (Finset.Ioc 0 N).filter (fun n => Nat.Coprime n D)
  let P : ℕ := ∏ n ∈ S, n
  let A : Finset ℕ :=
    (Finset.Ioc 0 N).filter (fun m => Nat.Coprime m P)

  have hPCoprime : Nat.Coprime P D := by
    dsimp [P]
    apply Nat.Coprime.prod_left
    intro n hn
    exact (Finset.mem_filter.mp hn).2

  have hRestrictedDivisors (m : ℕ) (hm : m ∈ Finset.Ioc 0 N) :
      (m.gcd P).divisors =
        m.divisors.filter (fun n => Nat.Coprime n D) := by
    have hmPos : 0 < m := (Finset.mem_Ioc.mp hm).1
    have hGcdPos : 0 < m.gcd P := Nat.gcd_pos_of_pos_left P hmPos
    ext n
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hnGcd, -⟩
      have hnm : n ∣ m := hnGcd.trans (Nat.gcd_dvd_left m P)
      have hnP : n ∣ P := hnGcd.trans (Nat.gcd_dvd_right m P)
      exact ⟨⟨hnm, hmPos.ne'⟩, Nat.Coprime.of_dvd_left hnP hPCoprime⟩
    · rintro ⟨⟨hnm, -⟩, hnCoprime⟩
      have hnPos : 0 < n := Nat.pos_of_dvd_of_pos hnm hmPos
      have hnLeN : n ≤ N :=
        (Nat.le_of_dvd hmPos hnm).trans (Finset.mem_Ioc.mp hm).2
      have hnS : n ∈ S := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨hnPos, hnLeN⟩, hnCoprime⟩
      have hnP : n ∣ P := by
        dsimp [P]
        exact Finset.dvd_prod_of_mem (fun k : ℕ => k) hnS
      exact ⟨Nat.dvd_gcd hnm hnP, hGcdPos.ne'⟩

  have hRangeDivisors (m : ℕ) (hm : m ∈ Finset.Ioc 0 N) :
      S.filter (fun n => n ∣ m) =
        m.divisors.filter (fun n => Nat.Coprime n D) := by
    have hmPos : 0 < m := (Finset.mem_Ioc.mp hm).1
    ext n
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hnS, hnm⟩
      exact ⟨⟨hnm, hmPos.ne'⟩, (Finset.mem_filter.mp hnS).2⟩
    · rintro ⟨⟨hnm, -⟩, hnCoprime⟩
      have hnPos : 0 < n := Nat.pos_of_dvd_of_pos hnm hmPos
      have hnLeN : n ≤ N :=
        (Nat.le_of_dvd hmPos hnm).trans (Finset.mem_Ioc.mp hm).2
      exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hnPos, hnLeN⟩, hnCoprime⟩, hnm⟩

  have hIndicator (m : ℕ) (hm : m ∈ Finset.Ioc 0 N) :
      (∑ n ∈ S, if n ∣ m then
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0) =
        if Nat.Coprime m P then 1 else 0 := by
    calc
      (∑ n ∈ S, if n ∣ m then
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0) =
          ∑ n ∈ S.filter (fun n => n ∣ m),
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
        symm
        rw [Finset.sum_filter]
      _ = ∑ n ∈ m.divisors.filter (fun n => Nat.Coprime n D),
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
        rw [hRangeDivisors m hm]
      _ = ∑ n ∈ (m.gcd P).divisors,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
        rw [hRestrictedDivisors m hm]
      _ = if Nat.Coprime m P then 1 else 0 :=
        sum_moebius_divisors_gcd

  have hCardA :
      (A.card : ℝ) =
        ∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          ((N / n : ℕ) : ℝ) := by
    calc
      (A.card : ℝ) =
          ∑ m ∈ Finset.Ioc 0 N,
            if Nat.Coprime m P then (1 : ℝ) else 0 := by
        simp [A]
      _ = ∑ m ∈ Finset.Ioc 0 N, ∑ n ∈ S,
            if n ∣ m then
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        exact (hIndicator m hm).symm
      _ = ∑ n ∈ S, ∑ m ∈ Finset.Ioc 0 N,
            if n ∣ m then
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            ((N / n : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        calc
          (∑ m ∈ Finset.Ioc 0 N, if n ∣ m then
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0) =
              ∑ _m ∈ (Finset.Ioc 0 N).filter (fun m => n ∣ m),
                ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
            rw [Finset.sum_filter]
          _ = ((N / n : ℕ) : ℝ) *
                ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul,
              Nat.Ioc_filter_dvd_card_eq_div]
          _ = ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                ((N / n : ℕ) : ℝ) := by ring

  have hDecomposition :
      (N : ℝ) * (∑ n ∈ S,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) =
        (A.card : ℝ) +
          ∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (((N % n : ℕ) : ℝ) / (n : ℝ)) := by
    rw [Finset.mul_sum]
    calc
      (∑ n ∈ S, (N : ℝ) *
          (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ))) =
          ∑ n ∈ S,
            (((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                ((N / n : ℕ) : ℝ) +
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                (((N % n : ℕ) : ℝ) / (n : ℝ))) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnPos : 0 < n :=
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
        have hnReal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnPos.ne'
        have hQuotient :
            (N : ℝ) / (n : ℝ) =
              ((N / n : ℕ) : ℝ) +
                ((N % n : ℕ) : ℝ) / (n : ℝ) := by
          apply (div_eq_iff hnReal).2
          rw [add_mul, div_mul_cancel₀ _ hnReal]
          have hNat : N = N / n * n + N % n := by
            simpa [Nat.mul_comm] using (Nat.div_add_mod N n).symm
          exact_mod_cast hNat
        rw [show (N : ℝ) *
            (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) =
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                ((N : ℝ) / (n : ℝ)) by ring, hQuotient]
        ring
      _ = (∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              ((N / n : ℕ) : ℝ)) +
            ∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              (((N % n : ℕ) : ℝ) / (n : ℝ)) := by
        rw [Finset.sum_add_distrib]
      _ = (A.card : ℝ) +
            ∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              (((N % n : ℕ) : ℝ) / (n : ℝ)) := by
        rw [hCardA]

  have hEraseSum :
      (∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          (((N % n : ℕ) : ℝ) / (n : ℝ))) =
        ∑ n ∈ S.erase 1, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          (((N % n : ℕ) : ℝ) / (n : ℝ)) := by
    by_cases hOne : 1 ∈ S
    · rw [← Finset.sum_erase_add _ _ hOne]
      simp [Nat.mod_one]
    · rw [Finset.erase_eq_of_notMem hOne]

  have hRemainder :
      |∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          (((N % n : ℕ) : ℝ) / (n : ℝ))| ≤
        ((S.erase 1).card : ℝ) := by
    rw [hEraseSum]
    calc
      |∑ n ∈ S.erase 1, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          (((N % n : ℕ) : ℝ) / (n : ℝ))| ≤
          ∑ n ∈ S.erase 1,
            |((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              (((N % n : ℕ) : ℝ) / (n : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ S.erase 1, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnS : n ∈ S := Finset.mem_of_mem_erase hn
        have hnPos : 0 < n :=
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnS).1).1
        have hMu :
            |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
        have hRatioNonneg :
            0 ≤ ((N % n : ℕ) : ℝ) / (n : ℝ) := by positivity
        have hRatioLe :
            ((N % n : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
          apply (div_le_one (by positivity)).2
          exact_mod_cast (Nat.mod_lt N hnPos).le
        rw [abs_mul, abs_of_nonneg hRatioNonneg]
        exact (mul_le_mul hMu hRatioLe hRatioNonneg zero_le_one).trans_eq
          (mul_one 1)
      _ = ((S.erase 1).card : ℝ) := by simp

  have hDisjoint : Disjoint A (S.erase 1) := by
    rw [Finset.disjoint_left]
    intro n hnA hnErase
    have hnS : n ∈ S := Finset.mem_of_mem_erase hnErase
    have hnDivP : n ∣ P := by
      dsimp [P]
      exact Finset.dvd_prod_of_mem (fun k : ℕ => k) hnS
    have hnCoprime : Nat.Coprime n P := (Finset.mem_filter.mp hnA).2
    have hnOne : n = 1 :=
      Nat.eq_one_of_dvd_coprimes hnCoprime (dvd_refl n) hnDivP
    exact (Finset.ne_of_mem_erase hnErase) hnOne
  have hASubset : A ⊆ Finset.Ioc 0 N := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hEraseSubset : S.erase 1 ⊆ Finset.Ioc 0 N := by
    intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hn)).1
  have hCardNat : A.card + (S.erase 1).card ≤ N := by
    have hUnion := Finset.card_le_card
      (Finset.union_subset hASubset hEraseSubset)
    rw [Finset.card_union_of_disjoint hDisjoint, Nat.card_Ioc] at hUnion
    simpa using hUnion
  have hCard :
      (A.card : ℝ) + ((S.erase 1).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hCardNat

  have hScaled :
      |(N : ℝ) * (∑ n ∈ S,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ))| ≤ (N : ℝ) := by
    rw [hDecomposition]
    calc
      |(A.card : ℝ) +
          ∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (((N % n : ℕ) : ℝ) / (n : ℝ))| ≤
          |(A.card : ℝ)| +
            |∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              (((N % n : ℕ) : ℝ) / (n : ℝ))| := abs_add_le _ _
      _ = (A.card : ℝ) +
            |∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              (((N % n : ℕ) : ℝ) / (n : ℝ))| := by
        rw [abs_of_nonneg (Nat.cast_nonneg A.card)]
      _ ≤ (A.card : ℝ) + ((S.erase 1).card : ℝ) := by
        exact add_le_add le_rfl hRemainder
      _ ≤ (N : ℝ) := hCard

  have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNPos
  have hCancel :
      (N : ℝ) * |∑ n ∈ S,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
        (N : ℝ) * 1 := by
    simpa [abs_mul, abs_of_nonneg hNReal.le] using hScaled
  have hFinal := (mul_le_mul_iff_right₀ hNReal).mp hCancel
  simpa [S] using hFinal

end BoundedGaps.Maynard
