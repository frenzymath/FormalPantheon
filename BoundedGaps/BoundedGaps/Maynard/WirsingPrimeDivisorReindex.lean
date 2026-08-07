import BoundedGaps.Maynard.MaynardPrimeDivisorMean

noncomputable section

/-!
# Wirsing prime-divisor reindex

The reciprocal-totient mass of squarefree multiples of a new prime is
reindexed exactly by division by that prime. This is the finite
prime-divisor step below GGPY2009, Lemma `L:Wirsing`, source lines 803--842.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

set_option maxRecDepth 3000 in
theorem squarefreeCoprimePrimeDivisorMean_eq
    {W Q p : ℕ} (hp : p.Prime) (hpW : ¬p ∣ W) :
    (∑ n ∈ squarefreeCoprimePrimeDivisorSupport W Q p,
        (1 : ℝ) / Nat.totient n) =
      (1 : ℝ) / Nat.totient p *
        squarefreeCoprimeInvTotientMean (W * p) (Q / p) := by
  classical
  let S := squarefreeCoprimePrimeDivisorSupport W Q p
  let T := (Finset.Icc 1 (Q / p)).filter fun m =>
    Squarefree m ∧ Nat.Coprime m (W * p)
  have hpWcop : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpW
  have hreindex :
      (∑ n ∈ S, (1 : ℝ) / Nat.totient n) =
        (1 : ℝ) / Nat.totient p *
          ∑ m ∈ T, (1 : ℝ) / Nat.totient m := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij'
      (fun n _ => n / p) (fun m _ => p * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnBounds := Finset.mem_Icc.mp hnData.1
      have hnPos : 0 < n := zero_lt_one.trans_le hnBounds.1
      have hpdvd : p ∣ n := hnData.2.2.2
      have hmPos : 0 < n / p :=
        Nat.div_pos (Nat.le_of_dvd hnPos hpdvd) hp.pos
      have hmDvd : n / p ∣ n := Nat.div_dvd_of_dvd hpdvd
      have hmSquarefree : Squarefree (n / p) :=
        hnData.2.1.squarefree_of_dvd hmDvd
      have hmW : Nat.Coprime (n / p) W :=
        Nat.Coprime.of_dvd_left hmDvd hnData.2.2.1
      have hprod : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
      have hpm : Nat.Coprime p (n / p) := by
        apply Nat.coprime_of_squarefree_mul
        simpa [hprod] using hnData.2.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hmPos, Nat.div_le_div_right hnBounds.2⟩,
        hmSquarefree, ?_⟩
      exact Nat.coprime_mul_iff_right.mpr ⟨hmW, hpm.symm⟩
    · intro m hm
      have hmData := Finset.mem_filter.mp hm
      have hmBounds := Finset.mem_Icc.mp hmData.1
      have hmCoprime := Nat.coprime_mul_iff_right.mp hmData.2.2
      have hpm : Nat.Coprime p m := hmCoprime.2.symm
      have hmulSquarefree : Squarefree (p * m) :=
        (Nat.squarefree_mul hpm).mpr ⟨hp.squarefree, hmData.2.1⟩
      have hmulLe : p * m ≤ Q := by
        have h := (Nat.le_div_iff_mul_le hp.pos).mp hmBounds.2
        simpa [Nat.mul_comm] using h
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr
          ⟨Nat.mul_pos hp.pos (zero_lt_one.trans_le hmBounds.1), hmulLe⟩,
        hmulSquarefree, hpWcop.mul_left hmCoprime.1, Nat.dvd_mul_right p m⟩
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      exact Nat.mul_div_cancel' hnData.2.2.2
    · intro m hm
      exact Nat.mul_div_cancel_left m hp.pos
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hpdvd : p ∣ n := hnData.2.2.2
      have hprod : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
      have hpm : Nat.Coprime p (n / p) := by
        apply Nat.coprime_of_squarefree_mul
        simpa [hprod] using hnData.2.1
      rw [← hprod, Nat.totient_mul hpm]
      push_cast
      rw [Nat.mul_div_cancel_left (n / p) hp.pos]
      ring
  rw [show squarefreeCoprimePrimeDivisorSupport W Q p = S by rfl,
    hreindex]
  unfold squarefreeCoprimeInvTotientMean
  dsimp [T]
  rw [Finset.sum_filter]

private theorem log_eq_sum_primeFactors_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log p := by
  calc
    Real.log n = Real.log (∏ p ∈ n.primeFactors, (p : ℝ)) := by
      congr 1
      rw [← Nat.cast_prod]
      exact_mod_cast (Nat.prod_primeFactors_of_squarefree hn).symm
    _ = ∑ p ∈ n.primeFactors, Real.log p := by
      rw [Real.log_prod]
      intro p hpMem
      exact_mod_cast (Nat.prime_of_mem_primeFactors hpMem).ne_zero

noncomputable def squarefreeCoprimeInvTotientLogMean
    (W Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Q).filter fun n =>
      Squarefree n ∧ Nat.Coprime n W,
    Real.log n / Nat.totient n

set_option maxRecDepth 4000 in
theorem squarefreeCoprimeInvTotientLogMean_eq_prime_sum
    (W Q : ℕ) :
    squarefreeCoprimeInvTotientLogMean W Q =
      ∑ p ∈ Q.primesLE.filter (fun p => ¬p ∣ W),
        (Real.log p / Nat.totient p) *
          squarefreeCoprimeInvTotientMean (W * p) (Q / p) := by
  classical
  let S := (Finset.Icc 1 Q).filter fun n =>
    Squarefree n ∧ Nat.Coprime n W
  let P := Q.primesLE.filter fun p => ¬p ∣ W
  have hfactor : ∀ n ∈ S,
      P.filter (fun p => p ∣ n) = n.primeFactors := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnBounds := Finset.mem_Icc.mp hnData.1
    have hnPos : 0 < n := zero_lt_one.trans_le hnBounds.1
    ext p
    simp only [P, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpLE, hpW⟩, hpn⟩
      exact Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primesLE hpLE, hpn, hnPos.ne'⟩
    · intro hpMem
      have hp := Nat.prime_of_mem_primeFactors hpMem
      have hpn := Nat.dvd_of_mem_primeFactors hpMem
      have hpLeN := Nat.le_of_dvd hnPos hpn
      have hpCopW := Nat.Coprime.of_dvd_left hpn hnData.2.2
      exact ⟨⟨Nat.mem_primesLE.mpr ⟨hpLeN.trans hnBounds.2, hp⟩,
        hp.coprime_iff_not_dvd.mp hpCopW⟩, hpn⟩
  have hpoint : ∀ n ∈ S,
      Real.log n / Nat.totient n =
        ∑ p ∈ P.filter (fun p => p ∣ n),
          Real.log p / Nat.totient n := by
    intro n hn
    have hnSquarefree := (Finset.mem_filter.mp hn).2.1
    rw [hfactor n hn, ← Finset.sum_div,
      ← log_eq_sum_primeFactors_of_squarefree hnSquarefree]
  have hswap :
      (∑ n ∈ S, ∑ p ∈ P.filter (fun p => p ∣ n),
          Real.log p / Nat.totient n) =
        ∑ p ∈ P, ∑ n ∈ S.filter (fun n => p ∣ n),
          Real.log p / Nat.totient n := by
    calc
      (∑ n ∈ S, ∑ p ∈ P.filter (fun p => p ∣ n),
          Real.log p / Nat.totient n) =
          ∑ n ∈ S, ∑ p ∈ P,
            if p ∣ n then Real.log p / Nat.totient n else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_filter]
      _ = ∑ p ∈ P, ∑ n ∈ S,
          if p ∣ n then Real.log p / Nat.totient n else 0 := by
        exact Finset.sum_comm
      _ = ∑ p ∈ P, ∑ n ∈ S.filter (fun n => p ∣ n),
          Real.log p / Nat.totient n := by
        apply Finset.sum_congr rfl
        intro p hpMem
        exact (Finset.sum_filter (s := S) (p := fun n => p ∣ n)
          (f := fun n => Real.log p / Nat.totient n)).symm
  unfold squarefreeCoprimeInvTotientLogMean
  rw [show (Finset.Icc 1 Q).filter
      (fun n => Squarefree n ∧ Nat.Coprime n W) = S by rfl]
  calc
    (∑ n ∈ S, Real.log n / Nat.totient n) =
        ∑ n ∈ S, ∑ p ∈ P.filter (fun p => p ∣ n),
          Real.log p / Nat.totient n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n hn
    _ = ∑ p ∈ P, ∑ n ∈ S.filter (fun n => p ∣ n),
        Real.log p / Nat.totient n := hswap
    _ = ∑ p ∈ P,
        (Real.log p / Nat.totient p) *
          squarefreeCoprimeInvTotientMean (W * p) (Q / p) := by
      apply Finset.sum_congr rfl
      intro p hpMem
      have hpData := Finset.mem_filter.mp hpMem
      have hp := Nat.prime_of_mem_primesLE hpData.1
      have hsupport : S.filter (fun n => p ∣ n) =
          squarefreeCoprimePrimeDivisorSupport W Q p := by
        ext n
        simp [S, squarefreeCoprimePrimeDivisorSupport, and_assoc]
      rw [hsupport]
      calc
        (∑ n ∈ squarefreeCoprimePrimeDivisorSupport W Q p,
            Real.log p / Nat.totient n) =
            Real.log p *
              ∑ n ∈ squarefreeCoprimePrimeDivisorSupport W Q p,
                (1 : ℝ) / Nat.totient n := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = Real.log p *
            ((1 : ℝ) / Nat.totient p *
              squarefreeCoprimeInvTotientMean (W * p) (Q / p)) := by
          rw [squarefreeCoprimePrimeDivisorMean_eq hp hpData.2]
        _ = (Real.log p / Nat.totient p) *
            squarefreeCoprimeInvTotientMean (W * p) (Q / p) := by ring
    _ = ∑ p ∈ Q.primesLE.filter (fun p => ¬p ∣ W),
        (Real.log p / Nat.totient p) *
          squarefreeCoprimeInvTotientMean (W * p) (Q / p) := by rfl

set_option maxRecDepth 3500 in
theorem squarefreeCoprimeInvTotientMean_mul_prime
    {W Q p : ℕ} (hp : p.Prime) (hpW : Nat.Coprime p W) :
    squarefreeCoprimeInvTotientMean (W * p) Q =
      squarefreeCoprimeInvTotientMean W Q -
        (1 : ℝ) / Nat.totient p *
          squarefreeCoprimeInvTotientMean (W * p) (Q / p) := by
  classical
  let S := (Finset.Icc 1 Q).filter fun n =>
    Squarefree n ∧ Nat.Coprime n W
  let T := S.filter (fun n => Nat.Coprime n p)
  have hleft :
      (Finset.Icc 1 Q).filter (fun n =>
          Squarefree n ∧ Nat.Coprime n (W * p)) = T := by
    ext n
    simp only [T, S, Finset.mem_filter, Nat.coprime_mul_iff_right]
    tauto
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (Nat.Coprime · p)
    (fun n => (1 : ℝ) / Nat.totient n)
  have hbad :
      (∑ n ∈ S.filter (fun n => ¬Nat.Coprime n p),
          (1 : ℝ) / Nat.totient n) =
        (1 : ℝ) / Nat.totient p *
          squarefreeCoprimeInvTotientMean (W * p) (Q / p) := by
    have hnotcop : ∀ n : ℕ, (¬Nat.Coprime n p) ↔ p ∣ n := by
      intro n
      constructor
      · intro h
        by_contra hnot
        exact h (hp.coprime_iff_not_dvd.mpr hnot).symm
      · intro hpdvd hcop
        exact (hp.coprime_iff_not_dvd.mp hcop.symm) hpdvd
    have hsupport : S.filter (fun n => ¬Nat.Coprime n p) =
        squarefreeCoprimePrimeDivisorSupport W Q p := by
      ext n
      simp [S, squarefreeCoprimePrimeDivisorSupport, hnotcop, and_assoc]
    rw [hsupport]
    exact
      squarefreeCoprimePrimeDivisorMean_eq hp
        (hp.coprime_iff_not_dvd.mp hpW)
  have hmeanLeft :
      squarefreeCoprimeInvTotientMean (W * p) Q =
        ∑ n ∈ (Finset.Icc 1 Q).filter (fun n =>
          Squarefree n ∧ Nat.Coprime n (W * p)),
          (1 : ℝ) / Nat.totient n := by
    unfold squarefreeCoprimeInvTotientMean
    rw [Finset.sum_filter]
  have hmeanS :
      squarefreeCoprimeInvTotientMean W Q =
        ∑ n ∈ S, (1 : ℝ) / Nat.totient n := by
    unfold squarefreeCoprimeInvTotientMean
    rw [show S = (Finset.Icc 1 Q).filter (fun n =>
      Squarefree n ∧ Nat.Coprime n W) by rfl, Finset.sum_filter]
  rw [hmeanLeft, hleft, hmeanS]
  rw [← hbad]
  change _ = (∑ n ∈ S, (1 : ℝ) / Nat.totient n) -
    ∑ n ∈ S.filter (fun n => ¬Nat.Coprime n p),
      (1 : ℝ) / Nat.totient n
  linarith

end BoundedGaps.Maynard
