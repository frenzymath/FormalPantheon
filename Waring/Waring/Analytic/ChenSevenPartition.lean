import Waring.Analytic.ChenSevenBlock
import Waring.Analytic.ChenSevenNumerics

/-!
# Interval partitions in Chen's Lemma 7

This file assembles the rational-block and bounded-variation estimates over
the large and middle denominator ranges of Chen's Lemma 7.  The middle range
uses blocks of `L = (q + 1) / 2` terms; their `L - 1` phase increments satisfy
the exact half-denominator condition [CHEN1964-EN, pp. 1551-1552;
CHEN1964-ZH, pp. 718-719].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- A range whose every nonempty block of at most `L` terms has norm at most
`C` has norm at most `(P / L + 1) * C`.  The extra one avoids a separate
divisibility case for the final block. -/
theorem norm_sum_range_le_natDiv_add_one_mul
    {E : Type*} [SeminormedAddCommGroup E] (f : Nat → E)
    (P L : Nat) (C : Real) (hL : 0 < L) (hC : 0 ≤ C)
    (hblock : ∀ M n, 0 < n → M + n ≤ P → n ≤ L →
      ‖∑ i ∈ Finset.range n, f (M + i)‖ ≤ C) :
    ‖∑ i ∈ Finset.range P, f i‖ ≤
      (((P / L : Nat) : Real) + 1) * C := by
  induction P using Nat.strong_induction_on generalizing f with
  | h P ih =>
      by_cases hP0 : P = 0
      · subst P
        simp only [Finset.range_zero, Finset.sum_empty, norm_zero,
          Nat.zero_div, Nat.cast_zero, zero_add, one_mul]
        exact hC
      have hP : 0 < P := Nat.pos_of_ne_zero hP0
      by_cases hPL : P ≤ L
      · have hOne : (1 : Real) ≤ ((P / L : Nat) : Real) + 1 := by
          have : (0 : Real) ≤ ((P / L : Nat) : Real) := by positivity
          linarith
        calc
          ‖∑ i ∈ Finset.range P, f i‖ =
              ‖∑ i ∈ Finset.range P, f (0 + i)‖ := by simp
          _ ≤ C := hblock 0 P hP (by simp) hPL
          _ = 1 * C := by ring
          _ ≤ (((P / L : Nat) : Real) + 1) * C :=
            mul_le_mul_of_nonneg_right hOne hC
      · have hLP : L ≤ P := (Nat.lt_of_not_ge hPL).le
        have hSub : P - L < P := Nat.sub_lt hP hL
        have hFirst : ‖∑ i ∈ Finset.range L, f i‖ ≤ C := by
          simpa using hblock 0 L hL (by simpa using hLP) le_rfl
        have hTail :
            ‖∑ i ∈ Finset.range (P - L), f (L + i)‖ ≤
              ((((P - L) / L : Nat) : Real) + 1) * C := by
          apply ih (P - L) hSub (fun i ↦ f (L + i))
          intro M n hn hMn hnL
          have hEndpoint : L + M + n ≤ P := by omega
          simpa only [add_assoc] using
            hblock (L + M) n hn hEndpoint hnL
        have hDiv : P / L = (P - L) / L + 1 :=
          Nat.div_eq_sub_div hL hLP
        have hSplit : P = L + (P - L) := by omega
        have hSumSplit :
            (∑ i ∈ Finset.range P, f i) =
              (∑ i ∈ Finset.range L, f i) +
                ∑ i ∈ Finset.range (P - L), f (L + i) := by
          calc
            (∑ i ∈ Finset.range P, f i) =
                ∑ i ∈ Finset.range (L + (P - L)), f i := by
              rw [← hSplit]
            _ = (∑ i ∈ Finset.range L, f i) +
                ∑ i ∈ Finset.range (P - L), f (L + i) :=
              Finset.sum_range_add f L (P - L)
        calc
          ‖∑ i ∈ Finset.range P, f i‖ =
              ‖(∑ i ∈ Finset.range L, f i) +
                ∑ i ∈ Finset.range (P - L), f (L + i)‖ := by
            rw [hSumSplit]
          _ ≤ ‖∑ i ∈ Finset.range L, f i‖ +
                ‖∑ i ∈ Finset.range (P - L), f (L + i)‖ :=
            norm_add_le _ _
          _ ≤ C + ((((P - L) / L : Nat) : Real) + 1) * C :=
            add_le_add hFirst hTail
          _ = (((P / L : Nat) : Real) + 1) * C := by
            rw [hDiv]
            push_cast
            ring

/-- Blocks of `ceil(q/2)` terms require no more than Chen's real-valued count
`2*P/q+1`. -/
theorem natDiv_ceilHalf_add_one_cast_le
    (P q : Nat) (hq : 0 < q) :
    (((P / ((q + 1) / 2) : Nat) : Real) + 1) ≤
      2 * (P : Real) / q + 1 := by
  have hL : 0 < (q + 1) / 2 := by omega
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hLReal : (0 : Real) < ((q + 1) / 2 : Nat) := by
    exact_mod_cast hL
  have hqL : q ≤ 2 * ((q + 1) / 2) := by omega
  have hqLReal : (q : Real) ≤ 2 * (((q + 1) / 2 : Nat) : Real) := by
    exact_mod_cast hqL
  have hNatDiv : ((P / ((q + 1) / 2) : Nat) : Real) ≤
      (P : Real) / ((q + 1) / 2 : Nat) := Nat.cast_div_le
  have hRealDiv : (P : Real) / ((q + 1) / 2 : Nat) ≤
      2 * (P : Real) / q := by
    apply (div_le_div_iff₀ hLReal hqReal).2
    nlinarith [show (0 : Real) ≤ P by positivity]
  linarith

/-- If `P ≤ 2q`, every rational partial sum on `1,...,P` is the sum of at
most two blocks to which Chen's completion lemma applies. -/
theorem norm_partialSum_rationalFifthBlock_one_le_two_mul_log
    (q : Nat) [NeZero q] (a : ZMod q) (P : Nat) (B : Real)
    (hPq : P ≤ 2 * q)
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum a 0 0 0 h‖ ≤ B) :
    ∀ k, k ≤ P →
      ‖∑ i ∈ Finset.range k, rationalFifthBlock a 1 i‖ ≤
        2 * (Real.log q + 1) * B := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqOne : (1 : Real) ≤ q := by exact_mod_cast hq
  have hB : 0 ≤ B :=
    (norm_nonneg (polynomialCompleteSum a 0 0 0 0)).trans (hcomplete 0)
  have hD : 0 ≤ (Real.log q + 1) * B :=
    mul_nonneg (add_nonneg (Real.log_nonneg hqOne) (by norm_num)) hB
  intro k hkP
  by_cases hkq : k ≤ q
  · calc
      ‖∑ i ∈ Finset.range k, rationalFifthBlock a 1 i‖ ≤
          (Real.log q + 1) * B :=
        norm_sum_range_rationalFifthBlock_le_log_of_complete_bound
          q a 1 k B hkq hcomplete
      _ ≤ 2 * ((Real.log q + 1) * B) := by linarith
      _ = 2 * (Real.log q + 1) * B := by ring
  · have hqk : q ≤ k := (Nat.lt_of_not_ge hkq).le
    have hkTail : k - q ≤ q := by omega
    have hkSplit : k = q + (k - q) := by omega
    have hFirst :
        ‖∑ i ∈ Finset.range q, rationalFifthBlock a 1 i‖ ≤
          (Real.log q + 1) * B :=
      norm_sum_range_rationalFifthBlock_le_log_of_complete_bound
        q a 1 q B le_rfl hcomplete
    have hSecond :
        ‖∑ i ∈ Finset.range (k - q),
            rationalFifthBlock a (q + 1) i‖ ≤
          (Real.log q + 1) * B :=
      norm_sum_range_rationalFifthBlock_le_log_of_complete_bound
        q a (q + 1) (k - q) B hkTail hcomplete
    have hSumSplit :
        (∑ i ∈ Finset.range k, rationalFifthBlock a 1 i) =
          (∑ i ∈ Finset.range q, rationalFifthBlock a 1 i) +
            ∑ i ∈ Finset.range (k - q),
              rationalFifthBlock a (q + 1) i := by
      calc
        (∑ i ∈ Finset.range k, rationalFifthBlock a 1 i) =
            ∑ i ∈ Finset.range (q + (k - q)),
              rationalFifthBlock a 1 i := by rw [← hkSplit]
        _ = (∑ i ∈ Finset.range q, rationalFifthBlock a 1 i) +
            ∑ i ∈ Finset.range (k - q),
              rationalFifthBlock a 1 (q + i) :=
          Finset.sum_range_add (rationalFifthBlock a 1) q (k - q)
        _ = (∑ i ∈ Finset.range q, rationalFifthBlock a 1 i) +
            ∑ i ∈ Finset.range (k - q),
              rationalFifthBlock a (q + 1) i := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have hi : 1 + (q + i) = q + 1 + i := by omega
          unfold rationalFifthBlock
          rw [hi]
    rw [hSumSplit]
    calc
      ‖(∑ i ∈ Finset.range q, rationalFifthBlock a 1 i) +
          ∑ i ∈ Finset.range (k - q),
            rationalFifthBlock a (q + 1) i‖ ≤
          ‖∑ i ∈ Finset.range q, rationalFifthBlock a 1 i‖ +
            ‖∑ i ∈ Finset.range (k - q),
              rationalFifthBlock a (q + 1) i‖ := norm_add_le _ _
      _ ≤ (Real.log q + 1) * B + (Real.log q + 1) * B :=
        add_le_add hFirst hSecond
      _ = 2 * (Real.log q + 1) * B := by ring

/-- The analytic large-denominator assembly: two completed rational pieces
and one full-interval Abel estimate cost the factor `8`. -/
theorem norm_perturbedRationalFifthBlock_one_le_large
    (q : Nat) [NeZero q] (a : ZMod q) (z : Real)
    (P : Nat) (B : Real) (hP : 0 < P) (hPq : P ≤ 2 * q)
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum a 0 0 0 h‖ ≤ B) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
          rationalFifthBlock a 1 i‖ ≤
      8 * (Real.log q + 1) * B := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hpartial := norm_partialSum_rationalFifthBlock_one_le_two_mul_log
    q a P B hPq hcomplete
  have hphase := sum_abs_fifthPerturbationPhase_sub_le_three_of_full
    z P q hP hq hPq hz
  calc
    ‖∑ i ∈ Finset.range P,
        Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
          rationalFifthBlock a 1 i‖ ≤
        4 * (2 * (Real.log q + 1) * B) :=
      norm_sum_range_exp_I_mul_le_four_of_phase_variation
        (fifthPerturbationPhase z 1) (rationalFifthBlock a 1) P
          (2 * (Real.log q + 1) * B) hpartial hphase
    _ = 8 * (Real.log q + 1) * B := by ring

/-- Source-exponential form of the large-denominator assembly for a natural
numerator. -/
theorem norm_sum_range_exp_fifth_rational_add_perturbation_large_le
    (q : Nat) [NeZero q] (a : Nat) (z : Real)
    (P : Nat) (B : Real) (hP : 0 < P) (hPq : P ≤ 2 * q)
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum (a : ZMod q) 0 0 0 h‖ ≤ B) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
      8 * (Real.log q + 1) * B := by
  have hsum :
      (∑ i ∈ Finset.range P,
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))) =
        ∑ i ∈ Finset.range P,
          Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
            rationalFifthBlock (a : ZMod q) 1 i := by
    apply Finset.sum_congr rfl
    intro i _
    exact
      (exp_fifthPerturbationPhase_mul_rationalFifthBlock_natCast
        q a 1 i z).symm
  rw [hsum]
  exact norm_perturbedRationalFifthBlock_one_le_large
    q (a : ZMod q) z P B hP hPq hz hcomplete

/-- Large-denominator conclusion after inserting the conditional complete-sum
bound and the verified numerical absorption. -/
theorem chenSeven_largeDenominator_bound
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hPThreshold : (10 : Real) ^ 150 ≤ P)
    (hPq : P ≤ 2 * q)
    (hqUpper : (q : Real) ≤ (P : Real) ^ (26 / 25 : Real))
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum (a : ZMod q) 0 0 0 h‖ ≤
        10 ^ 15 * (q : Real) ^ (4 / 5 : Real)) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
      (P : Real) ^ (24 / 25 : Real) := by
  have hPReal : (0 : Real) < P :=
    (by positivity : (0 : Real) < 10 ^ 150).trans_le hPThreshold
  have hP : 0 < P := by exact_mod_cast hPReal
  have hqOne : (1 : Real) ≤ q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  calc
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
        8 * (Real.log q + 1) *
          (10 ^ 15 * (q : Real) ^ (4 / 5 : Real)) :=
      norm_sum_range_exp_fifth_rational_add_perturbation_large_le
        q a z P (10 ^ 15 * (q : Real) ^ (4 / 5 : Real))
          hP hPq hz hcomplete
    _ = 8 * 10 ^ 15 * (Real.log q + 1) *
        (q : Real) ^ (4 / 5 : Real) := by ring
    _ ≤ (P : Real) ^ (24 / 25 : Real) :=
      chenSeven_largeDenominator_numerical hPThreshold hqOne hqUpper

/-- The analytic middle-denominator assembly over ceiling-half blocks. -/
theorem norm_perturbedRationalFifthBlock_one_le_middle
    (q : Nat) [NeZero q] (a : ZMod q) (z : Real)
    (P : Nat) (B : Real) (hP : 0 < P)
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum a 0 0 0 h‖ ≤ B) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
          rationalFifthBlock a 1 i‖ ≤
      (2 * (P : Real) / q + 1) * 4 * (Real.log q + 1) * B := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqOne : (1 : Real) ≤ q := by exact_mod_cast hq
  have hL : 0 < (q + 1) / 2 := by omega
  have hB : 0 ≤ B :=
    (norm_nonneg (polynomialCompleteSum a 0 0 0 0)).trans (hcomplete 0)
  have hC : 0 ≤ 4 * (Real.log q + 1) * B := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (add_nonneg (Real.log_nonneg hqOne) (by norm_num))) hB
  have hPartition := norm_sum_range_le_natDiv_add_one_mul
    (fun i ↦
      Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
        rationalFifthBlock a 1 i)
    P ((q + 1) / 2) (4 * (Real.log q + 1) * B) hL hC
  have hPartitionBound :
      ‖∑ i ∈ Finset.range P,
          Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
            rationalFifthBlock a 1 i‖ ≤
        ((((P / ((q + 1) / 2) : Nat) : Real) + 1) *
          (4 * (Real.log q + 1) * B)) := by
    apply hPartition
    intro M n hn hMn hnL
    have hEndpoint : M + 1 + n ≤ P + 1 := by omega
    have hhalf : 2 * (n - 1) ≤ q := by omega
    have hblock := norm_perturbedRationalFifthBlock_le
      q a z (M + 1) n P B hn hP hEndpoint hhalf hz hcomplete
    have hsum :
        (∑ i ∈ Finset.range n,
            Complex.exp
                (Complex.I * fifthPerturbationPhase z 1 (M + i)) *
              rationalFifthBlock a 1 (M + i)) =
          ∑ i ∈ Finset.range n,
            Complex.exp
                (Complex.I * fifthPerturbationPhase z (M + 1) i) *
              rationalFifthBlock a (M + 1) i := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : 1 + (M + i) = M + 1 + i := by omega
      unfold fifthPerturbationPhase rationalFifthBlock
      rw [hi]
    rw [hsum]
    exact hblock
  have hCount := natDiv_ceilHalf_add_one_cast_le P q hq
  calc
    ‖∑ i ∈ Finset.range P,
        Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
          rationalFifthBlock a 1 i‖ ≤
        (((P / ((q + 1) / 2) : Nat) : Real) + 1) *
          (4 * (Real.log q + 1) * B) := hPartitionBound
    _ ≤ (2 * (P : Real) / q + 1) *
        (4 * (Real.log q + 1) * B) :=
      mul_le_mul_of_nonneg_right hCount hC
    _ = (2 * (P : Real) / q + 1) * 4 * (Real.log q + 1) * B := by
      ring

/-- Source-exponential form of the middle-denominator partition assembly. -/
theorem norm_sum_range_exp_fifth_rational_add_perturbation_middle_le
    (q : Nat) [NeZero q] (a : Nat) (z : Real)
    (P : Nat) (B : Real) (hP : 0 < P)
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum (a : ZMod q) 0 0 0 h‖ ≤ B) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
      (2 * (P : Real) / q + 1) * 4 * (Real.log q + 1) * B := by
  have hsum :
      (∑ i ∈ Finset.range P,
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))) =
        ∑ i ∈ Finset.range P,
          Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
            rationalFifthBlock (a : ZMod q) 1 i := by
    apply Finset.sum_congr rfl
    intro i _
    exact
      (exp_fifthPerturbationPhase_mul_rationalFifthBlock_natCast
        q a 1 i z).symm
  rw [hsum]
  exact norm_perturbedRationalFifthBlock_one_le_middle
    q (a : ZMod q) z P B hP hz hcomplete

/-- Middle-denominator conclusion after inserting the conditional
complete-sum bound and the verified numerical absorption. -/
theorem chenSeven_middleDenominator_bound
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hPThreshold : (10 : Real) ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (19 / 20 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ P)
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum (a : ZMod q) 0 0 0 h‖ ≤
        10 ^ 15 * (q : Real) ^ (4 / 5 : Real)) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
      (P : Real) ^ (24 / 25 : Real) := by
  have hPReal : (0 : Real) < P :=
    (by positivity : (0 : Real) < 10 ^ 150).trans_le hPThreshold
  have hP : 0 < P := by exact_mod_cast hPReal
  have hqOne : (1 : Real) ≤ q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  calc
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
        (2 * (P : Real) / q + 1) * 4 * (Real.log q + 1) *
          (10 ^ 15 * (q : Real) ^ (4 / 5 : Real)) :=
      norm_sum_range_exp_fifth_rational_add_perturbation_middle_le
        q a z P (10 ^ 15 * (q : Real) ^ (4 / 5 : Real))
          hP hz hcomplete
    _ = (2 * (P : Real) / q + 1) * 4 * 10 ^ 15 *
        (Real.log q + 1) * (q : Real) ^ (4 / 5 : Real) := by ring
    _ ≤ (P : Real) ^ (24 / 25 : Real) :=
      chenSeven_middleDenominator_numerical
        hPThreshold hqOne hqLower hqUpper

end Waring.Analytic
