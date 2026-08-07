import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthCoefficient
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Mobius moments for the Granville--Ramare estimate

This file proves the two Mobius moments in Granville--Ramare1996, Lemma 10.3,
printed p. 42, together with its cumulative square estimate.  The contracts
and the source's corrected internal citations are reviewed in `SEM-457`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

private def squarefreeCandidateIndices (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter (fun n ↦ ¬4 ∣ n ∧ ¬9 ∣ n)

private theorem card_squarefreeCandidateIndices (N : ℕ) :
    (squarefreeCandidateIndices N).card =
      N - N / 4 - N / 9 + N / 36 := by
  let s := Finset.Ioc 0 N
  let a := s.filter (fun n ↦ 4 ∣ n)
  let na := s.filter (fun n ↦ ¬4 ∣ n)
  let b := s.filter (fun n ↦ 9 ∣ n)
  let ab := b.filter (fun n ↦ 4 ∣ n)
  let nab := na.filter (fun n ↦ 9 ∣ n)
  have hs : s.card = N := by
    simp [s, Nat.card_Ioc]
  have ha : a.card = N / 4 := by
    simpa only [a, s] using Nat.Ioc_filter_dvd_card_eq_div N 4
  have hb : b.card = N / 9 := by
    simpa only [b, s] using Nat.Ioc_filter_dvd_card_eq_div N 9
  have habFinset : ab = s.filter (fun n ↦ 36 ∣ n) := by
    ext n
    simp only [ab, b, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn, h9⟩, h4⟩
      refine ⟨hn, ?_⟩
      simpa only [show 36 = 4 * 9 by norm_num] using
        (by norm_num : Nat.Coprime 4 9).mul_dvd_of_dvd_of_dvd h4 h9
    · rintro ⟨hn, h36⟩
      exact ⟨⟨hn, (by omega : 9 ∣ 36).trans h36⟩,
        (by omega : 4 ∣ 36).trans h36⟩
  have hab : ab.card = N / 36 := by
    rw [habFinset]
    exact Nat.Ioc_filter_dvd_card_eq_div N 36
  have hsplitA : a.card + na.card = s.card := by
    simpa only [a, na] using
      (Finset.card_filter_add_card_filter_not (s := s) (fun n ↦ 4 ∣ n))
  have hsplitB : ab.card + nab.card = b.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := b) (fun n ↦ 4 ∣ n)
    have hnotEq : b.filter (fun n ↦ ¬4 ∣ n) = nab := by
      ext n
      simp only [b, nab, na, Finset.mem_filter]
      tauto
    simpa only [ab, hnotEq] using h
  have hsplitNine : nab.card + (squarefreeCandidateIndices N).card =
      na.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := na) (fun n ↦ 9 ∣ n)
    have hcandEq : na.filter (fun n ↦ ¬9 ∣ n) =
        squarefreeCandidateIndices N := by
      ext n
      simp only [na, squarefreeCandidateIndices, Finset.mem_filter]
      tauto
    simpa only [nab, hcandEq] using h
  omega

private theorem sum_sq_moebius_eq_card_squarefree (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N,
      (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2) =
      (((Finset.Ioc 0 N).filter Squarefree).card : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N, if Squarefree n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
      split_ifs <;> norm_num
    _ = _ := by simp

private theorem squarefree_subset_candidateIndices (N : ℕ) :
    (Finset.Ioc 0 N).filter Squarefree ⊆ squarefreeCandidateIndices N := by
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnIoc, hsq⟩
  rw [squarefreeCandidateIndices, Finset.mem_filter]
  refine ⟨hnIoc, ?_, ?_⟩
  · intro h4
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two)
      (by simpa using h4)
  · intro h9
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 3 Nat.prime_three)
      (by simpa using h9)

/-- The cumulative Mobius-square estimate used in Granville--Ramare1996,
Lemma 10.3. -/
theorem sum_sq_moebius_le_two_thirds (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N,
      (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2) ≤
      (2 / 3 : ℝ) * ((N : ℝ) + 2) := by
  rw [sum_sq_moebius_eq_card_squarefree]
  have hcard := Finset.card_le_card (squarefree_subset_candidateIndices N)
  have hcandidates :
      3 * (squarefreeCandidateIndices N).card ≤ 2 * (N + 2) := by
    rw [card_squarefreeCandidateIndices]
    omega
  have hcandidatesReal :
      (3 : ℝ) * ((squarefreeCandidateIndices N).card : ℝ) ≤
        2 * ((N : ℝ) + 2) := by
    exact_mod_cast hcandidates
  have hcardReal :
      (((Finset.Ioc 0 N).filter Squarefree).card : ℝ) ≤
        ((squarefreeCandidateIndices N).card : ℝ) := by
    exact_mod_cast hcard
  nlinarith

private def mobiusSquare (n : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2

private def mobiusSquarePrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, mobiusSquare n

private theorem sum_range_mobiusSquare (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), mobiusSquare n) =
      mobiusSquarePrefix N := by
  rw [← Nat.Ico_zero_eq_range, Finset.Ico_add_one_right_eq_Icc,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons]
  simp [mobiusSquare, mobiusSquarePrefix]

private theorem mobiusSquare_abel (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N, mobiusSquare n / (n : ℝ)) =
      mobiusSquarePrefix N / (N : ℝ) +
        ∑ n ∈ Finset.Ioc 0 (N - 1), mobiusSquarePrefix n *
          ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
  have h := Finset.sum_Ioc_by_parts (fun n : ℕ ↦ ((n : ℝ))⁻¹)
    mobiusSquare (show 0 < N by omega)
  simp_rw [sum_range_mobiusSquare] at h
  have hprefixZero : mobiusSquarePrefix 0 = 0 := by
    simp [mobiusSquarePrefix]
  rw [hprefixZero] at h
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N, (n : ℝ)⁻¹ * mobiusSquare n := by
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = (N : ℝ)⁻¹ * mobiusSquarePrefix N -
        ∑ n ∈ Finset.Ioc 0 (N - 1),
          (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) *
            mobiusSquarePrefix n := by
      simpa only [smul_eq_mul, mul_zero, sub_zero] using h
    _ = _ := by
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro n _hn
        ring

private theorem mobiusSquare_abel_weights (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) + 2) / (N : ℝ) +
        ∑ n ∈ Finset.Ioc 0 (N - 1), ((n : ℝ) + 2) *
          ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) =
      (harmonic N : ℝ) + 2 := by
  rcases Nat.exists_eq_add_of_le hN with ⟨k, rfl⟩
  induction k with
  | zero => norm_num [harmonic]
  | succ k ih =>
      have ih' := ih (by omega : 1 ≤ 1 + k)
      simp only [show 1 + k - 1 = k by omega] at ih'
      rw [show 1 + (k + 1) - 1 = k + 1 by omega,
        Finset.sum_Ioc_succ_top (Nat.zero_le k),
        show 1 + (k + 1) = (1 + k) + 1 by omega, harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
      calc
        _ = (((1 + k : ℕ) : ℝ) + 2) / ((1 + k : ℕ) : ℝ) +
              ∑ n ∈ Finset.Ioc 0 k, ((n : ℝ) + 2) *
                ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) +
              (((1 + k + 1 : ℕ) : ℝ))⁻¹ := by
            norm_num only [Nat.cast_add, Nat.cast_one]
            field_simp
            ring
        _ = ((harmonic (1 + k) : ℝ) + 2) +
              (((1 + k + 1 : ℕ) : ℝ))⁻¹ := by rw [ih']
        _ = _ := by ring

/-- The first Mobius moment in Granville--Ramare1996, Lemma 10.3. -/
theorem sum_sq_moebius_div_le_two_thirds
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N,
      (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2 / (n : ℝ)) ≤
      (2 / 3 : ℝ) * (Real.log (N : ℝ) + 3) := by
  change (∑ n ∈ Finset.Ioc 0 N, mobiusSquare n / (n : ℝ)) ≤ _
  rw [mobiusSquare_abel N hN]
  calc
    mobiusSquarePrefix N / (N : ℝ) +
          ∑ n ∈ Finset.Ioc 0 (N - 1), mobiusSquarePrefix n *
            ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) ≤
        (2 / 3 : ℝ) * ((N : ℝ) + 2) / (N : ℝ) +
          ∑ n ∈ Finset.Ioc 0 (N - 1),
            (2 / 3 : ℝ) * ((n : ℝ) + 2) *
              ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right
          (by simpa [mobiusSquarePrefix, mobiusSquare] using
            sum_sq_moebius_le_two_thirds N)
          (by positivity)
      · apply Finset.sum_le_sum
        intro n hn
        have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
        have hweight :
            0 ≤ (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹ := by
          apply sub_nonneg.mpr
          exact inv_anti₀ (by exact_mod_cast hnpos) (by norm_num)
        exact mul_le_mul_of_nonneg_right
          (by simpa [mobiusSquarePrefix, mobiusSquare] using
            sum_sq_moebius_le_two_thirds n)
          hweight
    _ = (2 / 3 : ℝ) *
        (((N : ℝ) + 2) / (N : ℝ) +
          ∑ n ∈ Finset.Ioc 0 (N - 1), ((n : ℝ) + 2) *
            ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹)) := by
      have hsum :
          (∑ n ∈ Finset.Ioc 0 (N - 1),
            (2 / 3 : ℝ) * ((n : ℝ) + 2) *
              ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹)) =
          (2 / 3 : ℝ) *
            ∑ n ∈ Finset.Ioc 0 (N - 1), ((n : ℝ) + 2) *
              ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      rw [hsum]
      ring
    _ = (2 / 3 : ℝ) * ((harmonic N : ℝ) + 2) := by
      rw [mobiusSquare_abel_weights N hN]
    _ ≤ (2 / 3 : ℝ) * (Real.log (N : ℝ) + 3) := by
      have hH := harmonic_le_one_add_log N
      norm_num at hH ⊢
      linarith

private theorem mobiusSquare_nonneg (n : ℕ) : 0 ≤ mobiusSquare n :=
  sq_nonneg _

private noncomputable def mobiusSquareDiv : ArithmeticFunction ℝ :=
  ⟨fun n ↦ mobiusSquare n / (n : ℝ), by simp [mobiusSquare]⟩

private theorem mobiusSquareDiv_nonneg (n : ℕ) :
    0 ≤ mobiusSquareDiv n :=
  div_nonneg (mobiusSquare_nonneg n) (Nat.cast_nonneg n)

private theorem mobiusSquare_divisorCard_div_le_convolution (n : ℕ) :
    mobiusSquare n * (n.divisors.card : ℝ) / (n : ℝ) ≤
      (mobiusSquareDiv * mobiusSquareDiv) n := by
  rw [ArithmeticFunction.mul_apply]
  rw [show
      (∑ x ∈ n.divisorsAntidiagonal,
        mobiusSquareDiv x.1 * mobiusSquareDiv x.2) =
        ∑ d ∈ n.divisors, mobiusSquareDiv d * mobiusSquareDiv (n / d) from
      Nat.sum_divisorsAntidiagonal
        (fun a b ↦ mobiusSquareDiv a * mobiusSquareDiv b)]
  by_cases hsq : Squarefree n
  · have hgn : mobiusSquare n = 1 := by
      rw [mobiusSquare, ← Int.cast_pow, ArithmeticFunction.moebius_sq,
        if_pos hsq]
      norm_num
    rw [hgn, one_mul]
    have hterm (d : ℕ) (hd : d ∈ n.divisors) :
        mobiusSquareDiv d * mobiusSquareDiv (n / d) =
          1 / (n : ℝ) := by
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hprodNat : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have hprod : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast hprodNat
      have hgd : mobiusSquare d = 1 := by
        rw [mobiusSquare, ← Int.cast_pow, ArithmeticFunction.moebius_sq,
          if_pos (hsq.squarefree_of_dvd hdvd)]
        norm_num
      have hgnd : mobiusSquare (n / d) = 1 := by
        rw [mobiusSquare, ← Int.cast_pow, ArithmeticFunction.moebius_sq,
          if_pos (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd))]
        norm_num
      rw [mobiusSquareDiv, ArithmeticFunction.coe_mk, hgd, hgnd]
      norm_num only [one_div]
      rw [← mul_inv, hprod]
    calc
      (n.divisors.card : ℝ) / (n : ℝ) =
          ∑ _d ∈ n.divisors, 1 / (n : ℝ) := by
        simp [div_eq_mul_inv]
      _ = ∑ d ∈ n.divisors,
          mobiusSquareDiv d * mobiusSquareDiv (n / d) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact (hterm d hd).symm
      _ ≤ _ := le_rfl
  · have hgn : mobiusSquare n = 0 := by
      rw [mobiusSquare, ← Int.cast_pow, ArithmeticFunction.moebius_sq,
        if_neg hsq]
      norm_num
    rw [hgn, zero_mul, zero_div]
    exact Finset.sum_nonneg fun d _hd ↦
      mul_nonneg (mobiusSquareDiv_nonneg d)
        (mobiusSquareDiv_nonneg (n / d))

/-- The divisor-weighted Mobius moment in Granville--Ramare1996,
Lemma 10.3. -/
theorem sum_sq_moebius_mul_card_divisors_div_le_four_ninths
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N,
      (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2 *
        (n.divisors.card : ℝ) / (n : ℝ)) ≤
      (4 / 9 : ℝ) * (Real.log (N : ℝ) + 3) ^ 2 := by
  let s := Finset.Ioc 0 N
  let box := s ×ˢ s
  let pairs := box.filter (fun x : ℕ × ℕ ↦ x.1 * x.2 ≤ N)
  have hpairsSubset : pairs ⊆ box := Finset.filter_subset _ _
  have hdrop :
      (∑ x ∈ pairs, mobiusSquareDiv x.1 * mobiusSquareDiv x.2) ≤
        ∑ x ∈ box, mobiusSquareDiv x.1 * mobiusSquareDiv x.2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hpairsSubset
    intro x _hx _hnot
    exact mul_nonneg (mobiusSquareDiv_nonneg x.1)
      (mobiusSquareDiv_nonneg x.2)
  have hfirst := sum_sq_moebius_div_le_two_thirds hN
  have hsumNonneg : 0 ≤ ∑ n ∈ s, mobiusSquareDiv n := by
    exact Finset.sum_nonneg fun n _hn ↦ mobiusSquareDiv_nonneg n
  have hrightNonneg :
      0 ≤ (2 / 3 : ℝ) * (Real.log (N : ℝ) + 3) := by
    have hlog : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hN)
    positivity
  calc
    (∑ n ∈ Finset.Ioc 0 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2 *
          (n.divisors.card : ℝ) / (n : ℝ)) ≤
        ∑ n ∈ Finset.Ioc 0 N,
          (mobiusSquareDiv * mobiusSquareDiv) n := by
      apply Finset.sum_le_sum
      intro n _hn
      simpa only [mobiusSquare] using
        mobiusSquare_divisorCard_div_le_convolution n
    _ = ∑ x ∈ pairs,
        mobiusSquareDiv x.1 * mobiusSquareDiv x.2 := by
      simpa only [s, box, pairs] using
        ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter
          mobiusSquareDiv mobiusSquareDiv N
    _ ≤ ∑ x ∈ box,
        mobiusSquareDiv x.1 * mobiusSquareDiv x.2 := hdrop
    _ = ∑ a ∈ s, ∑ b ∈ s, mobiusSquareDiv a * mobiusSquareDiv b :=
      Finset.sum_product' s s
        (fun a b ↦ mobiusSquareDiv a * mobiusSquareDiv b)
    _ = (∑ n ∈ s, mobiusSquareDiv n) ^ 2 := by
      rw [← Finset.sum_mul_sum]
      ring
    _ ≤ ((2 / 3 : ℝ) * (Real.log (N : ℝ) + 3)) ^ 2 := by
      apply (sq_le_sq₀ hsumNonneg hrightNonneg).2
      simpa only [s, mobiusSquareDiv, ArithmeticFunction.coe_mk,
        mobiusSquare] using hfirst
    _ = (4 / 9 : ℝ) * (Real.log (N : ℝ) + 3) ^ 2 := by ring

end BoundedGaps.Maynard
