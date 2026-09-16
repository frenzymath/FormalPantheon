import Waring.Analytic.DivisorMoments
import Waring.Analytic.LogMomentBounds

/-!
# Chen's second divisor moment

This file formalizes the finite double count and common-divisor overcount in
equation (11) of Chen's English Lemma 8 [CHEN1964-EN, p. 1553].
-/

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

private lemma divisorCount_eq_sum_indicator_Icc {n i : Nat}
    (hi : i ∈ Finset.Icc 1 n) :
    divisorCount i = ∑ d ∈ Finset.Icc 1 n, if d ∣ i then 1 else 0 := by
  simp only [Finset.mem_Icc] at hi
  have hi0 : i ≠ 0 := by omega
  have hset : {d ∈ Finset.Icc 1 n | d ∣ i} = i.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, _⟩, hdi⟩
      exact ⟨hdi, hi0⟩
    · rintro ⟨hdi, _⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdi (by omega)
      have hdle : d ≤ i := Nat.le_of_dvd (by omega) hdi
      exact ⟨⟨hdpos, hdle.trans hi.2⟩, hdi⟩
  rw [divisorCount]
  calc
    i.divisors.card = {d ∈ Finset.Icc 1 n | d ∣ i}.card := by rw [hset]
    _ = ∑ d ∈ Finset.Icc 1 n, if d ∣ i then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma common_multiple_indicator_sum (n a b : Nat) :
    (∑ i ∈ Finset.Icc 1 n, if a ∣ i ∧ b ∣ i then 1 else 0) =
      n / a.lcm b := by
  calc
    (∑ i ∈ Finset.Icc 1 n, if a ∣ i ∧ b ∣ i then 1 else 0) =
        {i ∈ Finset.Icc 1 n | a.lcm b ∣ i}.card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Nat.lcm_dvd_iff]
    _ = {i ∈ Finset.Ioc 0 n | a.lcm b ∣ i}.card := by
      congr 1
    _ = n / a.lcm b := Nat.Ioc_filter_dvd_card_eq_div n (a.lcm b)

/-- Ordered pairs of divisors, summed over positive `i ≤ n`, are counted by
positive multiples of their least common multiple. -/
theorem sum_divisorCount_sq_eq_sum_div_lcm (n : Nat) :
    ∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 2 =
      ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n, n / a.lcm b := by
  classical
  calc
    ∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 2 =
        ∑ i ∈ Finset.Icc 1 n,
          ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
            if a ∣ i ∧ b ∣ i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [divisorCount_eq_sum_indicator_Icc hi, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases ha : a ∣ i <;> by_cases hb : b ∣ i <;> simp [ha, hb]
    _ = ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          ∑ i ∈ Finset.Icc 1 n, if a ∣ i ∧ b ∣ i then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          n / a.lcm b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact common_multiple_indicator_sum n a b

private def invMultiplesSum (n d : Nat) : Real :=
  ∑ a ∈ Finset.Icc 1 n, if d ∣ a then (a : Real)⁻¹ else 0

private lemma invMultiplesSum_eq (n d : Nat) (hd : 0 < d) :
    invMultiplesSum n d = (d : Real)⁻¹ * (harmonic (n / d) : Real) := by
  classical
  unfold invMultiplesSum
  rw [← Finset.sum_filter]
  have hsum_forward :
      ∑ j ∈ Finset.Icc 1 (n / d), ((d * j : Nat) : Real)⁻¹ =
        ∑ a ∈ {a ∈ Finset.Icc 1 n | d ∣ a}, (a : Real)⁻¹ := by
    apply Finset.sum_bij (fun j _ ↦ d * j)
    · intro j hj
      simp only [Finset.mem_Icc, Finset.mem_filter] at hj ⊢
      refine ⟨⟨Nat.mul_pos hd hj.1, ?_⟩, dvd_mul_right d j⟩
      simpa [mul_comm] using Nat.mul_le_of_le_div d j n hj.2
    · intro j₁ _ j₂ _ h
      exact Nat.eq_of_mul_eq_mul_left hd h
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      refine ⟨a / d, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) ha.2) hd
        · exact Nat.div_le_div_right ha.1.2
      · rw [mul_comm]
        exact Nat.div_mul_cancel ha.2
    · intro j hj
      rfl
  rw [← hsum_forward]
  calc
    (∑ j ∈ Finset.Icc 1 (n / d), ((d * j : Nat) : Real)⁻¹) =
        (d : Real)⁻¹ * ∑ j ∈ Finset.Icc 1 (n / d), (j : Real)⁻¹ := by
      simp_rw [Nat.cast_mul, mul_inv]
      rw [Finset.mul_sum]
    _ = (d : Real)⁻¹ * (harmonic (n / d) : Real) := by
      congr 1
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private def commonDivisorTerm (a b d : Nat) : Real :=
  if d ∣ a ∧ d ∣ b then (d : Real) / ((a : Real) * (b : Real)) else 0

private lemma inv_lcm_le_commonDivisorSum {n a b : Nat}
    (ha : a ∈ Finset.Icc 1 n) (hb : b ∈ Finset.Icc 1 n) :
    ((a.lcm b : Nat) : Real)⁻¹ ≤
      ∑ d ∈ Finset.Icc 1 n, commonDivisorTerm a b d := by
  simp only [Finset.mem_Icc] at ha hb
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (by omega)
  have hgle : a.gcd b ≤ n :=
    (Nat.gcd_le_left b (by omega)).trans ha.2
  have hgmem : a.gcd b ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    omega
  have hlcm0 : a.lcm b ≠ 0 := Nat.lcm_ne_zero ha0 hb0
  have hinv : ((a.lcm b : Nat) : Real)⁻¹ =
      (a.gcd b : Real) / ((a : Real) * (b : Real)) := by
    have hmul : (a.gcd b : Real) * (a.lcm b : Real) =
        (a : Real) * (b : Real) := by
      exact_mod_cast Nat.gcd_mul_lcm a b
    field_simp [ha0, hb0, hlcm0]
    nlinarith
  calc
    ((a.lcm b : Nat) : Real)⁻¹ = commonDivisorTerm a b (a.gcd b) := by
      rw [hinv]
      simp [commonDivisorTerm, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
    _ ≤ ∑ d ∈ Finset.Icc 1 n, commonDivisorTerm a b d := by
      apply Finset.single_le_sum
      · intro d _
        unfold commonDivisorTerm
        split_ifs
        · positivity
        · exact le_rfl
      · exact hgmem

private lemma commonDivisorTerm_eq (a b d : Nat) :
    commonDivisorTerm a b d =
      (d : Real) * (if d ∣ a then (a : Real)⁻¹ else 0) *
        (if d ∣ b then (b : Real)⁻¹ else 0) := by
  by_cases ha : d ∣ a
  · by_cases hb : d ∣ b
    · simp [commonDivisorTerm, ha, hb, div_eq_mul_inv]
      ring
    · simp [commonDivisorTerm, ha, hb]
  · by_cases hb : d ∣ b
    · simp [commonDivisorTerm, ha, hb]
    · simp [commonDivisorTerm, ha, hb]

private lemma sum_commonDivisorTerm_eq (n d : Nat) (hd : 0 < d) :
    ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n, commonDivisorTerm a b d =
      (d : Real)⁻¹ * (harmonic (n / d) : Real) ^ 2 := by
  let f : Nat → Real := fun a ↦ if d ∣ a then (a : Real)⁻¹ else 0
  have hfactor :
      ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n, commonDivisorTerm a b d =
        (d : Real) * (∑ a ∈ Finset.Icc 1 n, f a) ^ 2 := by
    calc
      ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n, commonDivisorTerm a b d =
          ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
            (d : Real) * f a * f b := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact commonDivisorTerm_eq a b d
      _ = ∑ a ∈ Finset.Icc 1 n,
          ((d : Real) * f a) * ∑ b ∈ Finset.Icc 1 n, f b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      _ = (∑ a ∈ Finset.Icc 1 n, (d : Real) * f a) *
          ∑ b ∈ Finset.Icc 1 n, f b := by
        rw [Finset.sum_mul]
      _ = ((d : Real) * ∑ a ∈ Finset.Icc 1 n, f a) *
          ∑ b ∈ Finset.Icc 1 n, f b := by
        congr 1
        exact (Finset.mul_sum _ _ _).symm
      _ = (d : Real) * (∑ a ∈ Finset.Icc 1 n, f a) ^ 2 := by
        ring
  rw [hfactor]
  have hsum : ∑ a ∈ Finset.Icc 1 n, f a =
      (d : Real)⁻¹ * (harmonic (n / d) : Real) := by
    exact invMultiplesSum_eq n d hd
  rw [hsum]
  have hd0 : (d : Real) ≠ 0 := by positivity
  field_simp

/-- The reciprocal-LCM sum is bounded by Chen's common-divisor reindexing. -/
theorem sum_inv_lcm_le_sum_harmonic (n : Nat) :
    ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ((a.lcm b : Nat) : Real)⁻¹ ≤
      ∑ d ∈ Finset.Icc 1 n,
        (d : Real)⁻¹ * (harmonic (n / d) : Real) ^ 2 := by
  calc
    ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ((a.lcm b : Nat) : Real)⁻¹ ≤
        ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          ∑ d ∈ Finset.Icc 1 n, commonDivisorTerm a b d := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact inv_lcm_le_commonDivisorSum ha hb
    _ = ∑ a ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 n,
          ∑ b ∈ Finset.Icc 1 n, commonDivisorTerm a b d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 n, ∑ a ∈ Finset.Icc 1 n,
          ∑ b ∈ Finset.Icc 1 n, commonDivisorTerm a b d := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 n,
        (d : Real)⁻¹ * (harmonic (n / d) : Real) ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact sum_commonDivisorTerm_eq n d (by
        simp only [Finset.mem_Icc] at hd
        omega)

private lemma harmonic_term_le_secondMomentKernel {n d : Nat}
    (hd : d ∈ Finset.Icc 1 n) :
    (n : Real) * ((d : Real)⁻¹ * (harmonic (n / d) : Real) ^ 2) ≤
      secondMomentKernel n d := by
  simp only [Finset.mem_Icc] at hd
  have hdpos : 0 < d := by omega
  have hnpos : 0 < n := hdpos.trans_le hd.2
  have hqpos : 0 < n / d := Nat.div_pos hd.2 hdpos
  have hcastpos : (0 : Real) < (n / d : Nat) := by exact_mod_cast hqpos
  have hlog : Real.log (n / d : Nat) ≤ Real.log ((n : Real) / d) :=
    Real.log_le_log hcastpos Nat.cast_div_le
  have hharm : (harmonic (n / d) : Real) ≤
      Real.log n - Real.log d + 1 := by
    calc
      (harmonic (n / d) : Real) ≤ 1 + Real.log (n / d : Nat) :=
        harmonic_le_one_add_log (n / d)
      _ ≤ 1 + Real.log ((n : Real) / d) := by linarith
      _ = Real.log n - Real.log d + 1 := by
        rw [Real.log_div (by exact_mod_cast hnpos.ne') (by exact_mod_cast hdpos.ne')]
        ring
  have hharmnonneg : (0 : Real) ≤ (harmonic (n / d) : Real) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hweightnonneg : 0 ≤ Real.log n - Real.log d + 1 :=
    hharmnonneg.trans hharm
  have hsquare : (harmonic (n / d) : Real) ^ 2 ≤
      (Real.log n - Real.log d + 1) ^ 2 :=
    (sq_le_sq₀ hharmnonneg hweightnonneg).2 hharm
  calc
    (n : Real) * ((d : Real)⁻¹ * (harmonic (n / d) : Real) ^ 2) =
        (n : Real) / d * (harmonic (n / d) : Real) ^ 2 := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ (n : Real) / d * (Real.log n - Real.log d + 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = secondMomentKernel n d := by rfl

private theorem sum_divisorCount_sq_le_mul_inv_lcm (n : Nat) :
    ((∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 2 : Nat) : Real) ≤
      (n : Real) * ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ((a.lcm b : Nat) : Real)⁻¹ := by
  rw [sum_divisorCount_sq_eq_sum_div_lcm, Nat.cast_sum]
  push_cast
  calc
    (∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ((n / a.lcm b : Nat) : Real)) ≤
        ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          (n : Real) / (a.lcm b : Nat) := by
      exact Finset.sum_le_sum fun _ _ ↦ Finset.sum_le_sum fun _ _ ↦ Nat.cast_div_le
    _ = (n : Real) * ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
        ((a.lcm b : Nat) : Real)⁻¹ := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

/-- Chen's second divisor-moment estimate, with the source's constant
`A₂ = 1/3`. -/
theorem chen_eight_second_moment (n : Nat) :
    ((∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 2 : Nat) : Real) ≤
      (n : Real) / 3 * (Real.log n + 2) ^ 3 := by
  by_cases hn0 : n = 0
  · subst n
    norm_num
  calc
    ((∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 2 : Nat) : Real) ≤
        (n : Real) * ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n,
          ((a.lcm b : Nat) : Real)⁻¹ := sum_divisorCount_sq_le_mul_inv_lcm n
    _ ≤ (n : Real) * ∑ d ∈ Finset.Icc 1 n,
        (d : Real)⁻¹ * (harmonic (n / d) : Real) ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_inv_lcm_le_sum_harmonic n) (Nat.cast_nonneg n)
    _ = ∑ d ∈ Finset.Icc 1 n,
        (n : Real) * ((d : Real)⁻¹ * (harmonic (n / d) : Real) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ Finset.Icc 1 n, secondMomentKernel n d := by
      exact Finset.sum_le_sum fun d hd ↦ harmonic_term_le_secondMomentKernel hd
    _ ≤ (n : Real) / 3 * (Real.log n + 2) ^ 3 := sum_secondMomentKernel_le n

end

end Waring.Analytic
