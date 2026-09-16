import Waring.Analytic.AbelVariation

/-!
# Perturbation-phase variation in Chen's Lemma 7

This file proves the exact telescoping and numerical bounds for the slowly
varying factor `exp(2*pi*i*z*x^5)` [CHEN1964-EN, pp. 1551-1552;
CHEN1964-ZH, pp. 718-719].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The real argument of Chen's fifth-power perturbation, starting at the
integer `M` and offset by `i`. -/
noncomputable def fifthPerturbationPhase (z : Real) (M i : Nat) : Real :=
  2 * Real.pi * z * (((M + i : Nat) : Real) ^ 5)

/-- One phase increment has the expected absolute fifth-power difference. -/
theorem abs_fifthPerturbationPhase_sub (z : Real) (M i : Nat) :
    |fifthPerturbationPhase z M (i + 1) -
        fifthPerturbationPhase z M i| =
      2 * Real.pi * |z| *
        ((((M + (i + 1) : Nat) : Real) ^ 5) -
          (((M + i : Nat) : Real) ^ 5)) := by
  have hbase : (0 : Real) ≤ ((M + i : Nat) : Real) := by positivity
  have hstep : ((M + i : Nat) : Real) ≤ ((M + (i + 1) : Nat) : Real) := by
    exact_mod_cast Nat.add_le_add_left (Nat.le_succ i) M
  have hpow : (((M + i : Nat) : Real) ^ 5) ≤
      (((M + (i + 1) : Nat) : Real) ^ 5) :=
    pow_le_pow_left₀ hbase hstep 5
  rw [fifthPerturbationPhase, fifthPerturbationPhase, ← mul_sub, abs_mul,
    abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos),
    abs_of_nonneg (sub_nonneg.mpr hpow)]

/-- The total discrete variation telescopes exactly to the endpoint
fifth-power difference. -/
theorem sum_abs_fifthPerturbationPhase_sub (z : Real) (M n : Nat) :
    (∑ i ∈ Finset.range n,
      |fifthPerturbationPhase z M (i + 1) -
        fifthPerturbationPhase z M i|) =
      2 * Real.pi * |z| *
        ((((M + n : Nat) : Real) ^ 5) - ((M : Real) ^ 5)) := by
  calc
    (∑ i ∈ Finset.range n,
        |fifthPerturbationPhase z M (i + 1) -
          fifthPerturbationPhase z M i|) =
        ∑ i ∈ Finset.range n,
          (2 * Real.pi * |z|) *
            ((((M + (i + 1) : Nat) : Real) ^ 5) -
              (((M + i : Nat) : Real) ^ 5)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact abs_fifthPerturbationPhase_sub z M i
    _ = (2 * Real.pi * |z|) *
        (∑ i ∈ Finset.range n,
          ((((M + (i + 1) : Nat) : Real) ^ 5) -
            (((M + i : Nat) : Real) ^ 5))) := by
      rw [Finset.mul_sum]
    _ = 2 * Real.pi * |z| *
        ((((M + n : Nat) : Real) ^ 5) - ((M : Real) ^ 5)) := by
      congr 1
      simpa only [Nat.add_zero] using
        (Finset.sum_range_sub
          (fun j ↦ (((M + j : Nat) : Real) ^ 5)) n)

/-- On an interval contained in `[0,P]`, the fifth-power endpoint difference
is at most `5*P^4` times the interval length. -/
theorem fifthPower_sub_le_five_mul_fourth_mul
    (M n P : Nat) (hMP : M + n ≤ P) :
    ((((M + n : Nat) : Real) ^ 5) - ((M : Real) ^ 5)) ≤
      5 * (P : Real) ^ 4 * n := by
  have hM : M ≤ M + n := Nat.le_add_right M n
  have hMReal : (0 : Real) ≤ M := by positivity
  have hMNReal : (M : Real) ≤ ((M + n : Nat) : Real) := by
    exact_mod_cast hM
  have hMNNonneg : (0 : Real) ≤ ((M + n : Nat) : Real) := by positivity
  have hPow := abs_pow_sub_pow_le
    (a := ((M + n : Nat) : Real)) (b := (M : Real)) (n := 5)
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hMReal hMNReal 5)),
    abs_of_nonneg hMNNonneg,
    abs_of_nonneg hMReal, max_eq_left hMNReal,
    abs_of_nonneg (sub_nonneg.mpr hMNReal)] at hPow
  have hDiff : (((M + n : Nat) : Real) - M) = n := by
    push_cast
    ring
  rw [hDiff] at hPow
  calc
    ((((M + n : Nat) : Real) ^ 5) - ((M : Real) ^ 5)) ≤
        (n : Real) * 5 * (((M + n : Nat) : Real) ^ 4) := hPow
    _ ≤ (n : Real) * 5 * (P : Real) ^ 4 := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hMP) 4
      · positivity
    _ = 5 * (P : Real) ^ 4 * n := by ring

/-- If the interval length is at most half the denominator, Chen's perturbation
has total phase variation below the convenient threshold `3`. -/
theorem sum_abs_fifthPerturbationPhase_sub_le_three_of_block
    (z : Real) (M n P q : Nat) (hP : 0 < P) (hq : 0 < q)
    (hMP : M + n ≤ P) (hnq : 2 * n ≤ q)
    (hz : |z| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    (∑ i ∈ Finset.range n,
      |fifthPerturbationPhase z M (i + 1) -
        fifthPerturbationPhase z M i|) ≤ 3 := by
  have hPReal : (0 : Real) < P := by exact_mod_cast hP
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hCount : (4 : Real) * n / q ≤ 2 := by
    apply (div_le_iff₀ hqReal).2
    have hnqReal : (2 : Real) * n ≤ q := by exact_mod_cast hnq
    linarith
  rw [sum_abs_fifthPerturbationPhase_sub]
  calc
    2 * Real.pi * |z| *
        ((((M + n : Nat) : Real) ^ 5) - ((M : Real) ^ 5)) ≤
        2 * Real.pi * |z| * (5 * (P : Real) ^ 4 * n) := by
      apply mul_le_mul_of_nonneg_left
      · exact fifthPower_sub_le_five_mul_fourth_mul M n P hMP
      · positivity
    _ ≤ 2 * Real.pi *
        (1 / (10 * (q : Real) * (P : Real) ^ 4)) *
          (5 * (P : Real) ^ 4 * n) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hz (by positivity)
      · positivity
    _ ≤ 2 * 4 *
        (1 / (10 * (q : Real) * (P : Real) ^ 4)) *
          (5 * (P : Real) ^ 4 * n) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left Real.pi_le_four (by norm_num)
        · positivity
      · positivity
    _ = (4 : Real) * n / q := by
      field_simp
      ring
    _ ≤ 2 := hCount
    _ ≤ 3 := by norm_num

/-- Cardinality-shaped form of the block estimate: an `L`-term sum has only
`L-1` adjacent phase increments. -/
theorem sum_abs_fifthPerturbationPhase_sub_le_three_of_block_length
    (z : Real) (M L P q : Nat) (hL : 0 < L) (hP : 0 < P) (hq : 0 < q)
    (hMP : M + L ≤ P + 1) (hLq : 2 * (L - 1) ≤ q)
    (hz : |z| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    (∑ i ∈ Finset.range (L - 1),
      |fifthPerturbationPhase z M (i + 1) -
        fifthPerturbationPhase z M i|) ≤ 3 := by
  apply sum_abs_fifthPerturbationPhase_sub_le_three_of_block
    z M (L - 1) P q hP hq
  · omega
  · exact hLq
  · exact hz

/-- On the full interval `1,...,P`, the same variation bound follows from
`P ≤ 2q`. -/
theorem sum_abs_fifthPerturbationPhase_sub_le_three_of_full
    (z : Real) (P q : Nat) (hP : 0 < P) (hq : 0 < q)
    (hPq : P ≤ 2 * q)
    (hz : |z| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    (∑ i ∈ Finset.range (P - 1),
      |fifthPerturbationPhase z 1 (i + 1) -
        fifthPerturbationPhase z 1 i|) ≤ 3 := by
  have hPReal : (0 : Real) < P := by exact_mod_cast hP
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hEndpoint : 1 + (P - 1) = P := by omega
  have hCount : (4 : Real) * P / (5 * q) ≤ 8 / 5 := by
    apply (div_le_div_iff₀ (by positivity : (0 : Real) < 5 * q)
      (by norm_num : (0 : Real) < 5)).2
    have hPqReal : (P : Real) ≤ 2 * q := by exact_mod_cast hPq
    nlinarith
  rw [sum_abs_fifthPerturbationPhase_sub, hEndpoint]
  simp only [Nat.cast_one, one_pow]
  calc
    2 * Real.pi * |z| * ((P : Real) ^ 5 - 1) ≤
        2 * Real.pi * |z| * (P : Real) ^ 5 := by
      apply mul_le_mul_of_nonneg_left
      · nlinarith
      · positivity
    _ ≤ 2 * Real.pi *
        (1 / (10 * (q : Real) * (P : Real) ^ 4)) * (P : Real) ^ 5 := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hz (by positivity)
      · positivity
    _ ≤ 2 * 4 *
        (1 / (10 * (q : Real) * (P : Real) ^ 4)) * (P : Real) ^ 5 := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left Real.pi_le_four (by norm_num)
        · positivity
      · positivity
    _ = (4 : Real) * P / (5 * q) := by
      field_simp
      ring
    _ ≤ 8 / 5 := hCount
    _ ≤ 3 := by norm_num

end Waring.Analytic
