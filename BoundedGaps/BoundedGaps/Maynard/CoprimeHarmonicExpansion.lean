import BoundedGaps.Maynard.MaynardCoprimeHarmonic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

noncomputable section

/-!
# Quantitative and coprime harmonic expansions

The Euler-Mascheroni remainder is made quantitative, and Möbius
inclusion-exclusion rewrites the coprime harmonic sum as a finite divisor sum.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable def realHarmonic (n : ℕ) : ℝ :=
  ((harmonic n : ℚ) : ℝ)

theorem abs_realHarmonic_sub_log_sub_eulerMascheroni_le
    {n : ℕ} (hn : 0 < n) :
    |realHarmonic n - Real.log n - Real.eulerMascheroniConstant| ≤
      (1 : ℝ) / n := by
  have hlower := (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n).le
  have hupper := (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n).le
  simp only [Real.eulerMascheroniSeq', hn.ne', if_false,
    Real.eulerMascheroniSeq, realHarmonic] at hlower hupper ⊢
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsuccPos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hratioPos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / n :=
    div_pos hsuccPos hnPos
  have hlogDiff : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤
      (1 : ℝ) / n := by
    calc
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log n =
          Real.log ((((n + 1 : ℕ) : ℝ) / n)) := by
        exact (Real.log_div hsuccPos.ne' hnPos.ne').symm
      _ ≤ (((n + 1 : ℕ) : ℝ) / n) - 1 :=
        Real.log_le_sub_one_of_pos hratioPos
      _ = (1 : ℝ) / n := by
        push_cast
        field_simp
        ring
  have hupper' : realHarmonic n - Real.log ((n + 1 : ℕ) : ℝ) ≤
      Real.eulerMascheroniConstant := by
    simpa only [Nat.cast_add, Nat.cast_one, realHarmonic] using hupper
  simp only [realHarmonic] at hupper'
  rw [abs_of_nonneg (by linarith)]
  linarith

private theorem sum_moebius_divisors_gcd
    {n W : ℕ} (hn : 0 < n) :
    (∑ d ∈ (n.gcd W).divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if Nat.Coprime n W then 1 else 0 := by
  have hgcd : 0 < n.gcd W := Nat.gcd_pos_of_pos_left W hn
  have hInt : (∑ d ∈ (n.gcd W).divisors,
      ArithmeticFunction.moebius d) =
      if Nat.Coprime n W then (1 : ℤ) else 0 := by
    calc
      (∑ d ∈ (n.gcd W).divisors, ArithmeticFunction.moebius d) =
          (ArithmeticFunction.moebius * ArithmeticFunction.zeta) (n.gcd W) := by
        rw [ArithmeticFunction.coe_mul_zeta_apply]
      _ = (1 : ArithmeticFunction ℤ) (n.gcd W) := by
        rw [ArithmeticFunction.moebius_mul_coe_zeta]
      _ = if Nat.Coprime n W then 1 else 0 := by
        by_cases hc : Nat.Coprime n W <;> simp [hc]
  exact_mod_cast hInt

private theorem divisors_gcd_eq_filter
    {n W : ℕ} (hn : 0 < n) (hW : 0 < W) :
    (n.gcd W).divisors = W.divisors.filter (· ∣ n) := by
  ext d
  have hgcd : 0 < n.gcd W := Nat.gcd_pos_of_pos_left W hn
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, hgcdNe⟩
    exact ⟨⟨hd.trans (Nat.gcd_dvd_right n W), hW.ne'⟩,
      hd.trans (Nat.gcd_dvd_left n W)⟩
  · rintro ⟨⟨hdW, hWNe⟩, hdn⟩
    exact ⟨Nat.dvd_gcd hdn hdW, hgcd.ne'⟩

private theorem coprime_inv_eq_moebius_sum
    {n W : ℕ} (hn : 0 < n) (hW : 0 < W) :
    (if Nat.Coprime n W then (1 : ℝ) / n else 0) =
      ∑ d ∈ W.divisors,
        if d ∣ n then (ArithmeticFunction.moebius d : ℝ) / n else 0 := by
  have hindicator := sum_moebius_divisors_gcd (W := W) hn
  calc
    (if Nat.Coprime n W then (1 : ℝ) / n else 0) =
        (if Nat.Coprime n W then (1 : ℝ) else 0) / n := by
      by_cases hc : Nat.Coprime n W
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, zero_div]
    _ = (∑ d ∈ (n.gcd W).divisors,
        (ArithmeticFunction.moebius d : ℝ)) / n := by rw [hindicator]
    _ = (∑ d ∈ W.divisors.filter (· ∣ n),
        (ArithmeticFunction.moebius d : ℝ)) / n := by
      rw [divisors_gcd_eq_filter hn hW]
    _ = ∑ d ∈ W.divisors,
        if d ∣ n then (ArithmeticFunction.moebius d : ℝ) / n else 0 := by
      rw [Finset.sum_filter, Finset.sum_div]
      simp only [ite_div, zero_div]

private theorem sum_multiples_inv {d Q : ℕ} (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 Q, if d ∣ n then (1 : ℝ) / n else 0) =
      (1 : ℝ) / d * realHarmonic (Q / d) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 Q, if d ∣ n then (1 : ℝ) / n else 0) =
        ∑ n ∈ (Finset.Icc 1 Q).filter (d ∣ ·), (1 : ℝ) / n := by
      rw [Finset.sum_filter]
    _ = ∑ m ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / (d * m) := by
      refine Finset.sum_bij'
        (fun n _ => n / d) (fun m _ => d * m) ?_ ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn
        have hnPos : 0 < n := zero_lt_one.trans_le hn.1.1
        exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hnPos hn.2) hd,
          Nat.div_le_div_right hn.1.2⟩
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd hm.1, ?_⟩,
          Nat.dvd_mul_right d m⟩
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hm.2
      · intro n hn
        simp only [Finset.mem_filter] at hn
        exact Nat.mul_div_cancel' hn.2
      · intro m hm
        exact Nat.mul_div_cancel_left m hd
      · intro n hn
        simp only [Finset.mem_filter] at hn
        have hnat := Nat.mul_div_cancel' hn.2
        norm_cast at hnat ⊢
        rw [hnat]
    _ = (1 : ℝ) / d *
        (∑ m ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = (1 : ℝ) / d * realHarmonic (Q / d) := by
      congr 1
      unfold realHarmonic
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem coprimeHarmonicSum_eq_moebius_harmonic
    {W Q : ℕ} (hW : 0 < W) :
    coprimeHarmonicSum W Q =
      ∑ d ∈ W.divisors,
        (ArithmeticFunction.moebius d : ℝ) / d * realHarmonic (Q / d) := by
  classical
  unfold coprimeHarmonicSum
  rw [Finset.sum_filter]
  calc
    (∑ n ∈ Finset.Icc 1 Q,
        if Nat.Coprime n W then (1 : ℝ) / n else 0) =
        ∑ n ∈ Finset.Icc 1 Q, ∑ d ∈ W.divisors,
          if d ∣ n then (ArithmeticFunction.moebius d : ℝ) / n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact coprime_inv_eq_moebius_sum
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1) hW
    _ = ∑ d ∈ W.divisors, ∑ n ∈ Finset.Icc 1 Q,
          if d ∣ n then (ArithmeticFunction.moebius d : ℝ) / n else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ W.divisors,
        (ArithmeticFunction.moebius d : ℝ) / d * realHarmonic (Q / d) := by
      apply Finset.sum_congr rfl
      intro d hdW
      have hdPos := Nat.pos_of_mem_divisors hdW
      calc
        (∑ n ∈ Finset.Icc 1 Q,
            if d ∣ n then (ArithmeticFunction.moebius d : ℝ) / n else 0) =
            (ArithmeticFunction.moebius d : ℝ) *
              (∑ n ∈ Finset.Icc 1 Q, if d ∣ n then (1 : ℝ) / n else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hdn : d ∣ n <;> simp [hdn]
          ring
        _ = (ArithmeticFunction.moebius d : ℝ) *
            ((1 : ℝ) / d * realHarmonic (Q / d)) := by
          rw [sum_multiples_inv hdPos]
        _ = (ArithmeticFunction.moebius d : ℝ) / d *
            realHarmonic (Q / d) := by ring

end BoundedGaps.Maynard
