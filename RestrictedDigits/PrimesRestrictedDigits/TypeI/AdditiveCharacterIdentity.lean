import PrimesRestrictedDigits.Fourier.ContinuousTransform
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Exact Type I additive-character identity

This proves the Moebius and complete-character identity used before the
denominator reduction in `MAYNARD-PRD-PUBLISHED`, pp. 159--160.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem digitPhaseAt_nat_div_eq_stdAddChar
    {m : Nat} [NeZero m] (b n : Nat) :
    digitPhaseAt ((b : Real) / (m : Real)) n =
      ZMod.stdAddChar (((n * b : Nat) : Int) : ZMod m) := by
  rw [ZMod.stdAddChar_coe]
  unfold digitPhaseAt
  congr 1
  push_cast
  ring

private theorem sum_digitPhaseAt_range_eq_ite_dvd
    {m : Nat} (hm : m ≠ 0) (n : Nat) :
    (∑ b ∈ Finset.range m,
      digitPhaseAt ((b : Real) / (m : Real)) n) =
      if m ∣ n then (m : Complex) else 0 := by
  letI : NeZero m := ⟨hm⟩
  simp_rw [digitPhaseAt_nat_div_eq_stdAddChar]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ b : Fin m,
        ZMod.stdAddChar (((n * (b : Nat) : Nat) : Int) : ZMod m)) =
        ∑ x : ZMod m, ZMod.stdAddChar (x * (n : ZMod m)) := by
      refine Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ ?_
      intro b
      congr 1
      have hfin :
          (ZMod.finEquiv m).toEquiv b = ((b : Nat) : ZMod m) := by
        cases m with
        | zero => exact (hm rfl).elim
        | succ m =>
            apply Fin.ext
            change b.val = b.val % (m + 1)
            exact (Nat.mod_eq_of_lt b.isLt).symm
      rw [hfin]
      push_cast
      rw [mul_comm]
    _ = if (n : ZMod m) = 0 then (m : Complex) else 0 := by
      simpa using AddChar.sum_mulShift (n : ZMod m)
        (ZMod.isPrimitive_stdAddChar m)
    _ = if m ∣ n then (m : Complex) else 0 := by
      simp only [ZMod.natCast_eq_zero_iff]

private theorem sum_moebius_divisors_complex (n : Nat) :
    (∑ d ∈ Nat.divisors n,
      (ArithmeticFunction.moebius d : Complex)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg
    (fun f : ArithmeticFunction Complex => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := Complex))
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.one_apply] at h
  exact h

private theorem sum_moebius_dvd_ten (n : Nat) :
    (∑ d ∈ Nat.divisors 10,
      if d ∣ n then (ArithmeticFunction.moebius d : Complex) else 0) =
      if Nat.Coprime n 10 then 1 else 0 := by
  have hfilter :
      (Nat.divisors 10).filter (fun d => d ∣ n) =
        (Nat.divisors 10).filter (fun d => d ∣ Nat.gcd 10 n) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd10, hdn⟩
      exact ⟨hd10, Nat.dvd_gcd (Nat.dvd_of_mem_divisors hd10) hdn⟩
    · rintro ⟨hd10, hdgcd⟩
      exact ⟨hd10, hdgcd.trans (Nat.gcd_dvd_right 10 n)⟩
  calc
    _ = ∑ d ∈ (Nat.divisors 10).filter (fun d => d ∣ n),
          (ArithmeticFunction.moebius d : Complex) := by
      rw [Finset.sum_filter]
    _ = ∑ d ∈ (Nat.divisors 10).filter
          (fun d => d ∣ Nat.gcd 10 n),
          (ArithmeticFunction.moebius d : Complex) := by
      rw [hfilter]
    _ = ∑ d ∈ Nat.divisors (Nat.gcd 10 n),
          (ArithmeticFunction.moebius d : Complex) := by
      rw [Nat.divisors_filter_dvd_of_dvd (by norm_num)
        (Nat.gcd_dvd_left 10 n)]
    _ = if Nat.gcd 10 n = 1 then 1 else 0 :=
      sum_moebius_divisors_complex (Nat.gcd 10 n)
    _ = if Nat.Coprime n 10 then 1 else 0 := by
      simp only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]

private theorem sum_moebius_mul_dvd
    (q n : Nat) (hq10 : Nat.Coprime q 10) :
    (∑ d ∈ Nat.divisors 10,
      if d * q ∣ n then (ArithmeticFunction.moebius d : Complex) else 0) =
      if q ∣ n ∧ Nat.Coprime n 10 then 1 else 0 := by
  by_cases hqn : q ∣ n
  · have hterm (d : Nat) (hd : d ∈ Nat.divisors 10) :
        d * q ∣ n ↔ d ∣ n := by
      have hd10 := Nat.dvd_of_mem_divisors hd
      have hcop : Nat.Coprime d q :=
        (hq10.coprime_dvd_right hd10).symm
      constructor
      · exact fun h => (Nat.dvd_mul_right d q).trans h
      · exact fun h => hcop.mul_dvd_of_dvd_of_dvd h hqn
    simp only [hqn, true_and]
    calc
      _ = ∑ d ∈ Nat.divisors 10,
            if d ∣ n then (ArithmeticFunction.moebius d : Complex) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [if_congr (hterm d hd) rfl rfl]
      _ = if Nat.Coprime n 10 then 1 else 0 := sum_moebius_dvd_ten n
  · rw [if_neg (fun h => hqn h.1)]
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro hdq
    exact hqn ((Nat.dvd_mul_left q d).trans
      (by simpa [Nat.mul_comm] using hdq))

private theorem normalized_phase_indicator
    (d q n : Nat) (hdq : d * q ≠ 0) :
    (ArithmeticFunction.moebius d : Complex) / ((d * q : Nat) : Complex) *
        (∑ b ∈ Finset.range (d * q),
          digitPhaseAt ((b : Real) / ((d * q : Nat) : Real)) n) =
      if d * q ∣ n then (ArithmeticFunction.moebius d : Complex) else 0 := by
  rw [sum_digitPhaseAt_range_eq_ite_dvd hdq n]
  by_cases hdiv : d * q ∣ n
  · rw [if_pos hdiv, if_pos hdiv]
    field_simp
  · rw [if_neg hdiv, if_neg hdiv, mul_zero]

private theorem card_filter_dvd_coprime_eq_moebius_fourier
    (A : Finset Nat) (q : Nat) (hq10 : Nat.Coprime q 10) :
    ((A.filter (fun n => q ∣ n ∧ Nat.Coprime n 10)).card : Complex) =
      ∑ d ∈ Nat.divisors 10,
        (ArithmeticFunction.moebius d : Complex) /
            ((d * q : Nat) : Complex) *
          ∑ b ∈ Finset.range (d * q),
            ∑ n ∈ A,
              digitPhaseAt ((b : Real) / ((d * q : Nat) : Real)) n := by
  have hq : q ≠ 0 := by
    intro h
    subst q
    norm_num [Nat.Coprime] at hq10
  symm
  calc
    _ = ∑ d ∈ Nat.divisors 10,
          ∑ n ∈ A,
            ((ArithmeticFunction.moebius d : Complex) /
                ((d * q : Nat) : Complex) *
              ∑ b ∈ Finset.range (d * q),
                digitPhaseAt ((b : Real) / ((d * q : Nat) : Real)) n) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Nat.divisors 10,
          ∑ n ∈ A,
            if d * q ∣ n then
              (ArithmeticFunction.moebius d : Complex) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro n hn
      apply normalized_phase_indicator
      exact Nat.mul_ne_zero
        (ne_zero_of_dvd_ne_zero (by norm_num)
          (Nat.dvd_of_mem_divisors hd)) hq
    _ = ∑ n ∈ A,
          ∑ d ∈ Nat.divisors 10,
            if d * q ∣ n then
              (ArithmeticFunction.moebius d : Complex) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ A,
          if q ∣ n ∧ Nat.Coprime n 10 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact sum_moebius_mul_dvd q n hq10
    _ = ((A.filter (fun n => q ∣ n ∧ Nat.Coprime n 10)).card : Complex) := by
      rw [← Finset.sum_filter]
      simp

/-- The exact Moebius and additive-character identity preceding the Type I
denominator reduction in `MAYNARD-PRD-PUBLISHED`, pp. 159--160. -/
theorem card_filter_dvd_coprime_paddedRestrictedNumbers_eq_moebius_fourier
    (digit : Fin 10) (length q : Nat) (hq10 : Nat.Coprime q 10) :
    (((paddedRestrictedNumbers digit length).filter
      (fun n => q ∣ n ∧ Nat.Coprime n 10)).card : Complex) =
      ∑ d ∈ Nat.divisors 10,
        (ArithmeticFunction.moebius d : Complex) /
            ((d * q : Nat) : Complex) *
          ∑ b ∈ Finset.range (d * q),
            paddedDigitFourierSumAt digit length
              ((b : Real) / ((d * q : Nat) : Real)) := by
  simpa only [paddedDigitFourierSumAt] using
    card_filter_dvd_coprime_eq_moebius_fourier
      (paddedRestrictedNumbers digit length) q hq10

end PrimesRestrictedDigits
