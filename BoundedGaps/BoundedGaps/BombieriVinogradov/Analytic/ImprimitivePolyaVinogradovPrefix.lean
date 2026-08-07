import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermPolyaVinogradov
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Polya--Vinogradov for imprimitive prefixes

This file proves the all-nonprincipal natural-prefix specialization of
KoukoulopoulosDistributionPrimesPrelim2022, Theorem 10.6, needed on printed
p. 125. The explicit factor `2` comes from pairing divisors of the quotient
of the modulus by the conductor; the source states only an absolute constant.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

private theorem card_divisors_le_two_mul_sqrt
    {n : ℕ} (hn : 0 < n) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  let small := n.divisors.filter fun d ↦ d ≤ Nat.sqrt n
  let large := n.divisors.filter fun d ↦ ¬d ≤ Nat.sqrt n
  have hsmall : small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    apply Finset.card_le_card
    intro d hd
    simp only [small, Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
  have hlarge : large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    refine Finset.card_le_card_of_injOn (fun d ↦ n / d) ?_ ?_
    · intro d hd
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd
      have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd.1).1
      have hdPos : 0 < d := Nat.pos_of_mem_divisors hd.1
      have hquotPos : 0 < n / d :=
        Nat.div_pos (Nat.le_of_dvd hn hdDvd) hdPos
      have hfactor : n = d * (n / d) := (Nat.mul_div_cancel' hdDvd).symm
      exact Finset.mem_Icc.mpr
        ⟨hquotPos, (Nat.le_sqrt_of_eq_mul hfactor).resolve_left hd.2⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
      have hd₁Dvd : d₁ ∣ n := (Nat.mem_divisors.mp hd₁.1).1
      have hd₂Dvd : d₂ ∣ n := (Nat.mem_divisors.mp hd₂.1).1
      have hquotPos : 0 < n / d₁ :=
        Nat.div_pos (Nat.le_of_dvd hn hd₁Dvd)
          (Nat.pos_of_mem_divisors hd₁.1)
      change n / d₁ = n / d₂ at heq
      apply Nat.mul_right_cancel hquotPos
      calc
        d₁ * (n / d₁) = n := Nat.mul_div_cancel' hd₁Dvd
        _ = d₂ * (n / d₂) := (Nat.mul_div_cancel' hd₂Dvd).symm
        _ = d₂ * (n / d₁) := by rw [heq]
  have hsmall' : small.card ≤ Nat.sqrt n := by
    calc
      small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hsmall
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hlarge' : large.card ≤ Nat.sqrt n := by
    calc
      large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hlarge
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hpartition : small.card + large.card = n.divisors.card := by
    simpa [small, large] using
      (Finset.card_filter_add_card_filter_not (s := n.divisors)
        (fun d ↦ d ≤ Nat.sqrt n))
  omega

private theorem divisors_gcd_eq_filter
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (n.gcd r).divisors = r.divisors.filter (fun a ↦ a ∣ n) := by
  ext a
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨ha, _⟩
    exact ⟨⟨ha.trans (Nat.gcd_dvd_right n r), hr.ne'⟩,
      ha.trans (Nat.gcd_dvd_left n r)⟩
  · rintro ⟨⟨har, _⟩, han⟩
    exact ⟨Nat.dvd_gcd han har, hgcd.ne'⟩

private theorem sum_moebius_divisors_eq_coprimeIndicator
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (∑ a ∈ r.divisors,
      if a ∣ n then
        ((ArithmeticFunction.moebius a : ℤ) : ℂ)
      else 0) =
      if n.Coprime r then 1 else 0 := by
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  calc
    (∑ a ∈ r.divisors,
        if a ∣ n then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) =
        ∑ a ∈ r.divisors.filter (fun a ↦ a ∣ n),
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [Finset.sum_filter]
    _ = ∑ a ∈ (n.gcd r).divisors,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [divisors_gcd_eq_filter hn hr]
    _ = ∑ a ∈ (n.gcd r).divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) a := by
      simp
    _ = (((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (n.gcd r)) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (1 : ArithmeticFunction ℂ) (n.gcd r) := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n.Coprime r then 1 else 0 := by
      by_cases hcop : n.Coprime r <;> simp [hcop]

private theorem character_eq_primitive_mul_coprimeIndicator
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (n : ℕ) :
    chi n = chi.primitiveCharacter n *
      (if n.Coprime (q / chi.conductor) then 1 else 0) := by
  have hdvd : chi.conductor ∣ q := chi.conductor_dvd_level
  have hfactor : chi.conductor * (q / chi.conductor) = q :=
    Nat.mul_div_cancel' hdvd
  by_cases hnr : n.Coprime (q / chi.conductor)
  · rw [if_pos hnr, mul_one]
    by_cases hnd : n.Coprime chi.conductor
    · have hnq : n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact ⟨hnd, hnr⟩
      simpa only [Int.cast_natCast] using
        (chi.primitiveCharacter_apply_of_isCoprime
          (Nat.isCoprime_iff_coprime.mpr hnq)).symm
    · have hnq : ¬n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact fun h ↦ hnd h.1
      have hchiZero : chi (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
          (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))
      have hpsiZero : chi.primitiveCharacter (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi.primitiveCharacter (n : ℤ)).2
          (fun h ↦ hnd (Nat.isCoprime_iff_coprime.mp h))
      simpa only [Int.cast_natCast] using hchiZero.trans hpsiZero.symm
  · rw [if_neg hnr, mul_zero]
    have hnq : ¬n.Coprime q := by
      rw [← hfactor, Nat.coprime_mul_iff_right]
      exact fun h ↦ hnr h.2
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
        (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))

private theorem sum_multiples_character
    {d a Y : ℕ} (ha : 0 < a) (psi : DirichletCharacter ℂ d) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n), psi n) =
      ∑ m ∈ Finset.Icc 1 (Y / a), psi (a * m) := by
  classical
  refine Finset.sum_bij'
    (fun n _ ↦ n / a) (fun m _ ↦ a * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hnPos : 0 < n := zero_lt_one.trans_le hn.1.1
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hnPos hn.2) ha,
        Nat.div_le_div_right hn.1.2⟩
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hm.1,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hm.2⟩,
        Nat.dvd_mul_right a m⟩
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m hm
    exact Nat.mul_div_cancel_left m ha
  · intro n hn
    simp only [Finset.mem_filter] at hn
    congr 1
    simpa only [Nat.cast_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod d))
        (Nat.mul_div_cancel' hn.2).symm

private theorem imprimitivePrefix_eq_divisorSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (Y : ℕ) :
    dirichletCharacterIntervalSum 1 Y q chi =
      ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
  classical
  have hdPos : 0 < chi.conductor := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hrPos : 0 < q / chi.conductor :=
    Nat.div_pos
      (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level) hdPos
  rw [dirichletCharacterIntervalSum]
  calc
    (∑ n ∈ Finset.Icc 1 Y, chi n) =
        ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (if n.Coprime (q / chi.conductor) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact character_eq_primitive_mul_coprimeIndicator chi n
    _ = ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (∑ a ∈ (q / chi.conductor).divisors,
              if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_moebius_divisors_eq_coprimeIndicator
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1) hrPos]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
          ∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
      apply Finset.sum_congr rfl
      intro a ha
      have haPos : 0 < a := Nat.pos_of_mem_divisors ha
      calc
        (∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0)) =
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n),
              chi.primitiveCharacter n *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n hn
          by_cases han : a ∣ n <;> simp [han]
        _ = ∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter (a * m) *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [← Finset.sum_mul, sum_multiples_character haPos,
            Finset.sum_mul]
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            (∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter m) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [map_mul]
          ring
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
              chi.primitiveCharacter := by
          rw [dirichletCharacterIntervalSum]

/-- The all-nonprincipal natural-prefix specialization of
Polya--Vinogradov. -/
theorem norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (Y : ℕ) :
    ‖dirichletCharacterIntervalSum 1 Y q chi‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let d := chi.conductor
  let r := q / d
  have hdPos : 0 < d := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hdDvd : d ∣ q := chi.conductor_dvd_level
  have hfactor : d * r = q := Nat.mul_div_cancel' hdDvd
  have hrPos : 0 < r :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hdDvd) hdPos
  have hdNeOne : d ≠ 1 := by
    intro hd
    exact hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
  have hd : 1 < d := by omega
  have hdLeq : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdDvd
  letI : NeZero d := ⟨hdPos.ne'⟩
  have hscalePos :
      0 < Real.sqrt (d : ℝ) * Real.log (d : ℝ) :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hdPos))
      (Real.log_pos (by exact_mod_cast hd))
  have hcard : r.divisors.card ≤ 2 * Nat.sqrt r :=
    card_divisors_le_two_mul_sqrt hrPos
  have hcardReal :
      (r.divisors.card : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by
    calc
      (r.divisors.card : ℝ) ≤ ((2 * Nat.sqrt r : ℕ) : ℝ) := by
        exact_mod_cast hcard
      _ = 2 * (Nat.sqrt r : ℝ) := by norm_num
      _ ≤ 2 * Real.sqrt (r : ℝ) := by
        gcongr
        exact Real.nat_sqrt_le_real_sqrt
  have hsqrt :
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) = Real.sqrt (q : ℝ) := by
    calc
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) =
          Real.sqrt ((d : ℝ) * (r : ℝ)) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (q : ℝ) := by rw [← Nat.cast_mul, hfactor]
  have hlog : Real.log (d : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hdPos) (by exact_mod_cast hdLeq)
  rw [imprimitivePrefix_eq_divisorSum chi Y]
  calc
    ‖∑ a ∈ r.divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) d
            chi.primitiveCharacter‖ ≤
        ∑ a ∈ r.divisors,
          ‖(((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ r.divisors,
        Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmu : ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or a with hzero | hone | hneg
        · simp [hzero]
        · simp [hone]
        · simp [hneg]
      have hcoeff :
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ ≤ 1 := by
        rw [norm_mul]
        calc
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ *
              ‖chi.primitiveCharacter a‖ ≤ 1 * 1 :=
            mul_le_mul hmu (chi.primitiveCharacter.norm_le_one a)
              (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      rw [norm_mul]
      calc
        ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ *
            ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ ≤
            1 * ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ :=
          mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ ≤ Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
          simpa using
            (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
              hd chi.primitiveCharacter chi.primitiveCharacter_isPrimitive
              1 (Y / a)).le
    _ = (r.divisors.card : ℝ) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) := by simp
    _ ≤ (2 * Real.sqrt (r : ℝ)) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardReal hscalePos.le
    _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by
      calc
        (2 * Real.sqrt (r : ℝ)) *
            (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) =
            2 * (Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ)) *
              Real.log (d : ℝ) := by ring
        _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by rw [hsqrt]
    _ ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      gcongr

end BoundedGaps.Maynard
