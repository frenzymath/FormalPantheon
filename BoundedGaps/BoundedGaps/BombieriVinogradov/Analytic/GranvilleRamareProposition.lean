import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamareLcmMain
import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamarePairMass
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The Granville--Ramare coefficient estimate

This file proves `GranvilleRamare1996`, Proposition 10.1, manuscript p. 41.
The square is expanded before the interval-count error is bounded, preserving
the cancellation in the signed least-common-multiple main term.  The exact
statement and source comparison are frozen in `SEM-457`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

private abbrev muR (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ)

private def positiveUpTo (N : ℕ) : Finset ℕ :=
  Finset.Ioc 0 N

private theorem abs_muR_eq_sq (n : ℕ) :
    |muR n| = (muR n) ^ 2 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [muR, h]

private theorem card_multiples_Ioc_eq_sub
    {a b p : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter (fun n => p ∣ n)).card = b / p - a / p := by
  let lower := (Finset.Ioc 0 a).filter (fun n => p ∣ n)
  let upper := (Finset.Ioc 0 b).filter (fun n => p ∣ n)
  have hsubset : lower ⊆ upper := by
    intro n hn
    simp only [lower, upper, Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    omega
  have heq :
      (Finset.Ioc a b).filter (fun n => p ∣ n) = upper \ lower := by
    ext n
    simp only [lower, upper, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff]
    omega
  rw [heq, Finset.card_sdiff_of_subset hsubset]
  simp only [lower, upper, Nat.Ioc_filter_dvd_card_eq_div]

private theorem abs_cast_card_multiples_real_dyadic_sub_le_one
    {N : ℝ} (hN : 0 ≤ N) {p : ℕ} (hp : 0 < p) :
    |((((Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
      (fun n => p ∣ n)).card : ℕ) : ℝ) - N / (p : ℝ)| ≤ 1 := by
  have hTwoN : N ≤ 2 * N := by linarith
  have hfloor : ⌊N⌋₊ ≤ ⌊2 * N⌋₊ := Nat.floor_mono hTwoN
  rw [card_multiples_Ioc_eq_sub hfloor]
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hdiv : N / (p : ℝ) ≤ 2 * N / (p : ℝ) :=
    (div_le_div_iff_of_pos_right hpReal).2 hTwoN
  have hfloorDiv : ⌊N / (p : ℝ)⌋₊ ≤ ⌊2 * N / (p : ℝ)⌋₊ :=
    Nat.floor_mono hdiv
  rw [← Nat.floor_div_natCast, ← Nat.floor_div_natCast,
    Nat.cast_sub hfloorDiv]
  have hNdiv : 0 ≤ N / (p : ℝ) := div_nonneg hN hpReal.le
  have hTwoNdiv : 0 ≤ 2 * N / (p : ℝ) := by positivity
  have hfloorN := Nat.floor_le hNdiv
  have hfloorTwoN := Nat.floor_le hTwoNdiv
  have hceilN := Nat.lt_floor_add_one (N / (p : ℝ))
  have hceilTwoN := Nat.lt_floor_add_one (2 * N / (p : ℝ))
  have hdouble : 2 * N / (p : ℝ) = 2 * (N / (p : ℝ)) := by ring
  rw [abs_le]
  constructor <;> nlinarith

private theorem vaughanFourthCoefficient_eq_sum_filter_dvd
    {V : ℝ} (hV : 0 ≤ V) {n : ℕ} (hn : 0 < n) :
    vaughanFourthCoefficient V n =
      ∑ d ∈ (positiveUpTo ⌊V⌋₊).filter (fun d => d ∣ n), muR d := by
  unfold vaughanFourthCoefficient positiveUpTo
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hdn, -⟩, hdV⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn, Nat.le_floor hdV⟩, hdn⟩
    · rintro ⟨⟨hdPos, hdV⟩, hdn⟩
      exact ⟨⟨hdn, hn.ne'⟩,
        (Nat.cast_le.mpr hdV).trans (Nat.floor_le hV)⟩
  · intro d hd
    rfl

private theorem sum_sq_divisor_filter_eq_pair_count (D I : Finset ℕ) :
    (∑ n ∈ I, (∑ d ∈ D.filter (fun d => d ∣ n), muR d) ^ 2) =
      ∑ d ∈ D, ∑ e ∈ D, muR d * muR e *
        (((I.filter (fun n => Nat.lcm d e ∣ n)).card : ℕ) : ℝ) := by
  have hexpand (n : ℕ) :
      (∑ d ∈ D.filter (fun d => d ∣ n), muR d) ^ 2 =
        ∑ d ∈ D, ∑ e ∈ D,
          if d ∣ n ∧ e ∣ n then muR d * muR e else 0 := by
    rw [pow_two, Finset.sum_mul_sum]
    calc
      (∑ d ∈ D.filter (fun d => d ∣ n),
        ∑ e ∈ D.filter (fun e => e ∣ n), muR d * muR e) =
          ∑ d ∈ D, if d ∣ n then
            ∑ e ∈ D.filter (fun e => e ∣ n), muR d * muR e else 0 := by
              rw [← Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdn : d ∣ n
        · rw [if_pos hdn, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro e he
          by_cases hen : e ∣ n <;> simp [hdn, hen]
        · simp [hdn]
  simp_rw [hexpand]
  calc
    (∑ n ∈ I, ∑ d ∈ D, ∑ e ∈ D,
      if d ∣ n ∧ e ∣ n then muR d * muR e else 0) =
      ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ I,
        if d ∣ n ∧ e ∣ n then muR d * muR e else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      calc
        (∑ n ∈ I, if d ∣ n ∧ e ∣ n then muR d * muR e else 0) =
            ∑ n ∈ I.filter (fun n => Nat.lcm d e ∣ n),
              muR d * muR e := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro n hn
                simp only [Nat.lcm_dvd_iff]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private theorem sum_pair_count_eq_filter_lcm (Z A B : ℕ) :
    (∑ d ∈ positiveUpTo Z, ∑ e ∈ positiveUpTo Z,
      muR d * muR e *
        ((((Finset.Ioc A B).filter
          (fun n => Nat.lcm d e ∣ n)).card : ℕ) : ℝ)) =
      ∑ d ∈ positiveUpTo Z,
        ∑ e ∈ (positiveUpTo Z).filter (fun e => Nat.lcm d e ≤ B),
          muR d * muR e *
            ((((Finset.Ioc A B).filter
              (fun n => Nat.lcm d e ∣ n)).card : ℕ) : ℝ) := by
  apply Finset.sum_congr rfl
  intro d hd
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hle : Nat.lcm d e ≤ B
  · simp [hle]
  · rw [if_neg hle]
    have hempty :
        (Finset.Ioc A B).filter (fun n => Nat.lcm d e ∣ n) = ∅ := by
      apply Finset.filter_false_of_mem
      intro n hnI hdiv
      have hnPos : 0 < n :=
        (Nat.zero_le A).trans_lt (Finset.mem_Ioc.mp hnI).1
      exact hle ((Nat.le_of_dvd hnPos hdiv).trans
        (Finset.mem_Ioc.mp hnI).2)
    simp [hempty]

private theorem pair_count_sum_le_main_add_mass
    {N : ℝ} (hN : 0 ≤ N) (Z : ℕ) :
    (∑ d ∈ positiveUpTo Z,
      ∑ e ∈ (positiveUpTo Z).filter
        (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
        muR d * muR e *
          ((((Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
            (fun n => Nat.lcm d e ∣ n)).card : ℕ) : ℝ)) ≤
      N * |∑ d ∈ positiveUpTo Z,
        ∑ e ∈ (positiveUpTo Z).filter
          (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
          muR d * muR e / (Nat.lcm d e : ℝ)| +
        ∑ d ∈ positiveUpTo Z,
          ∑ e ∈ (positiveUpTo Z).filter
            (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
            (muR d) ^ 2 * (muR e) ^ 2 := by
  let count : ℕ → ℕ → ℝ := fun d e =>
    ((((Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
      (fun n => Nat.lcm d e ∣ n)).card : ℕ) : ℝ)
  let main : ℝ := ∑ d ∈ positiveUpTo Z,
    ∑ e ∈ (positiveUpTo Z).filter
      (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
      muR d * muR e / (Nat.lcm d e : ℝ)
  let error : ℝ := ∑ d ∈ positiveUpTo Z,
    ∑ e ∈ (positiveUpTo Z).filter
      (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
      muR d * muR e * (count d e - N / (Nat.lcm d e : ℝ))
  have hdecomp :
      (∑ d ∈ positiveUpTo Z,
        ∑ e ∈ (positiveUpTo Z).filter
          (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
          muR d * muR e * count d e) = N * main + error := by
    dsimp only [main, error]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  have herror :
      |error| ≤ ∑ d ∈ positiveUpTo Z,
        ∑ e ∈ (positiveUpTo Z).filter
          (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
          (muR d) ^ 2 * (muR e) ^ 2 := by
    dsimp only [error]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro e he
    have hdPos : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hePos : 0 < e :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp he).1).1
    have hlcmPos : 0 < Nat.lcm d e := Nat.lcm_pos hdPos hePos
    have hcount := abs_cast_card_multiples_real_dyadic_sub_le_one hN hlcmPos
    change |muR d * muR e *
      (count d e - N / (Nat.lcm d e : ℝ))| ≤ _
    rw [abs_mul, abs_mul, abs_muR_eq_sq, abs_muR_eq_sq]
    exact mul_le_of_le_one_right
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hcount
  change (∑ d ∈ positiveUpTo Z,
    ∑ e ∈ (positiveUpTo Z).filter
      (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
      muR d * muR e * count d e) ≤ _
  rw [hdecomp]
  calc
    N * main + error ≤ |N * main + error| := le_abs_self _
    _ ≤ |N * main| + |error| := abs_add_le _ _
    _ = N * |main| + |error| := by rw [abs_mul, abs_of_nonneg hN]
    _ ≤ N * |main| +
        ∑ d ∈ positiveUpTo Z,
          ∑ e ∈ (positiveUpTo Z).filter
            (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
            (muR d) ^ 2 * (muR e) ^ 2 :=
      add_le_add le_rfl herror

/-- `GranvilleRamare1996`, Proposition 10.1, with its real endpoints and
divisor cutoff represented exactly by natural floors. -/
theorem sum_sq_vaughanFourthCoefficient_dyadic_le
    {N V : ℝ} (hN : 1 ≤ N) (hV : 1 ≤ V) :
    (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      (vaughanFourthCoefficient V n) ^ 2) ≤
      (4 / 3 : ℝ) * N * (Real.log V + 3) ^ 2 := by
  have hNNonneg : 0 ≤ N := zero_le_one.trans hN
  have hVNonneg : 0 ≤ V := zero_le_one.trans hV
  have hFloorV : 1 ≤ ⌊V⌋₊ := (Nat.one_le_floor_iff V).2 hV
  have hExpanded :
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        (vaughanFourthCoefficient V n) ^ 2) =
        ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
          (∑ d ∈ (positiveUpTo ⌊V⌋₊).filter (fun d => d ∣ n),
            muR d) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [vaughanFourthCoefficient_eq_sum_filter_dvd hVNonneg
      ((Nat.zero_le ⌊N⌋₊).trans_lt (Finset.mem_Ioc.mp hn).1)]
  have hMain := abs_sum_moebius_mul_moebius_div_lcm_le_four_ninths
    (Z := ⌊V⌋₊) (B := ⌊2 * N⌋₊) hFloorV
  have hMass := sum_sq_moebius_pair_lcm_le
    (Z := ⌊V⌋₊) (B := ⌊2 * N⌋₊) hFloorV
  have hFloorTwoN : ((⌊2 * N⌋₊ : ℕ) : ℝ) ≤ 2 * N :=
    Nat.floor_le (mul_nonneg (by norm_num) hNNonneg)
  have hFloorVCast : ((⌊V⌋₊ : ℕ) : ℝ) ≤ V := Nat.floor_le hVNonneg
  have hFloorVPositive : (0 : ℝ) < (⌊V⌋₊ : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hFloorV)
  have hVPositive : 0 < V := zero_lt_one.trans_le hV
  have hLogLe : Real.log (⌊V⌋₊ : ℕ) ≤ Real.log V :=
    Real.strictMonoOn_log.monotoneOn
      hFloorVPositive hVPositive hFloorVCast
  have hLogFloorNonneg : 0 ≤ Real.log (⌊V⌋₊ : ℕ) :=
    Real.log_nonneg (by exact_mod_cast hFloorV)
  have hLogVNonneg : 0 ≤ Real.log V := Real.log_nonneg hV
  have hSquareLog :
      (Real.log (⌊V⌋₊ : ℕ) + 3) ^ 2 ≤ (Real.log V + 3) ^ 2 := by
    have hDiff : 0 ≤ (Real.log V + 3) -
        (Real.log (⌊V⌋₊ : ℕ) + 3) := sub_nonneg.mpr (by linarith)
    have hSum : 0 ≤ (Real.log V + 3) +
        (Real.log (⌊V⌋₊ : ℕ) + 3) := by linarith
    nlinarith [mul_nonneg hDiff hSum]
  calc
    (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        (vaughanFourthCoefficient V n) ^ 2) =
        ∑ d ∈ positiveUpTo ⌊V⌋₊,
          ∑ e ∈ (positiveUpTo ⌊V⌋₊).filter
            (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
            muR d * muR e *
              ((((Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
                (fun n => Nat.lcm d e ∣ n)).card : ℕ) : ℝ) := by
      rw [hExpanded,
        sum_sq_divisor_filter_eq_pair_count,
        sum_pair_count_eq_filter_lcm]
    _ ≤ N * |∑ d ∈ positiveUpTo ⌊V⌋₊,
          ∑ e ∈ (positiveUpTo ⌊V⌋₊).filter
            (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
            muR d * muR e / (Nat.lcm d e : ℝ)| +
        ∑ d ∈ positiveUpTo ⌊V⌋₊,
          ∑ e ∈ (positiveUpTo ⌊V⌋₊).filter
            (fun e => Nat.lcm d e ≤ ⌊2 * N⌋₊),
            (muR d) ^ 2 * (muR e) ^ 2 :=
      pair_count_sum_le_main_add_mass hNNonneg ⌊V⌋₊
    _ ≤ N * ((4 / 9 : ℝ) *
          (Real.log (⌊V⌋₊ : ℕ) + 3) ^ 2) +
        (⌊2 * N⌋₊ : ℕ) *
          ((2 / 3 : ℝ) * (Real.log (⌊V⌋₊ : ℕ) + 3)) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hMain hNNonneg) hMass
    _ ≤ N * ((4 / 9 : ℝ) *
          (Real.log (⌊V⌋₊ : ℕ) + 3) ^ 2) +
        (2 * N) *
          ((2 / 3 : ℝ) * (Real.log (⌊V⌋₊ : ℕ) + 3)) ^ 2 :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hFloorTwoN (sq_nonneg _))
    _ = (4 / 3 : ℝ) * N *
        (Real.log (⌊V⌋₊ : ℕ) + 3) ^ 2 := by ring
    _ ≤ (4 / 3 : ℝ) * N * (Real.log V + 3) ^ 2 :=
      mul_le_mul_of_nonneg_left hSquareLog
        (mul_nonneg (by norm_num) hNNonneg)

end

end BoundedGaps.Maynard
