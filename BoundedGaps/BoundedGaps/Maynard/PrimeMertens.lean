import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP

noncomputable section

/-!
# A bounded-error prime Mertens estimate

This proves the arithmetic input needed by the `kappa = 1` specialization of
GGPY2009, Lemma 4.  The von Mangoldt harmonic sum is compared with
`log (n !) / n`; the contribution from non-prime prime powers is then removed
using its summability in pinned Mathlib.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real ArithmeticFunction

noncomputable def mangoldtHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / (d : ℝ)

noncomputable def primeLogHarmonicSum (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)

private noncomputable def mangoldtFloorAverage (n : ℕ) : ℝ :=
  (∑ d ∈ Ioc 0 n,
    ArithmeticFunction.vonMangoldt d * (n / d : ℕ)) / (n : ℝ)

private noncomputable def nonprimeMangoldtHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n,
    (if d.Prime then 0 else ArithmeticFunction.vonMangoldt d) / (d : ℝ)

theorem sum_Ioc_log_eq_log_factorial (n : ℕ) :
    (∑ m ∈ Ioc 0 n, Real.log m) = Real.log n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ,
        Nat.cast_mul, Real.log_mul]
      · ring
      · exact_mod_cast Nat.succ_ne_zero n
      · exact_mod_cast Nat.factorial_ne_zero n

theorem sum_Ioc_log_eq_mangoldt_floor (n : ℕ) :
    (∑ m ∈ Ioc 0 n, Real.log m) =
      ∑ d ∈ Ioc 0 n,
        ArithmeticFunction.vonMangoldt d * (n / d : ℕ) := by
  calc
    (∑ m ∈ Ioc 0 n, Real.log m) =
        ∑ m ∈ Ioc 0 n,
          (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) m := by
      apply sum_congr rfl
      intro m hm
      rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      rfl
    _ = _ := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
      ArithmeticFunction.vonMangoldt n

private theorem floorAverage_le_harmonic {n : ℕ} (hn : 0 < n) :
    mangoldtFloorAverage n ≤ mangoldtHarmonicSum n := by
  unfold mangoldtFloorAverage mangoldtHarmonicSum
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro d hd
  have hdPos : 0 < d := (Finset.mem_Ioc.mp hd).1
  have hfloor : ((n / d : ℕ) : ℝ) / n ≤ 1 / (d : ℝ) := by
    rw [div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hdPos)]
    norm_cast
    simpa only [one_mul] using Nat.div_mul_le_self n d
  calc
    ArithmeticFunction.vonMangoldt d * (n / d : ℕ) / (n : ℝ) =
        ArithmeticFunction.vonMangoldt d * (((n / d : ℕ) : ℝ) / n) := by
      ring
    _ ≤ ArithmeticFunction.vonMangoldt d * (1 / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hfloor ArithmeticFunction.vonMangoldt_nonneg
    _ = ArithmeticFunction.vonMangoldt d / (d : ℝ) := by ring

private theorem harmonic_le_floorAverage_add_psi {n : ℕ} (hn : 0 < n) :
    mangoldtHarmonicSum n ≤ mangoldtFloorAverage n + Chebyshev.psi n / n := by
  unfold mangoldtHarmonicSum mangoldtFloorAverage
  calc
    (∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / (d : ℝ)) ≤
        ∑ d ∈ Ioc 0 n,
          (ArithmeticFunction.vonMangoldt d * (n / d : ℕ) / (n : ℝ) +
            ArithmeticFunction.vonMangoldt d / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdPos : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hmod := Nat.mod_lt n hdPos
      have hdecomp := Nat.div_add_mod n d
      have hnd : n ≤ (n / d + 1) * d := by
        calc
          n = d * (n / d) + n % d := hdecomp.symm
          _ ≤ d * (n / d) + d := Nat.add_le_add_left hmod.le _
          _ = (n / d + 1) * d := by
            rw [Nat.add_mul, one_mul, Nat.mul_comm (n / d) d]
      have hfloor : (1 : ℝ) / d ≤
          ((n / d : ℕ) : ℝ) / n + 1 / n := by
        calc
          (1 : ℝ) / d ≤ ((n / d + 1 : ℕ) : ℝ) / n := by
            rw [div_le_div_iff₀ (by exact_mod_cast hdPos) (by exact_mod_cast hn)]
            norm_cast
            simpa only [one_mul] using hnd
          _ = ((n / d : ℕ) : ℝ) / n + 1 / n := by
            push_cast
            ring
      calc
        ArithmeticFunction.vonMangoldt d / (d : ℝ) =
            ArithmeticFunction.vonMangoldt d * (1 / (d : ℝ)) := by ring
        _ ≤ ArithmeticFunction.vonMangoldt d *
            (((n / d : ℕ) : ℝ) / n + 1 / n) :=
          mul_le_mul_of_nonneg_left hfloor ArithmeticFunction.vonMangoldt_nonneg
        _ = ArithmeticFunction.vonMangoldt d * (n / d : ℕ) / (n : ℝ) +
            ArithmeticFunction.vonMangoldt d / (n : ℝ) := by ring
    _ = (∑ d ∈ Ioc 0 n,
          ArithmeticFunction.vonMangoldt d * (n / d : ℕ)) / (n : ℝ) +
        Chebyshev.psi n / n := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
      congr 2
      simp [Chebyshev.psi]

private theorem log_sub_one_le_floorAverage {n : ℕ} (hn : 0 < n) :
    Real.log n - 1 ≤ mangoldtFloorAverage n := by
  have hsum := sum_Ioc_log_eq_mangoldt_floor n
  have hfactorial := sum_Ioc_log_eq_log_factorial n
  have hstirling := Stirling.le_log_factorial_stirling hn.ne'
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hbasic : (n : ℝ) * Real.log n - n ≤ Real.log n ! := by
    linarith
  unfold mangoldtFloorAverage
  rw [← hsum, hfactorial]
  apply (le_div_iff₀ (by exact_mod_cast hn)).2
  nlinarith

private theorem floorAverage_le_log {n : ℕ} (hn : 0 < n) :
    mangoldtFloorAverage n ≤ Real.log n := by
  have hsum := sum_Ioc_log_eq_mangoldt_floor n
  have hfactorial := sum_Ioc_log_eq_log_factorial n
  have hfacReal : (n ! : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hlogFac : Real.log (n ! : ℝ) ≤ Real.log ((n : ℝ) ^ n) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity) hfacReal
  rw [Real.log_pow] at hlogFac
  unfold mangoldtFloorAverage
  rw [← hsum, hfactorial]
  apply (div_le_iff₀ (by exact_mod_cast hn)).2
  nlinarith

theorem abs_mangoldtHarmonicSum_sub_log_le (n : ℕ) :
    |mangoldtHarmonicSum n - Real.log n| ≤ Real.log 4 + 4 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
      have hlog4 : (0 : ℝ) ≤ Real.log (4 : ℝ) :=
        Real.log_nonneg (by norm_num)
      linarith
    simpa [mangoldtHarmonicSum] using hC
  have hlowerFloor := log_sub_one_le_floorAverage hn
  have hupperFloor := floorAverage_le_log hn
  have hfloorLe := floorAverage_le_harmonic hn
  have hharmonicUpper := harmonic_le_floorAverage_add_psi hn
  have hpsi := Chebyshev.psi_le_const_mul_self
    (show (0 : ℝ) ≤ n by positivity)
  have hpsiDiv : Chebyshev.psi n / n ≤ Real.log 4 + 4 := by
    apply (div_le_iff₀ (by exact_mod_cast hn)).2
    simpa [mul_comm] using hpsi
  rw [abs_le]
  constructor
  · have hC : (1 : ℝ) ≤ Real.log 4 + 4 := by
      have hlog4 : (0 : ℝ) ≤ Real.log (4 : ℝ) :=
        Real.log_nonneg (by norm_num)
      linarith
    linarith
  · linarith

theorem exists_uniform_abs_mangoldtHarmonicSum_sub_log :
    ∃ C : ℝ, ∀ n : ℕ,
      |mangoldtHarmonicSum n - Real.log n| ≤ C :=
  ⟨Real.log 4 + 4, abs_mangoldtHarmonicSum_sub_log_le⟩

private theorem mangoldtHarmonicSum_eq_prime_add_nonprime (n : ℕ) :
    mangoldtHarmonicSum n =
      primeLogHarmonicSum n + nonprimeMangoldtHarmonicSum n := by
  classical
  unfold mangoldtHarmonicSum primeLogHarmonicSum
    nonprimeMangoldtHarmonicSum
  calc
    (∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / (d : ℝ)) =
        ∑ d ∈ Ioc 0 n,
          ((if d.Prime then ArithmeticFunction.vonMangoldt d else 0) / (d : ℝ) +
            (if d.Prime then 0 else ArithmeticFunction.vonMangoldt d) / (d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hp : d.Prime <;> simp [hp]
    _ = (∑ d ∈ Ioc 0 n,
          (if d.Prime then ArithmeticFunction.vonMangoldt d else 0) / (d : ℝ)) +
        ∑ d ∈ Ioc 0 n,
          (if d.Prime then 0 else ArithmeticFunction.vonMangoldt d) / (d : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      calc
        (∑ d ∈ Ioc 0 n,
            (if d.Prime then ArithmeticFunction.vonMangoldt d else 0) / (d : ℝ)) =
            ∑ p ∈ (Ioc 0 n).filter Nat.Prime,
              ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
          simp only [ite_div, zero_div, Finset.sum_filter]
        _ = ∑ p ∈ Nat.primesLE n,
              ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
          apply Finset.sum_congr
          · rw [Nat.primesLE_eq_filter_Icc_one]
            ext p
            simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
            constructor
            · rintro ⟨⟨hp, hpn⟩, hprime⟩
              exact ⟨⟨Nat.succ_le_iff.mpr hp, hpn⟩, hprime⟩
            · rintro ⟨⟨hp, hpn⟩, hprime⟩
              exact ⟨⟨Nat.succ_le_iff.mp hp, hpn⟩, hprime⟩
          · intro p hp
            rfl
        _ = ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [ArithmeticFunction.vonMangoldt_apply_prime
            (Nat.prime_of_mem_primesLE hp)]

private theorem summable_nonprimeMangoldtTerm :
    Summable fun n : ℕ =>
      (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) / (n : ℝ) := by
  letI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  have hcast : ∀ n : ℕ, (n : ZMod 1) = 0 :=
    fun n => Subsingleton.elim _ _
  simpa [ArithmeticFunction.vonMangoldt.residueClass, hcast] using
    (ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
      (0 : ZMod 1))

theorem exists_uniform_abs_primeLogHarmonicSum_sub_log :
    ∃ C : ℝ, ∀ n : ℕ,
      |primeLogHarmonicSum n - Real.log n| ≤ C := by
  let f : ℕ → ℝ := fun d =>
    (if d.Prime then 0 else ArithmeticFunction.vonMangoldt d) / (d : ℝ)
  refine ⟨Real.log 4 + 4 + ∑' d : ℕ, f d, fun n => ?_⟩
  have hfNonneg (d : ℕ) : 0 ≤ f d := by
    unfold f
    split_ifs <;> positivity
  have hfSummable : Summable f := summable_nonprimeMangoldtTerm
  have hnonprimeNonneg : 0 ≤ nonprimeMangoldtHarmonicSum n := by
    change 0 ≤ ∑ d ∈ Ioc 0 n, f d
    exact Finset.sum_nonneg fun d hd => hfNonneg d
  have hnonprimeLe : nonprimeMangoldtHarmonicSum n ≤ ∑' d : ℕ, f d := by
    change (∑ d ∈ Ioc 0 n, f d) ≤ ∑' d : ℕ, f d
    exact hfSummable.sum_le_tsum (Ioc 0 n) fun d hd => hfNonneg d
  have hsplit := mangoldtHarmonicSum_eq_prime_add_nonprime n
  have heq : primeLogHarmonicSum n - Real.log n =
      (mangoldtHarmonicSum n - Real.log n) -
        nonprimeMangoldtHarmonicSum n := by
    rw [hsplit]
    ring
  rw [heq]
  calc
    |(mangoldtHarmonicSum n - Real.log n) -
        nonprimeMangoldtHarmonicSum n| ≤
        |mangoldtHarmonicSum n - Real.log n| +
          |nonprimeMangoldtHarmonicSum n| := abs_sub _ _
    _ ≤ (Real.log 4 + 4) + (∑' d : ℕ, f d) := by
      apply add_le_add (abs_mangoldtHarmonicSum_sub_log_le n)
      rwa [abs_of_nonneg hnonprimeNonneg]

end BoundedGaps.Maynard
