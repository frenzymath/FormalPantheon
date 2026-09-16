import Waring.Analytic.ChenTenGenericLocalFactor
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The aggregate generic-prime product

An elementary finite-product inequality and an exact telescoping series give
a uniform lower bound for every finite product of Chen's generic local factors.
This replaces the logarithmic estimates in [CHEN1964-EN, pp. 1566-1567,
equations (40)-(41); CHEN1964-ZH, pp. 732-733, equations (30)-(31)].
-/

namespace Waring.Analytic

/-- The comparison defect for a generic local factor. -/
noncomputable def chenTenGenericDefect (m : Nat) : Real :=
  1 / ((m : Real) ^ 2 - 1)

/-- Products of numbers `1 - delta_i` dominate `1 - sum delta_i` when all
defects lie in the unit interval. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι)
    (delta : ι -> Real) (hzero : ∀ i, i ∈ s -> 0 <= delta i)
    (hone : ∀ i, i ∈ s -> delta i <= 1) :
    1 - ∑ i ∈ s, delta i <= ∏ i ∈ s, (1 - delta i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hsum : 0 <= ∑ i ∈ s, delta i :=
        Finset.sum_nonneg fun i hi => hzero i (Finset.mem_insert_of_mem hi)
      have hdelta : 0 <= delta a := hzero a (by simp)
      have hfactor : 0 <= 1 - delta a := sub_nonneg.mpr (hone a (by simp))
      have hind : 1 - ∑ i ∈ s, delta i <= ∏ i ∈ s, (1 - delta i) :=
        ih (fun i hi => hzero i (Finset.mem_insert_of_mem hi))
          (fun i hi => hone i (Finset.mem_insert_of_mem hi))
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      calc
        1 - (delta a + ∑ i ∈ s, delta i) <=
            (1 - ∑ i ∈ s, delta i) * (1 - delta a) := by
          nlinarith [mul_nonneg hsum hdelta]
        _ <= (∏ i ∈ s, (1 - delta i)) * (1 - delta a) :=
          mul_le_mul_of_nonneg_right hind hfactor
        _ = (1 - delta a) * ∏ i ∈ s, (1 - delta i) := by ring

/-- Comparison defects are nonnegative from the first relevant index onward. -/
theorem chenTenGenericDefect_nonneg {m : Nat} (hm : 2 <= m) :
    0 <= chenTenGenericDefect m := by
  have hmReal : (2 : Real) <= m := by exact_mod_cast hm
  have hdenom : (0 : Real) < (m : Real) ^ 2 - 1 := by nlinarith
  unfold chenTenGenericDefect
  positivity

/-- One summand has the partial-fraction form used in the telescoping sum. -/
theorem chenTenGenericDefect_add_two (n : Nat) :
    chenTenGenericDefect (n + 2) =
      1 / (2 * ((n + 1 : Nat) : Real)) -
        1 / (2 * ((n + 3 : Nat) : Real)) := by
  have hn1 : (0 : Real) < (n + 1 : Nat) := by positivity
  have hn3 : (0 : Real) < (n + 3 : Nat) := by positivity
  have hdenom : (0 : Real) < ((n + 2 : Nat) : Real) ^ 2 - 1 := by
    have : (2 : Real) <= (n + 2 : Nat) := by
      exact_mod_cast (show 2 <= n + 2 by omega)
    nlinarith
  unfold chenTenGenericDefect
  field_simp [ne_of_gt hn1, ne_of_gt hn3, ne_of_gt hdenom]
  push_cast
  ring

/-- The finite comparison series telescopes exactly. -/
theorem sum_range_chenTenGenericDefect (n : Nat) :
    (∑ k ∈ Finset.range n, chenTenGenericDefect (k + 2)) =
      3 / 4 - 1 / (2 * ((n + 1 : Nat) : Real)) -
        1 / (2 * ((n + 2 : Nat) : Real)) := by
  induction n with
  | zero => norm_num [chenTenGenericDefect]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, chenTenGenericDefect_add_two]
      push_cast
      ring

/-- The shifted comparison defects sum to `3/4`. -/
theorem hasSum_chenTenGenericDefect :
    HasSum (fun k : Nat => chenTenGenericDefect (k + 2)) (3 / 4) := by
  have hnonneg : ∀ k : Nat, 0 <= chenTenGenericDefect (k + 2) := by
    intro k
    exact chenTenGenericDefect_nonneg (by omega)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  simp_rw [sum_range_chenTenGenericDefect]
  have hden1 : Filter.Tendsto
      (fun n : Nat => (2 : Real) * ((n + 1 : Nat) : Real))
    Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => by
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hn : (0 : Real) <= n := Nat.cast_nonneg n
      nlinarith) tendsto_natCast_atTop_atTop
  have hden2 : Filter.Tendsto
      (fun n : Nat => (2 : Real) * ((n + 2 : Nat) : Real))
    Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have hn : (0 : Real) <= n := Nat.cast_nonneg n
      nlinarith) tendsto_natCast_atTop_atTop
  have hlimit := ((hden1.const_div_atTop (1 : Real)).add
    (hden2.const_div_atTop (1 : Real))).const_sub (3 / 4 : Real)
  convert hlimit using 1
  · funext n
    push_cast
    ring
  · norm_num

/-- Every finite sum of prime comparison defects is at most `3/4`. -/
theorem sum_chenTenGenericDefect_primes_le (s : Finset Nat.Primes) :
    (∑ p ∈ s, chenTenGenericDefect p.1) <= 3 / 4 := by
  let shift : Nat.Primes -> Nat := fun p => p.1 - 2
  have hshift : Function.Injective shift := by
    intro p q hpq
    apply Subtype.ext
    dsimp [shift] at hpq
    have hpTwo : 2 <= p.1 := p.2.two_le
    have hqTwo : 2 <= q.1 := q.2.two_le
    omega
  let f : Nat -> Real := fun k => chenTenGenericDefect (k + 2)
  have hf : Summable f := hasSum_chenTenGenericDefect.summable
  have hfNonneg : ∀ k, 0 <= f k := by
    intro k
    exact chenTenGenericDefect_nonneg (by omega)
  have hcomp : Summable (f ∘ shift) := hf.comp_injective hshift
  calc
    (∑ p ∈ s, chenTenGenericDefect p.1) = ∑ p ∈ s, (f ∘ shift) p := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp only [Function.comp_apply, f, shift]
      rw [Nat.sub_add_cancel p.2.two_le]
    _ <= ∑' p : Nat.Primes, (f ∘ shift) p :=
      hcomp.sum_le_tsum s (fun p _hp => hfNonneg (shift p))
    _ <= ∑' k : Nat, f k :=
      tsum_comp_le_tsum_of_inj hf hfNonneg hshift
    _ = 3 / 4 := hasSum_chenTenGenericDefect.tsum_eq

/-- A generic prime defect is at most one third. -/
theorem chenTenGenericDefect_prime_le_one_third (p : Nat.Primes) :
    chenTenGenericDefect p.1 <= 1 / 3 := by
  have hpTwo : (2 : Real) <= p.1 := by exact_mod_cast p.2.two_le
  have hdenom : (3 : Real) <= (p.1 : Real) ^ 2 - 1 := by nlinarith
  unfold chenTenGenericDefect
  exact one_div_le_one_div_of_le (by norm_num) hdenom

/-- Every finite product of the generic lower factors is at least `1/4`. -/
theorem one_fourth_le_prod_generic_lower (s : Finset Nat.Primes) :
    1 / 4 <= ∏ p ∈ s, (1 - chenTenGenericDefect p.1) := by
  have hsum := sum_chenTenGenericDefect_primes_le s
  have hprod := one_sub_sum_le_prod_one_sub s
    (fun p : Nat.Primes => chenTenGenericDefect p.1)
    (fun p _hp => chenTenGenericDefect_nonneg p.2.two_le)
    (fun p _hp => (chenTenGenericDefect_prime_le_one_third p).trans (by norm_num))
  linarith

/-- The complex Euler product, whose factors are real, induces a real
`HasProd` with limit the real part of the singular series. -/
theorem hasProd_chenTenPrimeLocalFactor_re (N : Nat) :
    HasProd (fun p : Nat.Primes => (chenTenPrimeLocalFactor p.1 N).re)
      (chenTenSingularSeries N).re := by
  have hcomplex : HasProd
      (Complex.ofRealHom ∘
        fun p : Nat.Primes => (chenTenPrimeLocalFactor p.1 N).re)
      (Complex.ofRealHom (chenTenSingularSeries N).re) := by
    convert hasProd_chenTenPrimeLocalFactor N using 1
    · funext p
      apply Complex.ext
      · simp
      · simp [chenTenPrimeLocalFactor_im_eq_zero]
    · apply Complex.ext
      · simp
      · simp [chenTenSingularSeries_im_eq_zero]
  exact (Complex.isometry_ofReal.isEmbedding.isInducing.hasProd_iff
    (fun p : Nat.Primes => (chenTenPrimeLocalFactor p.1 N).re)
    (chenTenSingularSeries N).re).mp hcomplex

/-- Every finite product of generic Chen local factors is at least `1/4`. -/
theorem one_fourth_le_prod_chenTenPrimeLocalFactor_re_generic
    (s : Finset Nat.Primes)
    (hgeneric : ∀ p, p ∈ s -> p.1 ∉ chenTwoSpecialPrimes) (N : Nat) :
    1 / 4 <= ∏ p ∈ s, (chenTenPrimeLocalFactor p.1 N).re := by
  have hlower := one_fourth_le_prod_generic_lower s
  apply hlower.trans
  apply Finset.prod_le_prod
  · intro p hp
    have hthird := chenTenGenericDefect_prime_le_one_third p
    linarith
  · intro p hp
    simpa [chenTenGenericDefect] using
      chenTenPrimeLocalFactor_re_lower_generic p.2 (hgeneric p hp) N

/-- Once the exceptional prime `5` and the nonprimes `4,6` are removed, the
generic prime defects have total at most `5/8`. -/
theorem sum_chenTenGenericDefect_primes_le_five_eighths
    (s : Finset Nat.Primes)
    (hgeneric : ∀ p, p ∈ s -> p.1 ∉ chenTwoSpecialPrimes) :
    (∑ p ∈ s, chenTenGenericDefect p.1) <= 5 / 8 := by
  let shift : Nat.Primes -> Nat := fun p => p.1 - 2
  have hshift : Function.Injective shift := by
    intro p q hpq
    apply Subtype.ext
    dsimp [shift] at hpq
    have hpTwo : 2 <= p.1 := p.2.two_le
    have hqTwo : 2 <= q.1 := q.2.two_le
    omega
  let f : Nat -> Real := fun k => chenTenGenericDefect (k + 2)
  have hf : Summable f := hasSum_chenTenGenericDefect.summable
  have hfNonneg : ∀ k, 0 <= f k := by
    intro k
    exact chenTenGenericDefect_nonneg (by omega)
  let excluded : Finset Nat := {2, 3, 4}
  have havoid : Disjoint (s.image shift) excluded := by
    rw [Finset.disjoint_left]
    intro k hkImage hkExcluded
    obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hkImage
    simp only [excluded, Finset.mem_insert, Finset.mem_singleton] at hkExcluded
    have hpTwo := p.2.two_le
    rcases hkExcluded with rfl | rfl | rfl
    · have hpval : p.1 = 4 := by
        dsimp [shift] at hpk
        omega
      have hprime : Nat.Prime 4 := hpval ▸ p.2
      exact (by decide : ¬ Nat.Prime 4) hprime
    · have hpval : p.1 = 5 := by
        dsimp [shift] at hpk
        omega
      have hnot := hgeneric p hp
      rw [hpval] at hnot
      simp [chenTwoSpecialPrimes, chenTwoExceptionalPrimes] at hnot
    · have hpval : p.1 = 6 := by
        dsimp [shift] at hpk
        omega
      have hprime : Nat.Prime 6 := hpval ▸ p.2
      exact (by decide : ¬ Nat.Prime 6) hprime
  have htotal := hf.sum_le_tsum (s.image shift ∪ excluded)
    (fun k _hk => hfNonneg k)
  rw [Finset.sum_union havoid] at htotal
  have hrewrite :
      (∑ p ∈ s, chenTenGenericDefect p.1) =
        ∑ k ∈ s.image shift, f k := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      dsimp [f, shift]
      rw [Nat.sub_add_cancel p.2.two_le]
    · exact hshift.injOn
  have hexcluded : (∑ k ∈ excluded, f k) = (23 / 168 : Real) := by
    norm_num [excluded, f, chenTenGenericDefect]
  rw [← hrewrite, hexcluded, hasSum_chenTenGenericDefect.tsum_eq] at htotal
  linarith

/-- The sharpened generic finite product lower bound. -/
theorem three_eighths_le_prod_generic_lower_of_generic
    (s : Finset Nat.Primes)
    (hgeneric : ∀ p, p ∈ s -> p.1 ∉ chenTwoSpecialPrimes) :
    3 / 8 <= ∏ p ∈ s, (1 - chenTenGenericDefect p.1) := by
  have hsum :=
    sum_chenTenGenericDefect_primes_le_five_eighths s hgeneric
  have hprod := one_sub_sum_le_prod_one_sub s
    (fun p : Nat.Primes => chenTenGenericDefect p.1)
    (fun p _hp => chenTenGenericDefect_nonneg p.2.two_le)
    (fun p _hp => (chenTenGenericDefect_prime_le_one_third p).trans (by norm_num))
  linarith

/-- Every finite product of generic local factors is at least `3/8`. -/
theorem three_eighths_le_prod_chenTenPrimeLocalFactor_re_generic
    (s : Finset Nat.Primes)
    (hgeneric : ∀ p, p ∈ s -> p.1 ∉ chenTwoSpecialPrimes) (N : Nat) :
    3 / 8 <= ∏ p ∈ s, (chenTenPrimeLocalFactor p.1 N).re := by
  have hlower := three_eighths_le_prod_generic_lower_of_generic s hgeneric
  apply hlower.trans
  apply Finset.prod_le_prod
  · intro p hp
    have hthird := chenTenGenericDefect_prime_le_one_third p
    linarith
  · intro p hp
    simpa [chenTenGenericDefect] using
      chenTenPrimeLocalFactor_re_lower_generic p.2 (hgeneric p hp) N

end Waring.Analytic
