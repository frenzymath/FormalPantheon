import Waring.Analytic.ChenTenExceptionalFactors
import Waring.Analytic.ChenTenGenericProduct

/-!
# A positive global Euler product for Chen's singular series

The checked lower bounds for Chen's seven special primes and the aggregate
generic-prime estimate give a uniform `3/40` lower bound for every finite
Euler product.  Passing to the already constructed real Euler product proves
the same lower bound for the singular series
[CHEN1964-EN, pp. 1565-1567, equations (37)-(41);
CHEN1964-ZH, pp. 731-733, equations (27)-(31)].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The lower envelope used for Chen's seven special local factors. -/
noncomputable def chenTenExceptionalLower (p : Nat) : Real :=
  if p = 5 then 9 / 10
  else if p = 11 then 1 / 2
  else if p = 31 then 3 / 4
  else if p = 41 then 19 / 20
  else if p = 61 then 99 / 100
  else if p = 71 then 899 / 900
  else if p = 101 then 999 / 1000
  else 1

/-- Every value of the exceptional lower envelope is nonnegative. -/
theorem chenTenExceptionalLower_nonneg (p : Nat) :
    0 <= chenTenExceptionalLower p := by
  simp [chenTenExceptionalLower]
  split_ifs <;> norm_num

/-- Every value of the exceptional lower envelope is at most one. -/
theorem chenTenExceptionalLower_le_one (p : Nat) :
    chenTenExceptionalLower p <= 1 := by
  simp [chenTenExceptionalLower]
  split_ifs <;> norm_num

/-- The product of all seven checked exceptional lower bounds exceeds
`3/10`. -/
theorem three_tenths_le_prod_chenTenExceptionalLower :
    (3 : Real) / 10 <=
      ∏ p ∈ chenTwoSpecialPrimes, chenTenExceptionalLower p := by
  norm_num [chenTwoSpecialPrimes, chenTwoExceptionalPrimes,
    chenTenExceptionalLower, Finset.prod_insert]

/-- On the special set, the lower envelope is bounded by the real local
factor. -/
theorem chenTenExceptionalLower_le_localFactor
    (p : Nat.Primes) (hmem : p.1 ∈ chenTwoSpecialPrimes) (N : Nat) :
    chenTenExceptionalLower p.1 <=
      (chenTenPrimeLocalFactor p.1 N).re := by
  simp only [chenTwoSpecialPrimes, chenTwoExceptionalPrimes,
    Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h
  · rw [show p = ⟨5, by decide⟩ by exact Subtype.ext h]
    simpa [chenTenExceptionalLower] using
      nine_tenths_le_chenTenPrimeLocalFactor_five_re N
  · rw [show p = ⟨11, by decide⟩ by exact Subtype.ext h]
    simpa [chenTenExceptionalLower] using
      one_half_le_chenTenPrimeLocalFactor_eleven_re N
  · rw [show p = ⟨31, by decide⟩ by exact Subtype.ext h]
    simpa [chenTenExceptionalLower] using
      three_fourths_le_chenTenPrimeLocalFactor_31_re N
  · rw [show p = ⟨41, by decide⟩ by exact Subtype.ext h]
    simpa [chenTenExceptionalLower] using
      nineteen_twentieths_le_chenTenPrimeLocalFactor_41_re N
  · rw [show p = ⟨61, by decide⟩ by exact Subtype.ext h]
    simpa [chenTenExceptionalLower] using
      ninety_nine_hundredths_le_chenTenPrimeLocalFactor_61_re N
  · rw [show p = ⟨71, by decide⟩ by exact Subtype.ext h]
    simpa [chenTenExceptionalLower] using
      eight_hundred_ninety_ninths_le_chenTenPrimeLocalFactor_71_re N
  · rw [show p = ⟨101, by decide⟩ by exact Subtype.ext h]
    simpa [chenTenExceptionalLower] using
      nine_hundred_ninety_ninths_le_chenTenPrimeLocalFactor_101_re N

/-- Every finite product drawn from the seven special primes is bounded below
by `3/10`; omitting a lower-envelope factor can only increase its product. -/
theorem three_tenths_le_prod_chenTenPrimeLocalFactor_re_special
    (s : Finset Nat.Primes)
    (hspecial : ∀ p, p ∈ s -> p.1 ∈ chenTwoSpecialPrimes) (N : Nat) :
    (3 : Real) / 10 <=
      ∏ p ∈ s, (chenTenPrimeLocalFactor p.1 N).re := by
  have hsubset :
      s.image (fun p : Nat.Primes => p.1) ⊆ chenTwoSpecialPrimes := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact hspecial p hp
  have hlowerSubset :
      (∏ p ∈ chenTwoSpecialPrimes, chenTenExceptionalLower p) <=
        ∏ p ∈ s, chenTenExceptionalLower p.1 := by
    calc
      (∏ p ∈ chenTwoSpecialPrimes, chenTenExceptionalLower p) <=
          ∏ p ∈ s.image (fun p : Nat.Primes => p.1),
            chenTenExceptionalLower p := by
        apply Finset.prod_le_prod_of_subset_of_le_one hsubset
        · intro p _hp
          exact chenTenExceptionalLower_nonneg p
        · intro p _hp _hnot
          exact chenTenExceptionalLower_le_one p
      _ = ∏ p ∈ s, chenTenExceptionalLower p.1 :=
        Finset.prod_image Subtype.val_injective.injOn
  have hpointwise :
      (∏ p ∈ s, chenTenExceptionalLower p.1) <=
        ∏ p ∈ s, (chenTenPrimeLocalFactor p.1 N).re := by
    apply Finset.prod_le_prod
    · intro p _hp
      exact chenTenExceptionalLower_nonneg p.1
    · intro p hp
      exact chenTenExceptionalLower_le_localFactor p (hspecial p hp) N
  exact three_tenths_le_prod_chenTenExceptionalLower.trans
    (hlowerSubset.trans hpointwise)

/-- Every finite product of real local factors has the uniform lower bound
`3/40`. -/
theorem three_fortieths_le_prod_chenTenPrimeLocalFactor_re
    (s : Finset Nat.Primes) (N : Nat) :
    (3 : Real) / 40 <=
      ∏ p ∈ s, (chenTenPrimeLocalFactor p.1 N).re := by
  classical
  let special := s.filter (fun p : Nat.Primes =>
    p.1 ∈ chenTwoSpecialPrimes)
  let generic := s.filter (fun p : Nat.Primes =>
    p.1 ∉ chenTwoSpecialPrimes)
  have hgeneric : (1 : Real) / 4 <=
      ∏ p ∈ generic, (chenTenPrimeLocalFactor p.1 N).re := by
    apply one_fourth_le_prod_chenTenPrimeLocalFactor_re_generic
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hspecial : (3 : Real) / 10 <=
      ∏ p ∈ special, (chenTenPrimeLocalFactor p.1 N).re := by
    apply three_tenths_le_prod_chenTenPrimeLocalFactor_re_special
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsplit := Finset.prod_filter_not_mul_prod_filter s
    (fun p : Nat.Primes => p.1 ∈ chenTwoSpecialPrimes)
    (fun p : Nat.Primes => (chenTenPrimeLocalFactor p.1 N).re)
  calc
    (3 : Real) / 40 = (1 / 4 : Real) * (3 / 10 : Real) := by norm_num
    _ <= (∏ p ∈ generic, (chenTenPrimeLocalFactor p.1 N).re) *
        ∏ p ∈ special, (chenTenPrimeLocalFactor p.1 N).re := by
      exact mul_le_mul hgeneric hspecial (by norm_num) (by linarith [hgeneric])
    _ = ∏ p ∈ s, (chenTenPrimeLocalFactor p.1 N).re := by
      simpa [special, generic] using hsplit

/-- Chen's singular series has the explicit checked lower bound `3/40`. -/
theorem three_fortieths_le_chenTenSingularSeries_re (N : Nat) :
    (3 : Real) / 40 <= (chenTenSingularSeries N).re := by
  exact ge_of_tendsto (hasProd_chenTenPrimeLocalFactor_re N)
    (Filter.Eventually.of_forall fun s =>
      three_fortieths_le_prod_chenTenPrimeLocalFactor_re s N)

/-- In particular, Chen's singular series has positive real part. -/
theorem chenTenSingularSeries_re_pos (N : Nat) :
    0 < (chenTenSingularSeries N).re :=
  (by norm_num : (0 : Real) < 3 / 40).trans_le
    (three_fortieths_le_chenTenSingularSeries_re N)

/-- Chen's singular series is therefore nonzero. -/
theorem chenTenSingularSeries_ne_zero (N : Nat) :
    chenTenSingularSeries N ≠ 0 := by
  intro hzero
  have hpos := chenTenSingularSeries_re_pos N
  rw [hzero] at hpos
  norm_num at hpos

/-- Removing the three spurious integer defects in the generic comparison
raises the global lower bound to `9/80`. -/
theorem nine_eightieths_le_prod_chenTenPrimeLocalFactor_re
    (s : Finset Nat.Primes) (N : Nat) :
    (9 : Real) / 80 <=
      ∏ p ∈ s, (chenTenPrimeLocalFactor p.1 N).re := by
  classical
  let special := s.filter (fun p : Nat.Primes =>
    p.1 ∈ chenTwoSpecialPrimes)
  let generic := s.filter (fun p : Nat.Primes =>
    p.1 ∉ chenTwoSpecialPrimes)
  have hgeneric : (3 : Real) / 8 <=
      ∏ p ∈ generic, (chenTenPrimeLocalFactor p.1 N).re := by
    apply three_eighths_le_prod_chenTenPrimeLocalFactor_re_generic
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hspecial : (3 : Real) / 10 <=
      ∏ p ∈ special, (chenTenPrimeLocalFactor p.1 N).re := by
    apply three_tenths_le_prod_chenTenPrimeLocalFactor_re_special
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsplit := Finset.prod_filter_not_mul_prod_filter s
    (fun p : Nat.Primes => p.1 ∈ chenTwoSpecialPrimes)
    (fun p : Nat.Primes => (chenTenPrimeLocalFactor p.1 N).re)
  calc
    (9 : Real) / 80 = (3 / 8 : Real) * (3 / 10 : Real) := by norm_num
    _ <= (∏ p ∈ generic, (chenTenPrimeLocalFactor p.1 N).re) *
        ∏ p ∈ special, (chenTenPrimeLocalFactor p.1 N).re := by
      exact mul_le_mul hgeneric hspecial (by norm_num) (by linarith [hgeneric])
    _ = ∏ p ∈ s, (chenTenPrimeLocalFactor p.1 N).re := by
      simpa [special, generic] using hsplit

/-- Chen's singular series has the sharpened lower bound `9/80`. -/
theorem nine_eightieths_le_chenTenSingularSeries_re (N : Nat) :
    (9 : Real) / 80 <= (chenTenSingularSeries N).re := by
  exact ge_of_tendsto (hasProd_chenTenPrimeLocalFactor_re N)
    (Filter.Eventually.of_forall fun s =>
      nine_eightieths_le_prod_chenTenPrimeLocalFactor_re s N)

end Waring.Analytic
