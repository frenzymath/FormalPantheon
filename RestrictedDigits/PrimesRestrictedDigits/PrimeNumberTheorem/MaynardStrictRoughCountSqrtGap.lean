import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The square-root strict/weak endpoint gap

At the square-root cutoff, a weakly rough integer which is not strictly rough can only be the
prime equal to the square root. This gives the finite endpoint correction needed when the weak
Buchstab asymptotic is combined with the strict carrier in the Section 6 prime identity.

Source: `MAYNARD-PRD-PUBLISHED`, Section 5, Eq. (5.2), and the strict carrier convention in
Section 6.
-/

namespace PrimesRestrictedDigits

/- The weak-minus-strict carrier has at most one element. -/
theorem maynardRoughCarrier_sdiff_strict_sqrt_card_le_one
    {X : Real} (hX : 4 ≤ X) :
    (maynardRoughCarrier X (Real.sqrt X) \
      maynardStrictRoughCarrier X (Real.sqrt X)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro n hn m hm
  have hnD := Finset.mem_sdiff.mp hn
  have hmD := Finset.mem_sdiff.mp hm
  have hnW := mem_maynardRoughCarrier.mp hnD.1
  have hmW := mem_maynardRoughCarrier.mp hmD.1
  have hnNotS := hnD.2
  have hmNotS := hmD.2
  have hX0 : 0 ≤ X := by linarith
  have strictOne : 1 ∈ maynardStrictRoughCarrier X (Real.sqrt X) := by
    rw [mem_maynardStrictRoughCarrier]
    refine ⟨by norm_num, by norm_num; linarith, ?_⟩
    intro p hp hpd
    exact (hp.not_dvd_one hpd).elim
  have classify : ∀ {r : Nat},
      1 ≤ r -> (r : Real) < X -> r ≠ 1 ->
      (∀ p, p.Prime -> p ∣ r -> Real.sqrt X ≤ (p : Real)) ->
      r.Prime := by
    intro r hr1 hrX hrne hrough
    by_contra hrprime
    have hrpos : 0 < r := by omega
    have hqprime : r.minFac.Prime := Nat.minFac_prime hrne
    have hqrough : Real.sqrt X ≤ (r.minFac : Real) :=
      hrough r.minFac hqprime (Nat.minFac_dvd r)
    have hqsqNat : r.minFac ^ 2 ≤ r :=
      Nat.minFac_sq_le_self hrpos hrprime
    have hqsqReal : (r.minFac : Real) ^ 2 ≤ (r : Real) := by
      exact_mod_cast hqsqNat
    have hsqrtSq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX0
    have hXle : X ≤ (r.minFac : Real) ^ 2 := by
      nlinarith [Real.sqrt_nonneg X]
    have : X ≤ (r : Real) := hXle.trans hqsqReal
    linarith
  have hnOne : n ≠ 1 := by
    intro hn1
    subst n
    exact hnNotS strictOne
  have hmOne : m ≠ 1 := by
    intro hm1
    subst m
    exact hmNotS strictOne
  have hnprime : n.Prime :=
    classify hnW.1 hnW.2.1 hnOne hnW.2.2
  have hmprime : m.Prime :=
    classify hmW.1 hmW.2.1 hmOne hmW.2.2
  have hnle : Real.sqrt X ≤ (n : Real) := hnW.2.2 n hnprime dvd_rfl
  have hnnotlt : ¬ Real.sqrt X < (n : Real) := by
    intro hlt
    apply hnNotS
    rw [mem_maynardStrictRoughCarrier]
    refine ⟨hnW.1, hnW.2.1, ?_⟩
    intro p hp hpd
    have hpEq : p = n := (Nat.prime_dvd_prime_iff_eq hp hnprime).mp hpd
    subst p
    exact hlt
  have hnEq : Real.sqrt X = (n : Real) :=
    le_antisymm hnle (le_of_not_gt hnnotlt)
  have hmle : Real.sqrt X ≤ (m : Real) := hmW.2.2 m hmprime dvd_rfl
  have hmnotlt : ¬ Real.sqrt X < (m : Real) := by
    intro hlt
    apply hmNotS
    rw [mem_maynardStrictRoughCarrier]
    refine ⟨hmW.1, hmW.2.1, ?_⟩
    intro p hp hpd
    have hpEq : p = m := (Nat.prime_dvd_prime_iff_eq hp hmprime).mp hpd
    subst p
    exact hlt
  have hmEq : Real.sqrt X = (m : Real) :=
    le_antisymm hmle (le_of_not_gt hmnotlt)
  exact_mod_cast hnEq.symm.trans hmEq

/- The finite-set identity turns the endpoint cardinality into a count bound. -/
theorem maynardRoughCount_sqrt_le_strict_add_one
    {X : Real} (hX : 4 ≤ X) :
    maynardRoughCount X (Real.sqrt X) ≤
      maynardStrictRoughCount X (Real.sqrt X) + 1 := by
  rw [maynardRoughCount, maynardStrictRoughCount]
  have hsubset := maynardStrictRoughCarrier_subset_maynardRoughCarrier
    X (Real.sqrt X)
  have hcard := Finset.card_sdiff_add_card_eq_card hsubset
  have hdiff := maynardRoughCarrier_sdiff_strict_sqrt_card_le_one hX
  omega

end PrimesRestrictedDigits
