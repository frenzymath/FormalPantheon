import PrimesRestrictedDigits.BasicEstimates.PrimeCountingBridge
import PrimesRestrictedDigits.BasicEstimates.RoughNumbers

/-!
# The finite Buchstab count on the base range

This is the exact finite input behind `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7,
Eq. (7.35).  Above the square-root threshold, the only non-prime counted
integer other than one can be the closed-endpoint prime square.
-/

namespace PrimesRestrictedDigits

/-- On the base range, the rough count differs from the weak prime-count
difference by at most three.  The three possible contributions are one, the
lower prime endpoint, and the closed-endpoint prime square. -/
theorem abs_buchstabPhi_sub_prime_counts_le_three
    {x y : Real} (hy : 2 <= y) (hroot : Real.sqrt x <= y)
    (hyx : y <= x) :
    |(buchstabPhi x y : Real) -
        (realPrimeCounting x - realPrimeCounting y)| <= 3 := by
  classical
  let primes := Nat.primesLE (Nat.floor x) \ Nat.primesLE (Nat.floor y)
  let rough := buchstabRoughNumbers x y
  have hy0 : 0 <= y := by linarith
  have hx0 : 0 <= x := hy0.trans hyx
  have hprimeSubset :
      Nat.primesLE (Nat.floor y) ⊆ Nat.primesLE (Nat.floor x) :=
    Nat.primesLE_mono (Nat.floor_mono hyx)
  have hprimesCard : (primes.card : Real) =
      realPrimeCounting x - realPrimeCounting y := by
    dsimp [primes, realPrimeCounting]
    rw [Finset.card_sdiff_of_subset hprimeSubset,
      Nat.cast_sub (Finset.card_mono hprimeSubset)]
    simp
  have hprimesRough : primes ⊆ rough := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
    have hpPrime : p.Prime := hp.1.2
    have hpx : (p : Real) <= x :=
      (Nat.le_floor_iff hx0).mp hp.1.1
    have hfloorYp : Nat.floor y < p := by
      apply lt_of_not_ge
      intro hpFloor
      exact hp.2 (Nat.mem_primesLE.mpr <| And.intro hpFloor hpPrime)
    have hyp : y <= (p : Real) :=
      (Nat.floor_lt hy0).mp hfloorYp |>.le
    rw [mem_buchstabRoughNumbers]
    refine ⟨hpPrime.one_le, hpx, ?_⟩
    intro q hq hqp
    have hqpEq : q = p := (Nat.prime_dvd_prime_iff_eq hq hpPrime).mp hqp
    simpa [hqpEq] using hyp
  have hroughDiffSubset : rough \ primes ⊆
      ({1, Nat.floor y, Nat.floor x} : Finset Nat) := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    have hnRough := hn.1
    rw [mem_buchstabRoughNumbers] at hnRough
    by_cases hnOne : n = 1
    · simp [hnOne]
    by_cases hnPrime : n.Prime
    · have hnFloorX : n <= Nat.floor x :=
        (Nat.le_floor_iff hx0).mpr hnRough.2.1
      have hnPrimesX : n ∈ Nat.primesLE (Nat.floor x) :=
        Nat.mem_primesLE.mpr ⟨hnFloorX, hnPrime⟩
      have hnPrimesY : n ∈ Nat.primesLE (Nat.floor y) := by
        by_contra hnPrimesY
        exact hn.2 (Finset.mem_sdiff.mpr ⟨hnPrimesX, hnPrimesY⟩)
      have hnFloorY : n <= Nat.floor y := (Nat.mem_primesLE.mp hnPrimesY).1
      have hfloorYReal : (Nat.floor y : Real) <= y := Nat.floor_le hy0
      have hnEq : n = Nat.floor y := by
        exact_mod_cast le_antisymm (by exact_mod_cast hnFloorY)
          (hfloorYReal.trans (hnRough.2.2 n hnPrime dvd_rfl))
      simp [hnEq]
    · have hnPos : 0 < n := hnRough.1
      have hminPrime : n.minFac.Prime := Nat.minFac_prime hnOne
      have hyMin : y <= (n.minFac : Real) :=
        hnRough.2.2 n.minFac hminPrime (Nat.minFac_dvd n)
      have hminSq : n.minFac ^ 2 <= n :=
        Nat.minFac_sq_le_self hnPos hnPrime
      have hxySq : x <= y ^ 2 := by
        nlinarith [Real.sq_sqrt hx0, Real.sqrt_nonneg x]
      have hySqMin : y ^ 2 <= (n.minFac : Real) ^ 2 := by
        nlinarith [hminPrime.pos, hyMin]
      have hnEqX : (n : Real) = x := by
        have hminSqReal : ((n.minFac ^ 2 : Nat) : Real) <= (n : Real) := by
          exact_mod_cast hminSq
        norm_num [Nat.cast_pow] at hminSqReal
        nlinarith [hnRough.2.1]
      have hnFloorX : n = Nat.floor x := by
        rw [← hnEqX]
        simp
      simp [hnFloorX]
  have hdiffCard : (rough \ primes).card <= 3 :=
    (Finset.card_le_card hroughDiffSubset).trans Finset.card_le_three
  have hcardLower : primes.card <= rough.card :=
    Finset.card_le_card hprimesRough
  have hcardUpper : rough.card <= primes.card + 3 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hprimesRough
    omega
  have hcardLowerReal : (primes.card : Real) <= rough.card := by
    exact_mod_cast hcardLower
  have hcardUpperReal : (rough.card : Real) <= primes.card + 3 := by
    exact_mod_cast hcardUpper
  change |(rough.card : Real) -
      (realPrimeCounting x - realPrimeCounting y)| <= 3
  rw [← hprimesCard, abs_of_nonneg (sub_nonneg.mpr hcardLowerReal)]
  linarith

end PrimesRestrictedDigits
