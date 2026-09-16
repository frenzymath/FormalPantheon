import PrimesRestrictedDigits.BasicEstimates.RoughNumbers
import PrimesRestrictedDigits.Foundations.Intervals
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The exact Buchstab threshold recurrence

This is the finite least-prime-factor partition behind Montgomery--Vaughan,
Chapter 7, Eq. (7.43) and the following subtraction (pp. 217--218).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem minFac_mul_eq_left_of_weakRough
    {N p m : Nat} (hp : p.Prime) (hm : m ∈ weakRoughNumbersUpTo N p) :
    (p * m).minFac = p := by
  rw [mem_weakRoughNumbersUpTo_iff_minFac] at hm
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p m)
  · refine (Nat.le_minFac.mpr ?_).resolve_left ?_
    · intro q hq hqpm
      rcases hq.dvd_mul.mp hqpm with hqp | hqm
      · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).symm.le
      · exact (Nat.le_minFac.mp hm.2.2) q hq hqm
    · intro hpm
      exact hp.not_dvd_one (hpm ▸ dvd_mul_right p m)

private theorem weakRoughNumbersUpTo_anti
    {N k l : Nat} (hkl : k ≤ l) :
    weakRoughNumbersUpTo N l ⊆ weakRoughNumbersUpTo N k := by
  intro n hn
  rw [mem_weakRoughNumbersUpTo] at hn ⊢
  exact ⟨hn.1, hn.2.1, fun p hp hpn => hkl.trans (hn.2.2 p hp hpn)⟩

private theorem card_minFac_sdiff_fiber
    {N k l p : Nat}
    (hp : p ∈ (Finset.Ico k l).filter Nat.Prime) :
    ((weakRoughNumbersUpTo N k \ weakRoughNumbersUpTo N l).filter
        fun n => n.minFac = p).card =
      (weakRoughNumbersUpTo (N / p) p).card := by
  rw [Finset.card_bij
    (s := weakRoughNumbersUpTo (N / p) p)
    (t := (weakRoughNumbersUpTo N k \ weakRoughNumbersUpTo N l).filter
      fun n => n.minFac = p)
    (fun m _ => p * m)]
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_sdiff]
    have hpData := Finset.mem_filter.mp hp
    have hpBounds := Finset.mem_Ico.mp hpData.1
    have hpPrime : p.Prime := hpData.2
    have hmin := minFac_mul_eq_left_of_weakRough hpPrime hm
    rw [mem_weakRoughNumbersUpTo_iff_minFac] at hm
    refine ⟨⟨?_, ?_⟩, hmin⟩
    · rw [mem_weakRoughNumbersUpTo_iff_minFac]
      refine ⟨Nat.mul_pos hpPrime.pos hm.1, ?_, Or.inr ?_⟩
      · rw [mul_comm, ← Nat.le_div_iff_mul_le hpPrime.pos]
        exact hm.2.1
      · rw [hmin]
        exact hpBounds.1
    · intro hrough
      rw [mem_weakRoughNumbersUpTo] at hrough
      exact (not_le_of_gt hpBounds.2) (hrough.2.2 p hpPrime (dvd_mul_right p m))
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.mul_left_cancel (Finset.mem_filter.mp hp).2.pos heq
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_sdiff] at hn
    rcases hn with ⟨⟨hnMem, _⟩, hnMin⟩
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpdvd : p ∣ n := hnMin.symm ▸ Nat.minFac_dvd n
    rw [mem_weakRoughNumbersUpTo_iff_minFac] at hnMem
    have hdivPos : 0 < n / p :=
      Nat.div_pos (Nat.le_of_dvd hnMem.1 hpdvd) hpPrime.pos
    refine ⟨n / p, ?_, ?_⟩
    · rw [mem_weakRoughNumbersUpTo_iff_minFac]
      refine ⟨hdivPos, Nat.div_le_div_right hnMem.2.1, ?_⟩
      rw [Nat.le_minFac]
      intro q hq hqdiv
      exact hnMin ▸ Nat.minFac_le_of_dvd hq.two_le
        (hqdiv.trans (Nat.div_dvd_of_dvd hpdvd))
    · exact Nat.mul_div_cancel' hpdvd

/-- The finite weak-rough count changes by the least-prime-factor fibers
between two ordered natural thresholds. -/
theorem weakRoughNumbersUpTo_card_threshold_recurrence
    {N k l : Nat} (hkl : k ≤ l) :
    (weakRoughNumbersUpTo N k).card =
      (weakRoughNumbersUpTo N l).card +
        ∑ p ∈ (Finset.Ico k l).filter Nat.Prime,
          (weakRoughNumbersUpTo (N / p) p).card := by
  let lower := weakRoughNumbersUpTo N k
  let upper := weakRoughNumbersUpTo N l
  let primes := (Finset.Ico k l).filter Nat.Prime
  have hsubset : upper ⊆ lower := weakRoughNumbersUpTo_anti hkl
  have hmaps : ((lower \ upper : Finset Nat) : Set Nat).MapsTo Nat.minFac primes := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_sdiff] at hn
    have hnLower := hn.1
    have hnUpper := hn.2
    rw [mem_weakRoughNumbersUpTo_iff_minFac] at hnLower
    have hnNeOne : n ≠ 1 := by
      intro hnOne
      apply hnUpper
      rw [mem_weakRoughNumbersUpTo_iff_minFac]
      exact ⟨hnLower.1, hnLower.2.1, Or.inl hnOne⟩
    have hkMin : k ≤ n.minFac := hnLower.2.2.resolve_left hnNeOne
    have hlMin : n.minFac < l := by
      apply lt_of_not_ge
      intro hl
      apply hnUpper
      rw [mem_weakRoughNumbersUpTo_iff_minFac]
      exact ⟨hnLower.1, hnLower.2.1, Or.inr hl⟩
    change n.minFac ∈ (Finset.Ico k l).filter Nat.Prime
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hkMin, hlMin⟩, Nat.minFac_prime hnNeOne⟩
  have hdiff : (lower \ upper).card =
      ∑ p ∈ primes, (weakRoughNumbersUpTo (N / p) p).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro p hp
    exact card_minFac_sdiff_fiber (by simpa [primes] using hp)
  calc
    lower.card = (lower \ upper).card + upper.card :=
      (Finset.card_sdiff_add_card_eq_card hsubset).symm
    _ = upper.card + (lower \ upper).card := Nat.add_comm _ _
    _ = upper.card + ∑ p ∈ primes,
        (weakRoughNumbersUpTo (N / p) p).card := by rw [hdiff]

/-- The lower-closed, upper-open threshold subtraction following
Montgomery--Vaughan, Chapter 7, Eq. (7.43). -/
theorem buchstabPhi_threshold_recurrence
    {x a b : Real} (hab : a ≤ b) :
    buchstabPhi x a =
      buchstabPhi x b +
        ∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
          buchstabPhi (x / (p : Real)) (p : Real) := by
  simpa [buchstabPhi, buchstabRoughNumbers,
    naturalLeftClosedRightOpenInterval, Nat.floor_div_natCast] using
    weakRoughNumbersUpTo_card_threshold_recurrence
      (N := Nat.floor x) (k := Nat.ceil a) (l := Nat.ceil b) (Nat.ceil_mono hab)

end PrimesRestrictedDigits
