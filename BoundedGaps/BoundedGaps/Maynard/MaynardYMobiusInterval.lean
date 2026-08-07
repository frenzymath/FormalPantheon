import BoundedGaps.Maynard.MaynardYTransform
import BoundedGaps.Maynard.ImprovedGPY.Mobius
import Mathlib.Data.Finset.NatDivisors

noncomputable section

/-!
# Möbius cancellation on upper divisor intervals

The finite forward `lambda -> y` inversion uses Möbius cancellation over the
divisors lying between two squarefree naturals. This file proves the scalar
identity and its coordinatewise tuple lift.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

def upperDivisorInterval (r e : ℕ) : Finset ℕ :=
  by
    classical
    exact e.divisors.filter (r ∣ ·)

theorem sum_moebius_upperDivisorInterval
    {r e : ℕ} (he : Squarefree e) (hr : 0 < r) (hre : r ∣ e) :
    (∑ d ∈ upperDivisorInterval r e, ArithmeticFunction.moebius d) =
      if r = e then ArithmeticFunction.moebius r else 0 := by
  classical
  let q := e / r
  have he0 : e ≠ 0 := he.ne_zero
  have hq0 : q ≠ 0 := by
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hre) hr).ne'
  have hmul : r * q = e := Nat.mul_div_cancel' hre
  have hcop : Nat.Coprime r q := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hmul]
  have hreindex :
      (∑ d ∈ upperDivisorInterval r e, ArithmeticFunction.moebius d) =
        ∑ a ∈ q.divisors,
          ArithmeticFunction.moebius r * ArithmeticFunction.moebius a := by
    apply Finset.sum_bij (fun d hd => d / r)
    · intro d hd
      have hdData := Finset.mem_filter.mp hd
      have hrd : r ∣ d := hdData.2
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hq0⟩
      rw [Nat.dvd_div_iff_mul_dvd hre]
      rw [Nat.mul_div_cancel' hrd]
      exact Nat.dvd_of_mem_divisors hdData.1
    · intro d₁ hd₁ d₂ hd₂ hdiv
      have hr₁ := (Finset.mem_filter.mp hd₁).2
      have hr₂ := (Finset.mem_filter.mp hd₂).2
      calc
        d₁ = r * (d₁ / r) := (Nat.mul_div_cancel' hr₁).symm
        _ = r * (d₂ / r) := by rw [hdiv]
        _ = d₂ := Nat.mul_div_cancel' hr₂
    · intro a ha
      refine ⟨r * a, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Nat.mem_divisors.mpr ⟨?_, he0⟩, dvd_mul_right r a⟩
        have haDvd : a ∣ q := Nat.dvd_of_mem_divisors ha
        rw [← hmul]
        exact Nat.mul_dvd_mul_left r haDvd
      · exact Nat.mul_div_cancel_left a hr
    · intro d hd
      have hdData := Finset.mem_filter.mp hd
      have hrd : r ∣ d := hdData.2
      have hquotDvd : d / r ∣ q := by
        rw [Nat.dvd_div_iff_mul_dvd hre]
        rw [Nat.mul_div_cancel' hrd]
        exact Nat.dvd_of_mem_divisors hdData.1
      have hcop' : Nat.Coprime r (d / r) := hcop.of_dvd_right hquotDvd
      calc
        ArithmeticFunction.moebius d =
            ArithmeticFunction.moebius (r * (d / r)) := by
          rw [Nat.mul_div_cancel' hrd]
        _ = ArithmeticFunction.moebius r * ArithmeticFunction.moebius (d / r) :=
          ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop'
  rw [hreindex, ← Finset.mul_sum]
  rw [sum_moebius_divisors_eq_one_iff]
  by_cases hq : q = 1
  · have hreEq : r = e := Nat.eq_of_dvd_of_div_eq_one hre hq
    simp [hq, hreEq]
  · have hreNe : r ≠ e := by
      intro h
      apply hq
      change e / r = 1
      rw [h]
      exact Nat.div_self (h ▸ hr)
    simp [hq, hreNe]

def upperDivisorTupleInterval
    (H : Finset ℕ) (r e : H → ℕ) : Finset (H → ℕ) :=
  by
    classical
    exact Fintype.piFinset (fun h => upperDivisorInterval (r h) (e h))

theorem sum_tupleMoebius_upperDivisorTupleInterval
    {H : Finset ℕ} {r e : H → ℕ}
    (he : Squarefree (divisorTupleProduct H e))
    (hr : ∀ h, 0 < r h) (hre : ∀ h, r h ∣ e h) :
    (∑ d ∈ upperDivisorTupleInterval H r e,
        ∏ h : H, ArithmeticFunction.moebius (d h)) =
      if r = e then ∏ h : H, ArithmeticFunction.moebius (r h) else 0 := by
  classical
  calc
    (∑ d ∈ upperDivisorTupleInterval H r e,
        ∏ h : H, ArithmeticFunction.moebius (d h)) =
        ∏ h : H, ∑ d ∈ upperDivisorInterval (r h) (e h),
          ArithmeticFunction.moebius d := by
      exact (Finset.prod_univ_sum _ _).symm
    _ = ∏ h : H, if r h = e h then
          ArithmeticFunction.moebius (r h) else 0 := by
      apply Finset.prod_congr rfl
      intro h _
      exact sum_moebius_upperDivisorInterval
        (he.squarefree_of_dvd (divisorTupleCoordinate_dvd_product e h))
        (hr h) (hre h)
    _ = if r = e then ∏ h : H, ArithmeticFunction.moebius (r h) else 0 := by
      by_cases hdiag : r = e
      · subst e
        simp
      · rw [if_neg hdiag]
        obtain ⟨h, hh⟩ : ∃ h, r h ≠ e h := by
          by_contra hnone
          simp only [not_exists] at hnone
          apply hdiag
          funext i
          exact Classical.not_not.mp (hnone i)
        exact Finset.prod_eq_zero (Finset.mem_univ h) (if_neg hh)

end BoundedGaps.Maynard
