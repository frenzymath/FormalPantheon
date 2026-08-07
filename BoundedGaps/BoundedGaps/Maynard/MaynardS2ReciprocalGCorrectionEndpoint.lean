import BoundedGaps.Maynard.MaynardS2ReciprocalGCorrectionSum

noncomputable section

/-!
# Signed endpoint for the reciprocal-g correction

The correction attached to Maynard2013v3, Section 6, source lines 386--403,
has local signed total `1 + 1 / (p * (p - 2))` away from the pre-sieve.
This module identifies its global signed sum with the corresponding infinite
Euler-product tail. See `SEM-354`.
-/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped BigOperators

noncomputable def maynardS2ReciprocalGSingularLocalFactor (p : ℕ) : ℝ :=
  1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))

noncomputable def maynardS2ReciprocalGSingularSequenceFactor
    (D n : ℕ) : ℝ :=
  if n.Prime ∧ D < n then maynardS2ReciprocalGSingularLocalFactor n else 1

noncomputable def maynardS2ReciprocalGInfiniteSingularTail (D : ℕ) : ℝ :=
  ∏' n : ℕ, maynardS2ReciprocalGSingularSequenceFactor D n

private theorem maynardS2ReciprocalGCorrection_local_sum_eq
    (W : ℕ) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' i : ℕ, maynardS2ReciprocalGCorrectionAF W (p ^ i)) =
      if p ∣ W then 1 else maynardS2ReciprocalGSingularLocalFactor p := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    rw [maynardS2ReciprocalGCorrectionAF_apply_prime_pow_ge_three W hp hi])]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  rw [maynardS2ReciprocalGCorrectionAF_apply_prime W hp hp3,
    maynardS2ReciprocalGCorrectionAF_apply_prime_sq W hp]
  have hOne : maynardS2ReciprocalGCorrectionAF W 1 = 1 :=
    (maynardS2ReciprocalGCorrectionAF_isMultiplicative W).map_one
  rw [hOne]
  by_cases hpW : p ∣ W
  · simp [hpW]
  · rw [if_neg hpW, if_neg hpW]
    have hp2 : 2 ≤ p := hp.two_le
    rw [Nat.cast_sub hp2]
    norm_num only [Nat.cast_ofNat]
    unfold maynardS2ReciprocalGSingularLocalFactor
    rw [if_neg hpW]
    ring

private theorem maynardS2ReciprocalGCorrection_local_sum_two
    (W : ℕ) (hW : 2 ∣ W) :
    (∑' i : ℕ, maynardS2ReciprocalGCorrectionAF W (2 ^ i)) = 1 := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    rw [maynardS2ReciprocalGCorrectionAF_apply_prime_pow_ge_three W
      Nat.prime_two hi])]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  have hOne : maynardS2ReciprocalGCorrectionAF W 1 = 1 :=
    (maynardS2ReciprocalGCorrectionAF_isMultiplicative W).map_one
  rw [maynardS2ReciprocalGCorrectionAF_apply_two,
    maynardS2ReciprocalGCorrectionAF_apply_prime_sq W Nat.prime_two, hOne]
  simp [hW]

theorem tsum_maynardS2ReciprocalGCorrectionAF_eq_infiniteSingularTail
    {D : ℕ} (hD : 2 ≤ D) :
    (∑' n : ℕ,
      maynardS2ReciprocalGCorrectionAF (primorial D) n) =
      maynardS2ReciprocalGInfiniteSingularTail D := by
  have hsum : Summable (fun n : ℕ =>
      ‖maynardS2ReciprocalGCorrectionAF (primorial D) n‖) := by
    simpa [Real.norm_eq_abs] using
      summable_abs_maynardS2ReciprocalGCorrectionAF (primorial D)
  have hEuler :=
    (maynardS2ReciprocalGCorrectionAF_isMultiplicative (primorial D))
      |>.eulerProduct_tprod hsum
  rw [← hEuler]
  have hsupport : Function.mulSupport
      (maynardS2ReciprocalGSingularSequenceFactor D) ⊆
        {n | n.Prime} := by
    intro n hn
    by_contra hnp
    have hnp' : ¬n.Prime := by simpa using hnp
    apply hn
    simp [maynardS2ReciprocalGSingularSequenceFactor, hnp']
  have hseq :
      (∏' p : Nat.Primes,
        maynardS2ReciprocalGSingularSequenceFactor D (p : ℕ)) =
        maynardS2ReciprocalGInfiniteSingularTail D := by
    unfold maynardS2ReciprocalGInfiniteSingularTail
    exact tprod_subtype_eq_of_mulSupport_subset hsupport
  rw [← hseq]
  apply tprod_congr
  intro p
  by_cases hpD : (p : ℕ) ≤ D
  · have hpW : (p : ℕ) ∣ primorial D :=
      p.property.dvd_primorial_iff.mpr hpD
    by_cases hpTwo : (p : ℕ) = 2
    · have hpEq : p = (⟨2, Nat.prime_two⟩ : Nat.Primes) :=
        Subtype.ext hpTwo
      subst p
      have hlocal := maynardS2ReciprocalGCorrection_local_sum_two
        (primorial D) (by simpa using hpW)
      have hpNotD : ¬D < 2 := by omega
      simpa [maynardS2ReciprocalGSingularSequenceFactor,
        hpNotD] using hlocal
    · have hp3 : 3 ≤ (p : ℕ) := by
        have hp2 := p.property.two_le
        omega
      have hlocal := maynardS2ReciprocalGCorrection_local_sum_eq
        (primorial D) p.property hp3
      rw [if_pos hpW] at hlocal
      have hpNotD : ¬D < (p : ℕ) := by omega
      simpa [maynardS2ReciprocalGSingularSequenceFactor,
        p.property, hpNotD] using hlocal
  · have hp3 : 3 ≤ (p : ℕ) := by
      have hp2 := p.property.two_le
      omega
    have hpW : ¬(p : ℕ) ∣ primorial D := by
      intro h
      exact hpD (p.property.dvd_primorial_iff.mp h)
    have hlocal := maynardS2ReciprocalGCorrection_local_sum_eq
      (primorial D) p.property hp3
    rw [if_neg hpW] at hlocal
    have hpDlt : D < (p : ℕ) := by omega
    simpa [maynardS2ReciprocalGSingularSequenceFactor,
      p.property, hpDlt] using hlocal

end BoundedGaps.Maynard
