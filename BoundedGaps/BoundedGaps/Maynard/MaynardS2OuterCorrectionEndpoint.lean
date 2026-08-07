import BoundedGaps.Maynard.MaynardS2OuterCorrectionSum
import BoundedGaps.Maynard.MaynardS2OuterSingularSeries

noncomputable section

/-! Signed Euler-product endpoint for the S2 outer correction. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction Filter
open scoped BigOperators

private theorem maynardS2OuterCorrection_local_sum_eq
    (W : ℕ) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' i : ℕ, maynardS2OuterCorrectionAF W (p ^ i)) =
      if p ∣ W then 1 else maynardS2OuterSingularLocalFactor p := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    rw [maynardS2OuterCorrectionAF_apply_prime_pow_ge_three W hp hi])]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  rw [maynardS2OuterCorrectionAF_apply_prime W hp hp3,
    maynardS2OuterCorrectionAF_apply_prime_sq W hp]
  have hOne : maynardS2OuterCorrectionAF W 1 = 1 :=
    (maynardS2OuterCorrectionAF_isMultiplicative W).map_one
  rw [hOne]
  by_cases hpW : p ∣ W
  · simp [hpW]
  · rw [if_neg hpW, if_neg hpW,
      maynardS2OuterSingularLocalFactor_prime_eq hp hp3]
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : 2 ≤ p := by omega
    have hpG : (maynardS2G p : ℝ) = p - 2 := by
      rw [maynardS2G_prime hp]
      norm_num [Nat.cast_sub hp2]
    have hpPhi : (Nat.totient p : ℝ) = p - 1 := by
      rw [Nat.totient_prime hp]
      norm_num [Nat.cast_sub hp.one_le]
    have hpM2 : (0 : ℝ) < p - 2 := by
      have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    unfold maynardS2OuterScalarWeight maynardS2OuterSingularCorrection
    rw [hpG, hpPhi]
    norm_num only [Nat.cast_one]
    simp only [hpW, if_false]
    have hden : -(p : ℝ) ^ 3 * 2 + (p : ℝ) ^ 4 ≠ 0 := by
      have hpos : 0 < (p : ℝ) ^ 3 * ((p : ℝ) - 2) :=
        mul_pos (pow_pos hpR 3) hpM2
      nlinarith
    field_simp [ne_of_gt hpR, ne_of_gt hpM2, hden]
    ring

private theorem maynardS2OuterCorrection_local_sum_two
    (W : ℕ) (hW : 2 ∣ W) :
    (∑' i : ℕ, maynardS2OuterCorrectionAF W (2 ^ i)) = 1 := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    rw [maynardS2OuterCorrectionAF_apply_prime_pow_ge_three W
      Nat.prime_two hi])]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  have hOne : maynardS2OuterCorrectionAF W 1 = 1 :=
    (maynardS2OuterCorrectionAF_isMultiplicative W).map_one
  rw [maynardS2OuterCorrectionAF_apply_two,
    maynardS2OuterCorrectionAF_apply_prime_sq W Nat.prime_two, hOne]
  simp [hW]

theorem tsum_maynardS2OuterCorrectionAF_eq_maynardS2OuterInfiniteSingularTail
    {D : ℕ} (hD : 2 ≤ D) :
    (∑' n : ℕ, maynardS2OuterCorrectionAF (primorial D) n) =
      maynardS2OuterInfiniteSingularTail D := by
  have hsum : Summable (fun n : ℕ =>
      ‖maynardS2OuterCorrectionAF (primorial D) n‖) := by
    simpa [Real.norm_eq_abs] using
      summable_abs_maynardS2OuterCorrectionAF (primorial D)
  have hEuler :=
    (maynardS2OuterCorrectionAF_isMultiplicative (primorial D)).eulerProduct_tprod
      hsum
  rw [← hEuler]
  have hsupport : Function.mulSupport
      (maynardS2OuterSingularSequenceFactor D) ⊆ {n | n.Prime} := by
    intro n hn
    by_contra hnp
    have hnp' : ¬n.Prime := by simpa using hnp
    apply hn
    simp [maynardS2OuterSingularSequenceFactor, hnp']
  have hseq :
      (∏' p : Nat.Primes,
        maynardS2OuterSingularSequenceFactor D (p : ℕ)) =
        maynardS2OuterInfiniteSingularTail D := by
    unfold maynardS2OuterInfiniteSingularTail
    exact tprod_subtype_eq_of_mulSupport_subset hsupport
  rw [← hseq]
  apply tprod_congr
  intro p
  by_cases hpD : (p : ℕ) ≤ D
  · have hpW : (p : ℕ) ∣ primorial D :=
      p.property.dvd_primorial_iff.mpr hpD
    by_cases hpTwo : (p : ℕ) = 2
    · have hlocal := maynardS2OuterCorrection_local_sum_two
        (primorial D) (by simpa [hpTwo] using hpW)
      have hpNotD : ¬D < (p : ℕ) := by omega
      have hDnot : ¬D ≤ 1 := by omega
      simpa [maynardS2OuterSingularSequenceFactor, hpTwo, hpNotD, hDnot] using hlocal
    · have hp2 : 2 ≤ (p : ℕ) := p.property.two_le
      have hp3 : 3 ≤ (p : ℕ) := by omega
      have hlocal := maynardS2OuterCorrection_local_sum_eq
        (primorial D) p.property hp3
      simp [hpW] at hlocal
      have hpNotD : ¬D < (p : ℕ) := by omega
      simpa [maynardS2OuterSingularSequenceFactor, p.property, hpNotD] using hlocal
  · have hp3 : 3 ≤ (p : ℕ) := by
      have hp2 : 2 ≤ (p : ℕ) := p.property.two_le
      omega
    have hpW : ¬(p : ℕ) ∣ primorial D := by
      intro h
      exact hpD (p.property.dvd_primorial_iff.mp h)
    have hlocal := maynardS2OuterCorrection_local_sum_eq
      (primorial D) p.property hp3
    rw [if_neg hpW] at hlocal
    have hpPrime : (p : ℕ).Prime := p.property
    have hpDlt : D < (p : ℕ) := by omega
    rw [maynardS2OuterSingularSequenceFactor,
      if_pos ⟨hpPrime, hpDlt⟩]
    exact hlocal

end BoundedGaps.Maynard
