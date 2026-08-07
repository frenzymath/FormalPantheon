import BoundedGaps.Maynard.ConcreteS2RestrictedReindex
import BoundedGaps.Maynard.MaynardS1CrossPrime

noncomputable section

/-!
# Large-prime support of the restricted S2 cross correction

Every incompatible supported pair in the restricted S2 correction has a
cross-coordinate prime divisor above the concrete pre-sieve cutoff. When the
distinguished coordinates are one, both witness coordinates lie off that
face. This is the finite support statement behind Maynard2013v3, source lines
540--546.
-/

namespace BoundedGaps.Maynard

local instance s2RestrictedCrossPrimeDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

set_option maxRecDepth 3000 in
theorem exists_engelsmaS2RestrictedCross_prime_gt_tripleLogCutoff
    {alpha : ℝ} {N : ℕ}
    {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hd : d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (_he : e ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (hcross : ¬IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e) :
    ∃ a b : BoundedGaps.engelsmaTuple, ∃ p : ℕ,
      a ≠ b ∧ p.Prime ∧ tripleLogCutoff (N - 1) < p ∧
        p ∣ d a ∧ p ∣ e b := by
  exact exists_engelsma_crossCoordinate_prime_gt_tripleLogCutoff
    (maynardSupportFamily_mem_isMaynard hd) hcross

set_option maxRecDepth 3000 in
theorem exists_engelsmaS2RestrictedCross_offCoordinate_prime
    {alpha : ℝ} {N : ℕ} (m : BoundedGaps.engelsmaTuple)
    {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hd : d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (he : e ∈ (maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).filter
        (fun e => ¬IsCrossCoordinateCoprime
          BoundedGaps.engelsmaTuple d e))
    (hm : d m = 1 ∧ e m = 1) :
    ∃ a b : BoundedGaps.engelsmaTuple, ∃ p : ℕ,
      a ≠ b ∧ a ≠ m ∧ b ≠ m ∧ p.Prime ∧
        tripleLogCutoff (N - 1) < p ∧ p ∣ d a ∧ p ∣ e b := by
  have heData := Finset.mem_filter.mp he
  obtain ⟨a, b, p, hab, hp, hpCutoff, hpda, hpeb⟩ :=
    exists_engelsmaS2RestrictedCross_prime_gt_tripleLogCutoff
      hd heData.1 heData.2
  have ham : a ≠ m := by
    intro ha
    subst a
    rw [hm.1] at hpda
    exact hp.ne_one (Nat.dvd_one.mp hpda)
  have hbm : b ≠ m := by
    intro hb
    subst b
    rw [hm.2] at hpeb
    exact hp.ne_one (Nat.dvd_one.mp hpeb)
  exact ⟨a, b, p, hab, ham, hbm, hp, hpCutoff, hpda, hpeb⟩

end BoundedGaps.Maynard
