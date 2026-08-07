import BoundedGaps.Maynard.ConcreteS1Diagonal
import Mathlib.NumberTheory.Primorial

/-!
# Large prime witnesses for incompatible S1 pairs

Pre-sieving forces every prime shared by distinct tuple coordinates above the
primorial cutoff.
-/

namespace BoundedGaps.Maynard

theorem exists_crossCoordinate_common_prime
    {H : Finset ℕ} {d e : H → ℕ}
    (hcross : ¬IsCrossCoordinateCoprime H d e) :
    ∃ a b : H, ∃ p : ℕ,
      a ≠ b ∧ p.Prime ∧ p ∣ d a ∧ p ∣ e b := by
  have hnot := hcross
  rw [isCrossCoordinateCoprime_iff_ordered] at hnot
  push Not at hnot
  obtain ⟨a, b, hab, hcop⟩ := hnot
  obtain ⟨p, hp, hpda, hpeb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  exact ⟨a, b, p, hab, hp, hpda, hpeb⟩

theorem prime_gt_of_dvd_coprime_primorial
    {D₀ p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn : Nat.Coprime n (primorial D₀)) :
    D₀ < p := by
  by_contra hnot
  have hpD₀ : p ≤ D₀ := Nat.le_of_not_gt hnot
  have hpW : p ∣ primorial D₀ := hp.dvd_primorial_iff.mpr hpD₀
  have hpcop : Nat.Coprime p (primorial D₀) :=
    Nat.Coprime.of_dvd_left hpn hn
  exact hp.ne_one (hpcop.eq_one_of_dvd hpW)

theorem exists_crossCoordinate_prime_gt_primorialCutoff
    {H : Finset ℕ} {R D₀ : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R (primorial D₀) d)
    (hcross : ¬IsCrossCoordinateCoprime H d e) :
    ∃ a b : H, ∃ p : ℕ,
      a ≠ b ∧ p.Prime ∧ D₀ < p ∧ p ∣ d a ∧ p ∣ e b := by
  obtain ⟨a, b, p, hab, hp, hpda, hpeb⟩ :=
    exists_crossCoordinate_common_prime hcross
  have hpProd : p ∣ divisorTupleProduct H d :=
    dvd_trans hpda (divisorTupleCoordinate_dvd_product d a)
  exact ⟨a, b, p, hab, hp,
    prime_gt_of_dvd_coprime_primorial hp hpProd hd.2.1, hpda, hpeb⟩

theorem exists_engelsma_crossCoordinate_prime_gt_tripleLogCutoff
    {alpha : ℝ} {N : ℕ}
    {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hd : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) d)
    (hcross : ¬IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d e) :
    ∃ a b : BoundedGaps.engelsmaTuple, ∃ p : ℕ,
      a ≠ b ∧ p.Prime ∧ tripleLogCutoff (N - 1) < p ∧
        p ∣ d a ∧ p ∣ e b := by
  unfold engelsmaMaynardModulus at hd
  exact exists_crossCoordinate_prime_gt_primorialCutoff hd hcross

end BoundedGaps.Maynard
