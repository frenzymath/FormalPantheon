import BoundedGaps.Maynard.MaynardS2OuterSingularTail
import BoundedGaps.Maynard.PreSieveLocalSeries

noncomputable section

/-!
# Finite modulus-dependent singular-series factorization

Maynard2013v3, source lines 552--560, uses the outer gamma with zero local
density on primes dividing the primorial pre-sieve.  The finite product
identity below separates those factors from the remaining outer tail.
-/

namespace BoundedGaps.Maynard

noncomputable def maynardS2OuterModularSingularFactor (D p : ℕ) : ℝ :=
  if p ∣ primorial D then 1 - (1 : ℝ) / p
  else maynardS2OuterSingularLocalFactor p

theorem maynardS2OuterModularSingularFactorization
    {D Q : ℕ} (hDQ : D ≤ Q) :
    (∏ p ∈ Nat.primesLE Q,
      maynardS2OuterModularSingularFactor D p) =
      preSieveSingularSeries D *
        maynardS2OuterSingularTail D (Q + 1) := by
  let Plo := Nat.primesLE D
  let Phi := Nat.primesLE Q
  let Ptail := (Finset.Ico (D + 1) (Q + 1)).filter Nat.Prime
  have hsub : Plo ⊆ Phi := by
    intro p hp
    exact (Nat.mem_primesLE.mpr ⟨
      (Nat.mem_primesLE.mp hp).1.trans hDQ,
      (Nat.mem_primesLE.mp hp).2⟩)
  have hdiff : Phi \ Plo = Ptail := by
    ext p
    simp only [Phi, Plo, Ptail, Finset.mem_sdiff, Nat.mem_primesLE,
      Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hpQ, hpPrime⟩, hnotD⟩
      have hpD : ¬p ≤ D := by
        intro hpD
        exact hnotD ⟨hpD, hpPrime⟩
      have hDlt : D < p := by omega
      exact ⟨⟨by omega, by omega⟩, hpPrime⟩
    · rintro ⟨⟨hD, hpQ⟩, hpPrime⟩
      refine ⟨⟨by omega, hpPrime⟩, ?_⟩
      intro hpD
      omega
  have hlow (p : ℕ) (hp : p ∈ Plo) :
      maynardS2OuterModularSingularFactor D p =
        1 - (1 : ℝ) / p := by
    unfold maynardS2OuterModularSingularFactor
    have hpDiv : p ∣ primorial D :=
      (Nat.prime_of_mem_primesLE hp).dvd_primorial_iff.mpr
        (Nat.mem_primesLE.mp hp).1
    simp [hpDiv]
  have hhigh (p : ℕ) (hp : p ∈ Phi \ Plo) :
      maynardS2OuterModularSingularFactor D p =
        maynardS2OuterSingularLocalFactor p := by
    unfold maynardS2OuterModularSingularFactor
    rw [if_neg]
    intro hpD
    have hpPrime : p.Prime :=
      (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
    have hpLeD := hpPrime.dvd_primorial_iff.mp hpD
    exact (Finset.mem_sdiff.mp hp).2
      ((Nat.mem_primesLE.mpr ⟨hpLeD, hpPrime⟩))
  calc
    (∏ p ∈ Phi, maynardS2OuterModularSingularFactor D p) =
        (∏ p ∈ Phi \ Plo, maynardS2OuterModularSingularFactor D p) *
          ∏ p ∈ Plo, maynardS2OuterModularSingularFactor D p := by
      exact (Finset.prod_sdiff hsub).symm
    _ = (∏ p ∈ Ptail, maynardS2OuterSingularLocalFactor p) *
          ∏ p ∈ Plo, (1 - (1 : ℝ) / p) := by
      rw [hdiff]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro p hp
        exact hhigh p (by rw [hdiff]; exact hp)
      · apply Finset.prod_congr rfl
        intro p hp
        exact hlow p hp
    _ = preSieveSingularSeries D *
          maynardS2OuterSingularTail D (Q + 1) := by
      unfold preSieveSingularSeries maynardS2OuterSingularTail
      ring

end BoundedGaps.Maynard
