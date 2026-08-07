import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveConductorFibers
import Mathlib.NumberTheory.Divisors

/-!
# Positive divisor-pair reindexing

This file isolates the finite index change on Akbary--Hambrook2013v2,
Section 7, p. 25. A positive modulus and one of its divisors are reindexed by
the ordered pair `(d,k)` with modulus `d*k`. The first coordinate is reserved
for the future primitive conductor. The centered character sum, its
conductor-one vanishing, the totient weight, and the least-prime-factor cutoff
are deliberately not built into this generic finite layer.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Positive ordered factor pairs whose product is at most `Q`.

The first coordinate is the future primitive conductor and the second is its
positive multiplier. -/
def positiveFactorPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 Q ×ˢ Finset.Ioc 0 Q).filter
    (fun p ↦ p.1 * p.2 ≤ Q)

/-- Regroup a first-coordinate-filtered positive factor-pair sum by its first
coordinate and the exact positive multiplier range. -/
theorem sum_positiveFactorPairs_filter_fst_eq_sum_multipliers
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ → M) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦ P p.1),
      f p.1 p.2) =
      ∑ d ∈ Finset.Ioc 0 Q with P d,
        ∑ k ∈ Finset.Ioc 0 (Q / d), f d k := by
  let S : Finset (ℕ × ℕ) :=
    (positiveFactorPairs Q).filter (fun p ↦ P p.1)
  let T : Finset ((d : ℕ) × ℕ) :=
    Finset.sigma ((Finset.Ioc 0 Q).filter P)
      (fun d ↦ Finset.Ioc 0 (Q / d))
  have hbij :
      (∑ p ∈ S, f p.1 p.2) =
        ∑ z ∈ T, f z.1 z.2 := by
    apply Finset.sum_bij (fun p _hp ↦ ⟨p.1, p.2⟩)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpairs, hP⟩
      rcases Finset.mem_filter.mp hpairs with ⟨hprodmem, hprod⟩
      rcases Finset.mem_product.mp hprodmem with ⟨hdmem, hkmem⟩
      have hdpos : 0 < p.1 := (Finset.mem_Ioc.mp hdmem).1
      have hkdiv : p.2 ≤ Q / p.1 := by
        apply (Nat.le_div_iff_mul_le hdpos).2
        simpa [Nat.mul_comm] using hprod
      exact Finset.mem_sigma.mpr ⟨
        Finset.mem_filter.mpr ⟨hdmem, hP⟩,
        Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hkmem).1, hkdiv⟩⟩
    · intro p _hp p' _hp' heq
      apply Prod.ext
      · exact congrArg Sigma.fst heq
      · exact congrArg Sigma.snd heq
    · intro z hz
      rcases z with ⟨d, k⟩
      rcases Finset.mem_sigma.mp hz with ⟨hdmemP, hkmem⟩
      rcases Finset.mem_filter.mp hdmemP with ⟨hdmem, hP⟩
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hdmem).1
      have hkBounds := Finset.mem_Ioc.mp hkmem
      have hprod : d * k ≤ Q := by
        have h := (Nat.le_div_iff_mul_le hdpos).1 hkBounds.2
        simpa [Nat.mul_comm] using h
      have hkQ : k ≤ Q :=
        hkBounds.2.trans (Nat.div_le_self Q d)
      have hpairs : (d, k) ∈ positiveFactorPairs Q := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨hdmem,
          Finset.mem_Ioc.mpr ⟨hkBounds.1, hkQ⟩⟩, hprod⟩
      exact ⟨(d, k), Finset.mem_filter.mpr ⟨hpairs, hP⟩, rfl⟩
    · intro p _hp
      rfl
  have hsum := Finset.sum_sigma'
    ((Finset.Ioc 0 Q).filter P)
    (fun d ↦ Finset.Ioc 0 (Q / d)) (fun d k ↦ f d k)
  simpa [S, T] using hbij.trans hsum.symm

/-- Reindex positive products and their divisor antidiagonals by ordered
positive factor pairs. -/
theorem sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ p ∈ q.divisorsAntidiagonal, f p.1 p.2) =
      ∑ p ∈ positiveFactorPairs Q, f p.1 p.2 := by
  let T : Finset ℕ := Finset.Ioc 0 Q
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  have hmaps : ∀ p ∈ positiveFactorPairs Q, g p ∈ T := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp₁.1 hp₂.1, hprod⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := positiveFactorPairs Q) (t := T) hmaps
    (fun p ↦ f p.1 p.2)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (N := Q)]
  · apply Finset.sum_congr
    · ext p
      simp only [positiveFactorPairs, g, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hprod⟩
        exact ⟨⟨hp, hprod.le.trans (Finset.mem_Ioc.mp hq).2⟩, hprod⟩
      · rintro ⟨⟨hp, _⟩, hprod⟩
        exact ⟨hp, hprod⟩
    · intro p _
      rfl
  · exact (Finset.mem_Ioc.mp hq).1.ne'
  · exact (Finset.mem_Ioc.mp hq).2

/-- Reindex a positive modulus and one of its divisors by the divisor and its
positive complementary factor. -/
theorem sum_divisors_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ d ∈ q.divisors, f q d) =
      ∑ p ∈ positiveFactorPairs Q,
        f (p.1 * p.2) p.1 := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q, ∑ d ∈ q.divisors, f q d) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ p ∈ q.divisorsAntidiagonal,
            f (p.1 * p.2) p.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Nat.sum_divisorsAntidiagonal
        (f := fun d _k ↦ f q d)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [hp.1]
    _ = _ :=
      sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
        (fun d k ↦ f (d * k) d)

/-- Reindex the positive modulus/conductor sum while retaining the explicit
divisibility witness accepted by the summand. -/
theorem sum_primitive_conductors_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (F : ∀ {q d : ℕ}, d ∣ q → primitiveCharacters d → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ d : q.divisors,
        ∑ ψ : primitiveCharacters d.1,
          F (Nat.dvd_of_mem_divisors d.2) ψ) =
      ∑ p ∈ positiveFactorPairs Q,
        ∑ ψ : primitiveCharacters p.1,
          F (Nat.dvd_mul_right p.1 p.2) ψ := by
  let f : ℕ → ℕ → M := fun q d ↦
    if h : d ∣ q then
      ∑ ψ : primitiveCharacters d, F h ψ
    else 0
  have hdiv :
      (∑ q ∈ Finset.Ioc 0 Q,
        ∑ d : q.divisors,
          ∑ ψ : primitiveCharacters d.1,
            F (Nat.dvd_of_mem_divisors d.2) ψ) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ d ∈ q.divisors, f q d := by
    apply Finset.sum_congr rfl
    intro q hq
    calc
      (∑ d : q.divisors,
          ∑ ψ : primitiveCharacters d.1,
            F (Nat.dvd_of_mem_divisors d.2) ψ) =
          ∑ d : q.divisors, f q d.1 := by
        apply Fintype.sum_congr
        intro d
        simp only [f, dif_pos (Nat.dvd_of_mem_divisors d.2)]
      _ = ∑ d ∈ q.divisors, f q d := by
        exact (Finset.sum_subtype q.divisors
          (fun _ ↦ Iff.rfl) (f q)).symm
  rw [hdiv, sum_divisors_up_to_eq_sum_positiveFactorPairs]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [f, dif_pos (Nat.dvd_mul_right p.1 p.2)]

/-- The same conductor reindex with an arbitrary decidable condition on the
original modulus. -/
theorem sum_primitive_conductors_up_to_filter_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (P : ℕ → Prop) [DecidablePred P]
    (F : ∀ {q d : ℕ}, d ∣ q → primitiveCharacters d → M) :
    (∑ q ∈ Finset.Ioc 0 Q with P q,
      ∑ d : q.divisors,
        ∑ ψ : primitiveCharacters d.1,
          F (Nat.dvd_of_mem_divisors d.2) ψ) =
      ∑ p ∈ (positiveFactorPairs Q).filter
          (fun p ↦ P (p.1 * p.2)),
        ∑ ψ : primitiveCharacters p.1,
          F (Nat.dvd_mul_right p.1 p.2) ψ := by
  let G : ∀ {q d : ℕ}, d ∣ q → primitiveCharacters d → M :=
    fun {q _d} hd ψ ↦ if P q then F hd ψ else 0
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        if P q then
          ∑ d : q.divisors,
            ∑ ψ : primitiveCharacters d.1,
              F (Nat.dvd_of_mem_divisors d.2) ψ
        else 0) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ d : q.divisors,
            ∑ ψ : primitiveCharacters d.1,
              G (Nat.dvd_of_mem_divisors d.2) ψ := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hP : P q <;> simp [G, hP]
    _ = ∑ p ∈ positiveFactorPairs Q,
          ∑ ψ : primitiveCharacters p.1,
            G (Nat.dvd_mul_right p.1 p.2) ψ :=
      sum_primitive_conductors_up_to_eq_sum_positiveFactorPairs G
    _ = ∑ p ∈ positiveFactorPairs Q,
          if P (p.1 * p.2) then
            ∑ ψ : primitiveCharacters p.1,
              F (Nat.dvd_mul_right p.1 p.2) ψ
          else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hP : P (p.1 * p.2) <;> simp [G, hP]

end

end BoundedGaps.Maynard
