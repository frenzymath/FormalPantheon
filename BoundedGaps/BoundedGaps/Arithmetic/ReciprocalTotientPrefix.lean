import BoundedGaps.Arithmetic.SquarefreeReciprocalCoefficient
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.Radical.NatInt

/-!
# Full reciprocal-totient prefixes

This file proves the elementary full reciprocal-totient prefix bound used in
Akbary--Hambrook2013v2, Section 7, p. 25. Squarefreeness belongs only to the
divisor coefficient in the convolution; the target prefix includes every
positive natural number. The explicit constant `4` is a proved replacement
for the sharper Euler-product constant used in the source.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- For squarefree `n`, `n / phi(n)` is the sum of reciprocal totients over
all divisors of `n`. -/
theorem squarefree_div_totient_eq_sum_divisors_inv_totient
    {n : ℕ} (hn : Squarefree n) :
    (n : ℝ) / (Nat.totient n : ℝ) =
      ∑ a ∈ n.divisors, (Nat.totient a : ℝ)⁻¹ := by
  classical
  have hn0 : n ≠ 0 := hn.ne_zero
  have hterm : ∀ a ∈ n.divisors,
      (Nat.totient a : ℝ)⁻¹ =
        (Nat.totient (n / a) : ℝ) / (Nat.totient n : ℝ) := by
    intro a ha
    have hadvd : a ∣ n := Nat.dvd_of_mem_divisors ha
    have hmul : a * (n / a) = n := Nat.mul_div_cancel' hadvd
    have hcop : Nat.Coprime a (n / a) := by
      apply Nat.coprime_of_squarefree_mul
      rwa [hmul]
    have hphi : Nat.totient n =
        Nat.totient a * Nat.totient (n / a) := by
      calc
        Nat.totient n = Nat.totient (a * (n / a)) :=
          congrArg Nat.totient hmul.symm
        _ = Nat.totient a * Nat.totient (n / a) := Nat.totient_mul hcop
    have hapos : 0 < a := Nat.pos_of_mem_divisors ha
    have hqpos : 0 < n / a := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hadvd) hapos
    have hphiA0 : (Nat.totient a : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hapos))
    have hphiQ0 : (Nat.totient (n / a) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hqpos))
    rw [hphi]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_div]
  have hsum : (∑ a ∈ n.divisors,
      (Nat.totient (n / a) : ℝ)) = (n : ℝ) := by
    exact_mod_cast
      (Nat.sum_div_divisors n Nat.totient).trans (Nat.sum_totient n)
  rw [hsum]

private theorem radical_ratio {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / (n.totient : ℝ) =
      ((UniqueFactorizationMonoid.radical (M := ℕ) n : ℕ) : ℝ) /
        (Nat.totient
          (UniqueFactorizationMonoid.radical (M := ℕ) n) : ℝ) := by
  let r : ℕ := UniqueFactorizationMonoid.radical (M := ℕ) n
  have hr : 0 < r := Nat.radical_pos n
  have hphiNQ : (n.totient : ℚ) =
      (n : ℚ) * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors n
  have hphiRQ : (r.totient : ℚ) =
      (r : ℚ) * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors r]
    congr 2
    exact Nat.primeFactors_radical n
  have hphiN : (n.totient : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using congrArg (Rat.castHom ℝ) hphiNQ
  have hphiR : (r.totient : ℝ) =
      (r : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using congrArg (Rat.castHom ℝ) hphiRQ
  have hphiN0 : (n.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hn).ne'
  have hphiR0 : (r.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hr).ne'
  apply (div_eq_div_iff hphiN0 hphiR0).2
  rw [hphiN, hphiR]
  ring

/-- The reciprocal totient of any positive natural is a sum over its
squarefree divisors. The ambient natural need not itself be squarefree. -/
theorem inv_totient_eq_sum_squarefree_divisors
    {n : ℕ} (hn : 0 < n) :
    (Nat.totient n : ℝ)⁻¹ =
      ∑ d ∈ n.divisors.filter Squarefree,
        (1 : ℝ) / ((n : ℝ) * Nat.totient d) := by
  let r : ℕ := UniqueFactorizationMonoid.radical (M := ℕ) n
  have hr : 0 < r := Nat.radical_pos n
  have hratio := radical_ratio hn
  have hfilter : n.divisors.filter Squarefree = r.divisors := by
    ext d
    constructor
    · intro hd
      have hdf := Finset.mem_filter.mp hd
      have hdn := (Nat.mem_divisors.mp hdf.1).1
      have hdr : d ∣ r :=
        (UniqueFactorizationMonoid.dvd_radical_iff
          hdf.2.isRadical hn.ne').2 hdn
      exact Nat.mem_divisors.mpr ⟨hdr, (Nat.radical_pos n).ne'⟩
    · intro hd
      have hdr := (Nat.mem_divisors.mp hd).1
      have hsq : Squarefree d :=
        UniqueFactorizationMonoid.squarefree_radical.squarefree_of_dvd hdr
      have hdn : d ∣ n :=
        (UniqueFactorizationMonoid.dvd_radical_iff
          hsq.isRadical hn.ne').1 hdr
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdn, hn.ne'⟩, hsq⟩
  have hsum := squarefree_div_totient_eq_sum_divisors_inv_totient
    (UniqueFactorizationMonoid.squarefree_radical (a := n))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (Nat.totient n : ℝ)⁻¹ =
        (1 / (n : ℝ)) * ((n : ℝ) / Nat.totient n) := by field_simp
    _ = (1 / (n : ℝ)) * ((r : ℝ) / Nat.totient r) := by
      rw [show r = UniqueFactorizationMonoid.radical (M := ℕ) n by rfl]
      rw [hratio]
    _ = (1 / (n : ℝ)) *
        ∑ d ∈ r.divisors, (Nat.totient d : ℝ)⁻¹ := by rw [hsum]
    _ = ∑ d ∈ n.divisors.filter Squarefree,
        (1 : ℝ) / ((n : ℝ) * Nat.totient d) := by
      rw [hfilter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

private def squarefreePositiveDivisors (K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter Squarefree

/-- Sum of reciprocal Euler totients over all positive naturals at most `K`. -/
def reciprocalTotientPrefix (K : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ Finset.Ioc 0 K, (Nat.totient k : ℝ)⁻¹

/-- Bound the full reciprocal-totient prefix by the squarefree convolution
coefficient and the harmonic number. -/
theorem reciprocalTotientPrefix_le_coefficient_mul_harmonic (K : ℕ) :
    reciprocalTotientPrefix K ≤
      squarefreeInvNatTotientSum K * ((harmonic K : ℚ) : ℝ) := by
  classical
  let S : Finset (Σ _n : ℕ, ℕ) :=
    (Finset.Ioc 0 K).sigma (fun n => n.divisors.filter Squarefree)
  let f : (Σ _n : ℕ, ℕ) → ℕ × ℕ :=
    fun x => (x.2, x.1 / x.2)
  let A : Finset ℕ := squarefreePositiveDivisors K
  let B : Finset ℕ := Finset.Icc 1 K
  let g : ℕ × ℕ → ℝ := fun ab =>
    (1 : ℝ) / ((ab.1 : ℝ) * Nat.totient ab.1) * (1 / (ab.2 : ℝ))
  have hinj : Set.InjOn f S := by
    intro x hx y hy hxy
    have hxmem := Finset.mem_sigma.mp hx
    have hymem := Finset.mem_sigma.mp hy
    have hd : x.2 = y.2 := congrArg Prod.fst hxy
    have hprod : x.2 * (x.1 / x.2) = y.2 * (y.1 / y.2) :=
      congrArg (fun z : ℕ × ℕ => z.1 * z.2) hxy
    apply Sigma.ext
    · calc
        x.1 = x.2 * (x.1 / x.2) :=
          (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hxmem.2).1)).symm
        _ = y.2 * (y.1 / y.2) := hprod
        _ = y.1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors
          (Finset.mem_filter.mp hymem.2).1)
    · simp [hd]
  have himage : S.image f ⊆ A ×ˢ B := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxmem := Finset.mem_sigma.mp hx
    have hn := Finset.mem_Ioc.mp hxmem.1
    have hdmem := Finset.mem_filter.mp hxmem.2
    have hdvd := Nat.dvd_of_mem_divisors hdmem.1
    have hnpos : 0 < x.1 := hn.1
    have hdpos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdvd hnpos
    have hdle : x.2 ≤ x.1 := Nat.le_of_dvd hnpos hdvd
    have hmpos : 0 < x.1 / x.2 := Nat.div_pos hdle hdpos
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hdpos, hdle.trans hn.2⟩, hdmem.2⟩, ?_⟩
    exact Finset.mem_Icc.mpr
      ⟨hmpos, (Nat.div_le_self _ _).trans hn.2⟩
  calc
    reciprocalTotientPrefix K =
        ∑ n ∈ Finset.Ioc 0 K,
          ∑ d ∈ n.divisors.filter Squarefree,
            (1 : ℝ) / ((n : ℝ) * Nat.totient d) := by
      unfold reciprocalTotientPrefix
      apply Finset.sum_congr rfl
      intro n hn
      exact inv_totient_eq_sum_squarefree_divisors (Finset.mem_Ioc.mp hn).1
    _ = ∑ x ∈ S, (1 : ℝ) / ((x.1 : ℝ) * Nat.totient x.2) := by
      unfold S
      rw [Finset.sum_sigma']
    _ = ∑ x ∈ S, g (f x) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxmem := Finset.mem_sigma.mp hx
      have hdvd := Nat.dvd_of_mem_divisors
        (Finset.mem_filter.mp hxmem.2).1
      have hprod : x.2 * (x.1 / x.2) = x.1 := Nat.mul_div_cancel' hdvd
      have hprodR : (x.1 : ℝ) =
          (x.2 : ℝ) * (x.1 / x.2 : ℕ) := by
        exact_mod_cast hprod.symm
      dsimp [g, f]
      rw [hprodR]
      ring
    _ = ∑ z ∈ S.image f, g z := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    _ ≤ ∑ z ∈ A ×ˢ B, g z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro z hz hznot
      unfold g
      positivity
    _ = squarefreeInvNatTotientSum K * ((harmonic K : ℚ) : ℝ) := by
      unfold A B g squarefreePositiveDivisors
      rw [Finset.sum_product]
      calc
        (∑ d ∈ (Finset.Icc 1 K).filter Squarefree,
            ∑ m ∈ Finset.Icc 1 K,
              (1 : ℝ) / ((d : ℝ) * Nat.totient d) *
                (1 / (m : ℝ))) =
            ∑ d ∈ (Finset.Icc 1 K).filter Squarefree,
              ((1 : ℝ) / ((d : ℝ) * Nat.totient d)) *
                (∑ m ∈ Finset.Icc 1 K, (1 / (m : ℝ))) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
        _ = (∑ d ∈ Finset.Icc 1 K,
              if Squarefree d then
                (1 : ℝ) / ((d : ℝ) * Nat.totient d) else 0) *
            (∑ m ∈ Finset.Icc 1 K, (1 / (m : ℝ))) := by
          rw [← Finset.sum_filter]
          rw [Finset.sum_mul]
        _ = squarefreeInvNatTotientSum K * ((harmonic K : ℚ) : ℝ) := by
          rw [show (∑ d ∈ Finset.Icc 1 K,
                if Squarefree d then
                  (1 : ℝ) / ((d : ℝ) * Nat.totient d) else 0) =
              squarefreeInvNatTotientSum K by rfl]
          rw [harmonic_eq_sum_Icc]
          norm_num [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Uniform full reciprocal-totient prefix bound with explicit constant `4`. -/
theorem reciprocalTotientPrefix_le_four_mul_harmonic (K : ℕ) :
    reciprocalTotientPrefix K ≤ 4 * ((harmonic K : ℚ) : ℝ) := by
  calc
    reciprocalTotientPrefix K ≤
        squarefreeInvNatTotientSum K * ((harmonic K : ℚ) : ℝ) :=
      reciprocalTotientPrefix_le_coefficient_mul_harmonic K
    _ ≤ 4 * ((harmonic K : ℚ) : ℝ) := by
      apply mul_le_mul_of_nonneg_right (squarefreeInvNatTotientSum_le_four K)
      rw [harmonic_eq_sum_Icc]
      norm_num [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      positivity

/-- Logarithmic full-prefix bound at positive natural endpoints. -/
theorem reciprocalTotientPrefix_le_four_mul_one_add_log
    {K : ℕ} (hK : 0 < K) :
    reciprocalTotientPrefix K ≤ 4 * (1 + Real.log K) := by
  calc
    reciprocalTotientPrefix K ≤ 4 * ((harmonic K : ℚ) : ℝ) :=
      reciprocalTotientPrefix_le_four_mul_harmonic K
    _ ≤ 4 * (1 + Real.log K) := by
      apply mul_le_mul_of_nonneg_left
      · have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
        simpa [ne_of_gt hKreal] using harmonic_le_one_add_log K
      · norm_num

end

end BoundedGaps.Maynard
