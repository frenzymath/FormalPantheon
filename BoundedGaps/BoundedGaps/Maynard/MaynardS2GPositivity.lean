import BoundedGaps.Maynard.MaynardS2OuterTupleFactorization
import Mathlib.NumberTheory.Primorial

noncomputable section

/-!
# Positivity of the supported S2 `g`-factor

For a primorial cutoff at least two, every prime factor of a supported
coordinate is at least three. The totally multiplicative `g(p)=p-2` factor is
therefore positive on every supported coordinate and tuple product.
-/

namespace BoundedGaps.Maynard

theorem maynardS2G_pos_of_squarefree_coprime_primorial
    {D n : ℕ} (hD : 2 ≤ D) (hn : Squarefree n)
    (hcop : Nat.Coprime n (primorial D)) :
    0 < maynardS2G n := by
  by_cases hnOne : n = 1
  · subst n
    simp [maynardS2G]
  rw [maynardS2G_apply hn.ne_zero]
  apply Finset.prod_pos
  intro p hpMem
  have hp := Nat.prime_of_mem_primeFactors hpMem
  have hpDvd := Nat.dvd_of_mem_primeFactors hpMem
  have hpGt : D < p := by
    by_contra hnot
    have hpLe : p ≤ D := Nat.le_of_not_gt hnot
    have hpW : p ∣ primorial D := hp.dvd_primorial_iff.mpr hpLe
    have hpc : Nat.Coprime p (primorial D) :=
      Nat.Coprime.of_dvd_left hpDvd hcop
    exact hp.ne_one (hpc.eq_one_of_dvd hpW)
  have hp3 : 3 ≤ p := by omega
  exact_mod_cast (Nat.sub_pos_of_lt hp3)

theorem maynardS2G_product_pos_of_supported
    {H : Finset ℕ} {D R : ℕ} (hD : 2 ≤ D)
    {r : H → ℕ} (hr : IsMaynardDivisorTuple H R (primorial D) r) :
    0 < ∏ h : H, (maynardS2G (r h) : ℝ) := by
  apply Finset.prod_pos
  intro h hh
  exact_mod_cast maynardS2G_pos_of_squarefree_coprime_primorial hD
    (hr.coordinate_squarefree h) (hr.coordinate_coprime_W h)

end BoundedGaps.Maynard
