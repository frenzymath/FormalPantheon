import BoundedGaps.Maynard.CoprimeHarmonicExpansion
import BoundedGaps.Maynard.PreSieveLocalSeries
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

namespace BoundedGaps.Maynard

open Finset Nat Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable def primorialMobiusDensity (D : ℕ) : ℝ :=
  ∑ d ∈ (primorial D).divisors,
    (ArithmeticFunction.moebius d : ℝ) / d

theorem primorialMobiusDensity_eq_totient_div (D : ℕ) :
    primorialMobiusDensity D =
    (Nat.totient (primorial D) : ℝ) / primorial D := by
  let invId : ArithmeticFunction ℝ :=
    ArithmeticFunction.pdiv (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      (ArithmeticFunction.id : ArithmeticFunction ℝ)
  have hinvId (n : ℕ) : invId n = (1 : ℝ) / n := by
    unfold invId
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.id_apply]
    by_cases hn : n = 0
    · simp [hn]
    · rw [ArithmeticFunction.zeta_apply_ne hn]
      norm_num
  have hmult : invId.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.pdiv
      ArithmeticFunction.isMultiplicative_id.natCast
  have hEuler :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      invId hmult (squarefree_primorial D)
  rw [primeFactors_primorial] at hEuler
  simp_rw [hinvId] at hEuler
  have hseries : preSieveSingularSeries D =
      ∑ d ∈ (primorial D).divisors,
        (ArithmeticFunction.moebius d : ℝ) / d := by
    rw [preSieveSingularSeries]
    calc
      (∏ p ∈ Nat.primesLE D, (1 - (1 : ℝ) / p)) =
          ∑ d ∈ (primorial D).divisors,
            (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / d) := hEuler
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        ring
  unfold primorialMobiusDensity
  rw [← hseries, preSieveSingularSeries_eq_totient_div]

private theorem sum_powerset_prod_mul_sum
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (a b : ι → ℝ) :
    (∑ t ∈ P.powerset, (∏ p ∈ t, a p) * ∑ p ∈ t, b p) =
      ∑ p ∈ P, b p * a p * ∏ q ∈ P.erase p, (1 + a q) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert x P hx ih =>
      rw [Finset.sum_powerset_insert hx]
      have hxmem {t : Finset ι} (ht : t ∈ P.powerset) : x ∉ t := by
        exact fun hxt => hx (Finset.mem_powerset.mp ht hxt)
      have hins :
          (∑ t ∈ P.powerset,
              (∏ p ∈ insert x t, a p) * ∑ p ∈ insert x t, b p) =
            a x * b x * (∏ q ∈ P, (1 + a q)) +
              a x * (∑ t ∈ P.powerset,
                (∏ p ∈ t, a p) * ∑ p ∈ t, b p) := by
        calc
          (∑ t ∈ P.powerset,
              (∏ p ∈ insert x t, a p) * ∑ p ∈ insert x t, b p) =
              ∑ t ∈ P.powerset,
                (a x * ∏ p ∈ t, a p) * (b x + ∑ p ∈ t, b p) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.prod_insert (hxmem ht), Finset.sum_insert (hxmem ht)]
          _ = a x * b x * (∑ t ∈ P.powerset, ∏ p ∈ t, a p) +
              a x * (∑ t ∈ P.powerset,
                (∏ p ∈ t, a p) * ∑ p ∈ t, b p) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
            congr 1
            · calc
                (∑ t ∈ P.powerset, (a x * ∏ p ∈ t, a p) * b x) =
                    ∑ t ∈ P.powerset, (a x * b x) * ∏ p ∈ t, a p := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  ring
                _ = a x * b x * (∑ t ∈ P.powerset, ∏ p ∈ t, a p) := by
                  rw [Finset.mul_sum]
            · calc
                (∑ t ∈ P.powerset,
                    (a x * ∏ p ∈ t, a p) * ∑ p ∈ t, b p) =
                    ∑ t ∈ P.powerset,
                      a x * ((∏ p ∈ t, a p) * ∑ p ∈ t, b p) := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  ring
                _ = a x * (∑ t ∈ P.powerset,
                    (∏ p ∈ t, a p) * ∑ p ∈ t, b p) := by
                  rw [Finset.mul_sum]
          _ = _ := by rw [← Finset.prod_one_add]
      rw [hins, ih, Finset.sum_insert hx]
      have heraseX : (insert x P).erase x = P := by simp [hx]
      rw [heraseX]
      have hrest :
          (∑ p ∈ P, b p * a p *
            ∏ q ∈ (insert x P).erase p, (1 + a q)) =
            (1 + a x) *
              ∑ p ∈ P, b p * a p * ∏ q ∈ P.erase p, (1 + a q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpx : p ≠ x := (ne_of_mem_of_not_mem hp hx)
        have hxErase : x ∉ P.erase p := by simp [hx]
        have herase : (insert x P).erase p = insert x (P.erase p) := by
          ext q
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hqp, hqx | hqP⟩
            · exact Or.inl hqx
            · exact Or.inr ⟨hqp, hqP⟩
          · rintro (hqx | ⟨hqp, hqP⟩)
            · subst q
              exact ⟨hpx.symm, Or.inl rfl⟩
            · exact ⟨hqp, Or.inr hqP⟩
        rw [herase, Finset.prod_insert hxErase]
        ring
      rw [hrest]
      ring

noncomputable def primorialMobiusLogMoment (D : ℕ) : ℝ :=
  ∑ d ∈ (primorial D).divisors,
    (ArithmeticFunction.moebius d : ℝ) / d * Real.log d

private theorem moebius_prod_div_prod {D : ℕ}
    {t : Finset ℕ} (ht : t ⊆ Nat.primesLE D) :
    (ArithmeticFunction.moebius (∏ p ∈ t, p) : ℝ) /
        (∏ p ∈ t, p : ℕ) =
      ∏ p ∈ t, (-(1 : ℝ) / p) := by
  have htPrime : ∀ p ∈ t, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesLE (ht hp)
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime
    t htPrime
  rw [hmu]
  push_cast
  calc
    (∏ p ∈ t, (ArithmeticFunction.moebius p : ℝ)) /
          ∏ p ∈ t, (p : ℝ) =
        (∏ p ∈ t, (-(1 : ℝ))) / ∏ p ∈ t, (p : ℝ) := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      rw [ArithmeticFunction.moebius_apply_prime (htPrime p hp)]
      norm_num
    _ = ∏ p ∈ t, (-(1 : ℝ) / p) := by
      rw [Finset.prod_div_distrib]

private theorem log_prod_primes {D : ℕ}
    {t : Finset ℕ} (ht : t ⊆ Nat.primesLE D) :
    Real.log (∏ p ∈ t, p : ℕ) = ∑ p ∈ t, Real.log p := by
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.prime_of_mem_primesLE (ht hp)).ne_zero

theorem primorialMobiusLogMoment_eq (D : ℕ) :
    primorialMobiusLogMoment D =
    -preSieveSingularSeries D *
      ∑ p ∈ Nat.primesLE D, Real.log p / (p - 1 : ℕ) := by
  classical
  have hsq := squarefree_primorial D
  unfold primorialMobiusLogMoment
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsq,
    Nat.sum_divisors_filter_squarefree hsq.ne_zero, Nat.factors_eq]
  simp_rw [Finset.prod_val]
  change (∑ t ∈ (primorial D).primeFactors.powerset,
      (ArithmeticFunction.moebius (∏ p ∈ t, p) : ℝ) /
        (∏ p ∈ t, p : ℕ) * Real.log (∏ p ∈ t, p : ℕ)) = _
  rw [primeFactors_primorial]
  calc
    (∑ t ∈ (Nat.primesLE D).powerset,
        (ArithmeticFunction.moebius (∏ p ∈ t, p) : ℝ) /
            (∏ p ∈ t, p : ℕ) * Real.log (∏ p ∈ t, p : ℕ)) =
        ∑ t ∈ (Nat.primesLE D).powerset,
          (∏ p ∈ t, (-(1 : ℝ) / p)) * ∑ p ∈ t, Real.log p := by
      apply Finset.sum_congr rfl
      intro t ht
      have htSub := Finset.mem_powerset.mp ht
      rw [moebius_prod_div_prod htSub, log_prod_primes htSub]
    _ = ∑ p ∈ Nat.primesLE D,
        Real.log p * (-(1 : ℝ) / p) *
          ∏ q ∈ (Nat.primesLE D).erase p, (1 - (1 : ℝ) / q) := by
      rw [sum_powerset_prod_mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      apply Finset.prod_congr rfl
      intro q hq
      ring
    _ = -preSieveSingularSeries D *
        ∑ p ∈ Nat.primesLE D, Real.log p / (p - 1 : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := Nat.prime_of_mem_primesLE hp
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hpPredPos : (0 : ℝ) < (p - 1 : ℕ) := by
        exact_mod_cast Nat.sub_pos_of_lt hpPrime.one_lt
      unfold preSieveSingularSeries
      have hprod := Finset.mul_prod_erase (Nat.primesLE D)
        (fun q => (1 - (1 : ℝ) / q)) hp
      rw [show (1 - (1 : ℝ) / p) = (p - 1 : ℕ) / (p : ℝ) by
        rw [Nat.cast_sub hpPrime.one_le]; field_simp; ring] at hprod
      rw [← hprod]
      field_simp

end BoundedGaps.Maynard
