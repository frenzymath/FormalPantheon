import BoundedGaps.Maynard.CoprimeHarmonicExpansion
import BoundedGaps.Maynard.CoprimeHarmonicQuotientEndpoint

noncomputable section

/-!
# Squarefree coprime-harmonic error bound

The divisor expansion from Maynard2013v3/GGPY2009 is evaluated for an
arbitrary squarefree modulus. At endpoints containing every divisor of the
modulus, the Euler--Mascheroni and natural-quotient errors give an explicit
finite discrepancy envelope.
-/

namespace BoundedGaps.Maynard
open Finset Nat Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

private theorem sum_powerset_prod_mul_sum_general
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

private theorem moebius_prod_div_prod_general {W : ℕ}
    {t : Finset ℕ} (ht : t ⊆ W.primeFactors) :
    (ArithmeticFunction.moebius (∏ p ∈ t, p) : ℝ) /
        (∏ p ∈ t, p : ℕ) =
      ∏ p ∈ t, (-(1 : ℝ) / p) := by
  have htPrime : ∀ p ∈ t, p.Prime := fun p hp =>
    (Nat.mem_primeFactors.mp (ht hp)).1
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

private theorem log_prod_primes_general {W : ℕ}
    {t : Finset ℕ} (ht : t ⊆ W.primeFactors) :
    Real.log (∏ p ∈ t, p : ℕ) = ∑ p ∈ t, Real.log p := by
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.mem_primeFactors.mp (ht hp)).1.ne_zero

theorem mobiusDivisorDensity_eq
    {W : ℕ} (hSq : Squarefree W) :
    (∑ d ∈ W.divisors, (ArithmeticFunction.moebius d : ℝ) / d) =
      (Nat.totient W : ℝ) / W := by
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
      invId hmult hSq
  simp_rw [hinvId] at hEuler
  have hDensity : (Nat.totient W : ℝ) / W =
      ∏ p ∈ W.primeFactors, (1 - (1 : ℝ) / p) := by
    have htot := Nat.totient_mul_prod_primeFactors W
    have hEqR := congrArg (fun n : ℕ => (n : ℝ)) htot
    norm_num only [Nat.cast_mul, Nat.cast_prod] at hEqR
    have hprodPos : 0 < ∏ p ∈ W.primeFactors, (p : ℝ) := by
      exact Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.pos_of_mem_primeFactors hp)
    have hWReal : (0 : ℝ) < W := by
      exact_mod_cast (Nat.pos_of_ne_zero hSq.ne_zero)
    have hEqR' : (Nat.totient W : ℝ) *
          (∏ p ∈ W.primeFactors, (p : ℝ)) =
        (W : ℝ) * ∏ p ∈ W.primeFactors, ((p : ℝ) - 1) := by
      calc
        _ = (W : ℝ) * ∏ p ∈ W.primeFactors, ((p - 1 : ℕ) : ℝ) := hEqR
        _ = _ := by
          congr 1
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
          norm_num
    have hprodDiv :
        (∏ p ∈ W.primeFactors, (1 - (1 : ℝ) / p)) =
          (∏ p ∈ W.primeFactors, ((p : ℝ) - 1)) /
            (∏ p ∈ W.primeFactors, (p : ℝ)) := by
      calc
        _ = ∏ p ∈ W.primeFactors, (((p : ℝ) - 1) / p) := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpPos : (0 : ℝ) < p := by
            exact_mod_cast (Nat.pos_of_mem_primeFactors hp)
          field_simp
        _ = _ := by rw [Finset.prod_div_distrib]
    rw [hprodDiv]
    field_simp [hWReal.ne', hprodPos.ne']
    nlinarith [hEqR']
  rw [hDensity, hEuler]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem mobiusDivisorLogMoment_eq
    {W : ℕ} (hSq : Squarefree W) :
    (∑ d ∈ W.divisors,
      (ArithmeticFunction.moebius d : ℝ) / d * Real.log d) =
      -((Nat.totient W : ℝ) / W) *
        primeLogPredecessorDivisorMass W := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hSq,
    Nat.sum_divisors_filter_squarefree hSq.ne_zero, Nat.factors_eq]
  simp_rw [Finset.prod_val]
  change (∑ t ∈ W.primeFactors.powerset,
      (ArithmeticFunction.moebius (∏ p ∈ t, p) : ℝ) /
        (∏ p ∈ t, p : ℕ) * Real.log (∏ p ∈ t, p : ℕ)) = _
  calc
    (∑ t ∈ W.primeFactors.powerset,
        (ArithmeticFunction.moebius (∏ p ∈ t, p) : ℝ) /
            (∏ p ∈ t, p : ℕ) * Real.log (∏ p ∈ t, p : ℕ)) =
        ∑ t ∈ W.primeFactors.powerset,
          (∏ p ∈ t, (-(1 : ℝ) / p)) * ∑ p ∈ t, Real.log p := by
      apply Finset.sum_congr rfl
      intro t ht
      have htSub := Finset.mem_powerset.mp ht
      rw [moebius_prod_div_prod_general htSub, log_prod_primes_general htSub]
    _ = ∑ p ∈ W.primeFactors,
        Real.log p * (-(1 : ℝ) / p) *
          ∏ q ∈ W.primeFactors.erase p, (1 - (1 : ℝ) / q) := by
      rw [sum_powerset_prod_mul_sum_general]
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      apply Finset.prod_congr rfl
      intro q hq
      ring
    _ = -((Nat.totient W : ℝ) / W) *
        primeLogPredecessorDivisorMass W := by
      have hDensity : (Nat.totient W : ℝ) / W =
          ∏ p ∈ W.primeFactors, (1 - (1 : ℝ) / p) := by
        have hEuler := mobiusDivisorDensity_eq hSq
        let invId : ArithmeticFunction ℝ :=
          ArithmeticFunction.pdiv
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
            (ArithmeticFunction.id : ArithmeticFunction ℝ)
        have hinvId (n : ℕ) : invId n = (1 : ℝ) / n := by
          unfold invId
          simp only [ArithmeticFunction.pdiv_apply,
            ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
          by_cases hn : n = 0
          · simp [hn]
          · rw [ArithmeticFunction.zeta_apply_ne hn]
            norm_num
        have hmult : invId.IsMultiplicative :=
          ArithmeticFunction.isMultiplicative_zeta.natCast.pdiv
            ArithmeticFunction.isMultiplicative_id.natCast
        have hprod :=
          ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
            invId hmult hSq
        simp_rw [hinvId] at hprod
        calc
          (Nat.totient W : ℝ) / W =
              ∑ d ∈ W.divisors,
                (ArithmeticFunction.moebius d : ℝ) / d := hEuler.symm
          _ = ∑ d ∈ W.divisors,
                (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / d) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
          _ = ∏ p ∈ W.primeFactors, (1 - (1 : ℝ) / p) := hprod.symm
      unfold primeLogPredecessorDivisorMass
      have hmass : ∀ p ∈ W.primeFactors, p.Prime := fun p hp =>
        (Nat.mem_primeFactors.mp hp).1
      rw [hDensity, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := hmass p hp
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hpPredPos : (0 : ℝ) < (p - 1 : ℕ) := by
        exact_mod_cast Nat.sub_pos_of_lt hpPrime.one_lt
      have hpPredReal : (0 : ℝ) < (p : ℝ) - 1 := by
        have hpOne : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
        linarith
      have hprod := Finset.mul_prod_erase W.primeFactors
        (fun q => (1 - (1 : ℝ) / q)) hp
      have hfactor : (1 - (1 : ℝ) / p) =
          ((p - 1 : ℕ) : ℝ) / p := by
        rw [Nat.cast_sub hpPrime.one_le]
        norm_num
        field_simp
      rw [hfactor] at hprod
      rw [← hprod]
      rw [Nat.cast_sub hpPrime.one_le]
      norm_num only [Nat.cast_one]
      field_simp [hpPos.ne', hpPredPos.ne', hpPredReal.ne']

theorem mobiusLogMainTerm_eq_coprimeHarmonicMainTerm
    {W Q : ℕ} (hSq : Squarefree W) (hQ : 0 < Q) :
    (∑ d ∈ W.divisors,
        (ArithmeticFunction.moebius d : ℝ) / d *
          (Real.log ((Q : ℝ) / d) + Real.eulerMascheroniConstant)) =
      coprimeHarmonicMainTerm W Q := by
  have hlog : ∀ d ∈ W.divisors,
      Real.log ((Q : ℝ) / d) = Real.log Q - Real.log d := by
    intro d hd
    have hdPos := Nat.pos_of_mem_divisors hd
    rw [Real.log_div (by exact_mod_cast hQ.ne')
      (by exact_mod_cast hdPos.ne')]
  calc
    (∑ d ∈ W.divisors,
        (ArithmeticFunction.moebius d : ℝ) / d *
          (Real.log ((Q : ℝ) / d) + Real.eulerMascheroniConstant)) =
        ∑ d ∈ W.divisors,
          ((ArithmeticFunction.moebius d : ℝ) / d *
              (Real.log Q + Real.eulerMascheroniConstant) -
            (ArithmeticFunction.moebius d : ℝ) / d * Real.log d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hlog d hd]
      ring
    _ = (∑ d ∈ W.divisors,
          (ArithmeticFunction.moebius d : ℝ) / d) *
            (Real.log Q + Real.eulerMascheroniConstant) -
        ∑ d ∈ W.divisors,
          (ArithmeticFunction.moebius d : ℝ) / d * Real.log d := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = coprimeHarmonicMainTerm W Q := by
      rw [mobiusDivisorDensity_eq hSq, mobiusDivisorLogMoment_eq hSq]
      unfold coprimeHarmonicMainTerm coprimeHarmonicDensity
      ring

theorem abs_coprimeHarmonicError_le_divisor_envelope
    {W Q : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hWQ : W ≤ Q) :
    |coprimeHarmonicError W Q| ≤
      2 * (W.divisors.card : ℝ) / Q +
        Real.log 2 * ∑ d ∈ W.divisors, (1 : ℝ) / d := by
  have hQ : 0 < Q := hW.trans_le hWQ
  unfold coprimeHarmonicError
  rw [coprimeHarmonicSum_eq_moebius_harmonic hW,
    ← mobiusLogMainTerm_eq_coprimeHarmonicMainTerm hSq hQ,
    ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ W.divisors,
        ((ArithmeticFunction.moebius d : ℝ) / d * realHarmonic (Q / d) -
          (ArithmeticFunction.moebius d : ℝ) / d *
            (Real.log ((Q : ℝ) / d) + Real.eulerMascheroniConstant))| =
        |∑ d ∈ W.divisors,
          (ArithmeticFunction.moebius d : ℝ) / d *
            (realHarmonic (Q / d) - Real.log ((Q : ℝ) / d) -
              Real.eulerMascheroniConstant)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ∑ d ∈ W.divisors,
        |(ArithmeticFunction.moebius d : ℝ) / d *
          (realHarmonic (Q / d) - Real.log ((Q : ℝ) / d) -
            Real.eulerMascheroniConstant)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ W.divisors,
        ((2 : ℝ) / Q + Real.log 2 / d) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdPos := Nat.pos_of_mem_divisors hd
      have hdW := Nat.le_of_dvd hW (Nat.dvd_of_mem_divisors hd)
      have hdQ : d ≤ Q := hdW.trans hWQ
      have hquotPos : 0 < Q / d := Nat.div_pos hdQ hdPos
      have hEuler :=
        abs_realHarmonic_sub_log_sub_eulerMascheroni_le hquotPos
      have hFloor := abs_log_natDiv_sub_log_div_le_log_two hdPos hdQ
      have hTotal :
          |realHarmonic (Q / d) - Real.log ((Q : ℝ) / d) -
              Real.eulerMascheroniConstant| ≤
            (1 : ℝ) / (Q / d : ℕ) + Real.log 2 := by
        calc
          |realHarmonic (Q / d) - Real.log ((Q : ℝ) / d) -
              Real.eulerMascheroniConstant| =
              |(realHarmonic (Q / d) - Real.log (Q / d : ℕ) -
                  Real.eulerMascheroniConstant) +
                (Real.log (Q / d : ℕ) - Real.log ((Q : ℝ) / d))| := by
            congr 1
            ring
          _ ≤ |realHarmonic (Q / d) - Real.log (Q / d : ℕ) -
                  Real.eulerMascheroniConstant| +
                |Real.log (Q / d : ℕ) - Real.log ((Q : ℝ) / d)| :=
            abs_add_le _ _
          _ ≤ (1 : ℝ) / (Q / d : ℕ) + Real.log 2 :=
            add_le_add hEuler hFloor
      have hmuInt := ArithmeticFunction.abs_moebius_le_one (n := d)
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast hmuInt
      have hdReal : (0 : ℝ) < d := by exact_mod_cast hdPos
      have hweight :
          |(ArithmeticFunction.moebius d : ℝ) / d| ≤ (1 : ℝ) / d := by
        rw [abs_div, abs_of_pos hdReal]
        exact div_le_div_of_nonneg_right hmu hdReal.le
      have hQlt : Q < (Q / d + 1) * d := by
        have hmod := Nat.mod_lt Q hdPos
        have hdecomp := Nat.div_add_mod Q d
        calc
          Q = d * (Q / d) + Q % d := hdecomp.symm
          _ < d * (Q / d) + d := Nat.add_lt_add_left hmod _
          _ = (Q / d + 1) * d := by ring
      have hsuccLe : Q / d + 1 ≤ 2 * (Q / d) := by omega
      have hQle : Q ≤ 2 * (d * (Q / d)) := by
        nlinarith [hQlt, Nat.mul_le_mul_right d hsuccLe]
      have hprodPos : (0 : ℝ) < d * (Q / d : ℕ) := by
        exact_mod_cast Nat.mul_pos hdPos hquotPos
      have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
      have hHarmonic :
          (1 : ℝ) / d * ((1 : ℝ) / (Q / d : ℕ)) ≤ (2 : ℝ) / Q := by
        calc
          (1 : ℝ) / d * ((1 : ℝ) / (Q / d : ℕ)) =
              (1 : ℝ) / ((d : ℝ) * (Q / d : ℕ)) := by field_simp
          _ ≤ (2 : ℝ) / Q := by
            rw [div_le_div_iff₀ hprodPos hQReal]
            norm_num
            exact_mod_cast hQle
      rw [abs_mul]
      calc
        |(ArithmeticFunction.moebius d : ℝ) / d| *
            |realHarmonic (Q / d) - Real.log ((Q : ℝ) / d) -
              Real.eulerMascheroniConstant| ≤
            (1 : ℝ) / d *
              ((1 : ℝ) / (Q / d : ℕ) + Real.log 2) := by
          exact mul_le_mul hweight hTotal (abs_nonneg _) (by positivity)
        _ = ((1 : ℝ) / d * ((1 : ℝ) / (Q / d : ℕ))) +
            Real.log 2 / d := by ring
        _ ≤ (2 : ℝ) / Q + Real.log 2 / d :=
          add_le_add hHarmonic le_rfl
    _ = 2 * (W.divisors.card : ℝ) / Q +
        Real.log 2 * ∑ d ∈ W.divisors, (1 : ℝ) / d := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro d hd
        ring
end BoundedGaps.Maynard
