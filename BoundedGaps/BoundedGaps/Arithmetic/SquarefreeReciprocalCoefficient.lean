import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Shared squarefree reciprocal-totient coefficient bounds

This file owns the elementary finite arithmetic estimates used by both the
Maynard packet and the Bombieri--Vinogradov packet. Declarations retain the
historical `BoundedGaps.Maynard` namespace for compatibility.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

theorem one_div_nat_sq_le_two_mul_telescoping
    {m : ℕ} (hm : 0 < m) :
    (1 : ℝ) / (m : ℝ) ^ 2 ≤
      2 * ((1 : ℝ) / m - 1 / (m + 1)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmOneR : (1 : ℝ) ≤ m := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne')
  have hm1R : (0 : ℝ) < m + 1 := by positivity
  field_simp [ne_of_gt hmR, ne_of_gt hm1R]
  ring_nf
  nlinarith

theorem sum_Ico_one_div_nat_sq_le
    {D Q : ℕ} (hD : 0 < D) (hDQ : D ≤ Q) :
    (∑ m ∈ Finset.Ico D Q, (1 : ℝ) / (m : ℝ) ^ 2) ≤
      2 / (D : ℝ) := by
  calc
    (∑ m ∈ Finset.Ico D Q, (1 : ℝ) / (m : ℝ) ^ 2) ≤
        ∑ m ∈ Finset.Ico D Q,
          2 * ((1 : ℝ) / m - 1 / (m + 1)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact one_div_nat_sq_le_two_mul_telescoping
        (lt_of_lt_of_le hD (Finset.mem_Ico.mp hm).1)
    _ = 2 * ((1 : ℝ) / D - 1 / Q) := by
      rw [← Finset.mul_sum]
      have htel := Finset.sum_Ico_sub (fun m : ℕ => -((1 : ℝ) / m)) hDQ
      simpa only [neg_sub_neg, Nat.cast_add, Nat.cast_one] using
        congrArg (fun x : ℝ => 2 * x) htel
    _ ≤ 2 / (D : ℝ) := by
      have hQnonneg : (0 : ℝ) ≤ 1 / Q := by positivity
      have hle : 2 * ((1 : ℝ) / D - 1 / Q) ≤ 2 * (1 / D) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ hQnonneg) (by norm_num)
      calc
        2 * ((1 : ℝ) / D - 1 / Q) ≤ 2 * (1 / D) := hle
        _ = 2 / (D : ℝ) := by ring

theorem squarefree_le_totient_mul_card_divisors
    {n : ℕ} (hn : Squarefree n) :
    n ≤ n.totient * n.divisors.card := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have htot : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,
      Nat.prod_primeFactors_of_squarefree hn,
      Nat.div_self (Nat.pos_of_ne_zero hn0), one_mul]
  have hcard : n.divisors.card = ∏ p ∈ n.primeFactors, 2 := by
    rw [Nat.card_divisors hn0]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hn
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
  calc
    n = ∏ p ∈ n.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hn).symm
    _ ≤ ∏ p ∈ n.primeFactors, ((p - 1) * 2) := by
      refine Finset.prod_le_prod (fun p hp => Nat.zero_le _) ?_
      intro p hp
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    _ = (∏ p ∈ n.primeFactors, (p - 1)) *
        ∏ p ∈ n.primeFactors, 2 := by
      rw [Finset.prod_mul_distrib]
    _ = n.totient * n.divisors.card := by rw [htot, hcard]

theorem inv_totient_le_card_divisors_div
    {n : ℕ} (hn : Squarefree n) :
    (Nat.totient n : ℝ)⁻¹ ≤ (n.divisors.card : ℝ) / n := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have hφpos : 0 < n.totient := Nat.totient_pos.mpr hnpos
  have hnat := squarefree_le_totient_mul_card_divisors hn
  have hreal : (n : ℝ) ≤ (n.totient : ℝ) * n.divisors.card := by
    exact_mod_cast hnat
  rw [inv_eq_one_div]
  rw [div_le_div_iff₀ (by exact_mod_cast hφpos) (by exact_mod_cast hnpos)]
  simpa [mul_comm] using hreal

def squarefreeInvNatTotientSum (Q : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 Q,
    if Squarefree d then (1 : ℝ) / ((d : ℝ) * Nat.totient d) else 0

private def positiveProductPairsSq (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter
    (fun ab => ab.1 * ab.2 ≤ Q)

theorem sum_card_divisors_div_sq_eq_productPairSum (Q : ℕ) :
    (∑ n ∈ Finset.Icc 1 Q, (n.divisors.card : ℝ) / (n : ℝ) ^ 2) =
      ∑ ab ∈ positiveProductPairsSq Q,
        (1 : ℝ) / ((ab.1 : ℝ) ^ 2 * (ab.2 : ℝ) ^ 2) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 Q,
        (n.divisors.card : ℝ) / (n : ℝ) ^ 2) =
        ∑ n ∈ Finset.Icc 1 Q, ∑ _d ∈ n.divisors,
          (1 : ℝ) / (n : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ∑ x ∈ (Finset.Icc 1 Q).sigma (fun n => n.divisors),
        (1 : ℝ) / (x.1 : ℝ) ^ 2 := by
      rw [Finset.sum_sigma']
    _ = ∑ ab ∈ positiveProductPairsSq Q,
        (1 : ℝ) / ((ab.1 : ℝ) ^ 2 * (ab.2 : ℝ) ^ 2) := by
      refine Finset.sum_bij'
        (fun x _ => (x.2, x.1 / x.2))
        (fun ab _ => ⟨ab.1 * ab.2, ab.1⟩) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        have hn := Finset.mem_Icc.mp hmem.1
        have hdvd := (Nat.mem_divisors.mp hmem.2).1
        have hnPos : 0 < x.1 := zero_lt_one.trans_le hn.1
        have hdPos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdvd hnPos
        have hdLe : x.2 ≤ x.1 := Nat.le_of_dvd hnPos hdvd
        have hqPos : 0 < x.1 / x.2 := Nat.div_pos hdLe hdPos
        simp only [positiveProductPairsSq, Finset.mem_filter,
          Finset.mem_product]
        exact ⟨⟨Finset.mem_Icc.mpr ⟨hdPos, hdLe.trans hn.2⟩,
          Finset.mem_Icc.mpr ⟨hqPos, (Nat.div_le_self _ _).trans hn.2⟩⟩,
          (Nat.mul_div_cancel' hdvd).trans_le hn.2⟩
      · intro ab hab
        simp only [positiveProductPairsSq, Finset.mem_filter,
          Finset.mem_product] at hab
        have haPos := (Finset.mem_Icc.mp hab.1.1).1
        have hbPos := (Finset.mem_Icc.mp hab.1.2).1
        apply Finset.mem_sigma.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos haPos hbPos, hab.2⟩,
          Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right _ _,
            (Nat.mul_pos haPos hbPos).ne'⟩⟩
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        apply Sigma.ext
        · exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hmem.2)
        · simp
      · intro ab hab
        simp only [positiveProductPairsSq, Finset.mem_filter,
          Finset.mem_product] at hab
        exact Prod.ext rfl (Nat.mul_div_cancel_left _
          (Finset.mem_Icc.mp hab.1.1).1)
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        have hprod : (x.1 : ℝ) =
            (x.2 : ℝ) * (x.1 / x.2 : ℕ) := by
          exact_mod_cast (Nat.mul_div_cancel'
            (Nat.dvd_of_mem_divisors hmem.2)).symm
        rw [hprod]
        ring

theorem sum_card_divisors_div_sq_le_four (Q : ℕ) :
    (∑ n ∈ Finset.Icc 1 Q, (n.divisors.card : ℝ) / (n : ℝ) ^ 2) ≤ 4 := by
  rw [sum_card_divisors_div_sq_eq_productPairSum]
  calc
    (∑ ab ∈ positiveProductPairsSq Q,
        (1 : ℝ) / ((ab.1 : ℝ) ^ 2 * (ab.2 : ℝ) ^ 2)) ≤
        ∑ ab ∈ (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q),
          (1 : ℝ) / ((ab.1 : ℝ) ^ 2 * (ab.2 : ℝ) ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro ab hab habNot
        positivity
    _ = (∑ a ∈ Finset.Icc 1 Q, (1 : ℝ) / (a : ℝ) ^ 2) ^ 2 := by
      rw [Finset.sum_product]
      calc
        (∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ Finset.Icc 1 Q,
            (1 : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ) ^ 2)) =
            ∑ a ∈ Finset.Icc 1 Q,
              ((1 : ℝ) / (a : ℝ) ^ 2) *
                (∑ b ∈ Finset.Icc 1 Q, (1 : ℝ) / (b : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = (∑ a ∈ Finset.Icc 1 Q, (1 : ℝ) / (a : ℝ) ^ 2) ^ 2 := by
          rw [← Finset.sum_mul, pow_two]
    _ ≤ 4 := by
      have htail := sum_Ico_one_div_nat_sq_le (D := 1) (Q := Q + 1)
        Nat.zero_lt_one (by omega)
      have hsum : (∑ a ∈ Finset.Icc 1 Q,
          (1 : ℝ) / (a : ℝ) ^ 2) ≤ 2 := by
        have hinterval : Finset.Ico 1 (Q + 1) = Finset.Icc 1 Q := by
          ext x
          simp
        rw [hinterval] at htail
        norm_num at htail
        simpa only [one_div] using htail
      have hnonneg : 0 ≤ ∑ a ∈ Finset.Icc 1 Q,
          (1 : ℝ) / (a : ℝ) ^ 2 := by
        apply Finset.sum_nonneg
        intro a ha
        exact div_nonneg zero_le_one (sq_nonneg (a : ℝ))
      nlinarith

theorem squarefreeInvNatTotientSum_nonneg (Q : ℕ) :
    0 ≤ squarefreeInvNatTotientSum Q := by
  unfold squarefreeInvNatTotientSum
  apply Finset.sum_nonneg
  intro d hd
  by_cases hsq : Squarefree d
  · rw [if_pos hsq]
    exact div_nonneg zero_le_one
      (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d.totient))
  · rw [if_neg hsq]

theorem squarefreeInvNatTotientSum_le_four (Q : ℕ) :
    squarefreeInvNatTotientSum Q ≤ 4 := by
  unfold squarefreeInvNatTotientSum
  calc
    (∑ d ∈ Finset.Icc 1 Q,
        if Squarefree d then (1 : ℝ) / ((d : ℝ) * Nat.totient d) else 0) ≤
        ∑ d ∈ Finset.Icc 1 Q,
          (d.divisors.card : ℝ) / (d : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hsq : Squarefree d
      · rw [if_pos hsq]
        have hinv := inv_totient_le_card_divisors_div hsq
        have hdNonneg : (0 : ℝ) ≤ 1 / d := by positivity
        calc
          (1 : ℝ) / ((d : ℝ) * Nat.totient d) =
              (1 / (d : ℝ)) * (Nat.totient d : ℝ)⁻¹ := by ring
          _ ≤ (1 / (d : ℝ)) * ((d.divisors.card : ℝ) / d) :=
            mul_le_mul_of_nonneg_left hinv hdNonneg
          _ = (d.divisors.card : ℝ) / (d : ℝ) ^ 2 := by ring
      · rw [if_neg hsq]
        positivity
    _ ≤ 4 := sum_card_divisors_div_sq_le_four Q

end

end BoundedGaps.Maynard
