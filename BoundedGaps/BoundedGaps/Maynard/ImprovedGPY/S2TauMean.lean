import BoundedGaps.Maynard.ImprovedGPY.S2TauFiber
import BoundedGaps.Maynard.MaynardArithmeticBounds

noncomputable section

/-!
# A finite squarefree tau mean bound for S2

Maynard2013v3, in the Cauchy--Schwarz estimate for the error in
`lmm:S2Expression1` (source lines 365--369), uses a fixed logarithmic-power
bound for `sum mu(r)^2 tau_d(r)^2 / phi(r)`.  This file proves an explicit
finite harmonic-power bound by reindexing ordered multiplicative
antidiagonals into a positive tuple box.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance tauMeanDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem sum_inv_product_positiveProductTuples_le_harmonic
    (ι : Type*) [Fintype ι] (Q : ℕ) :
    (∑ a ∈ positiveProductTuples ι Q,
        (∏ i, (a i : ℝ))⁻¹) ≤
      ((harmonic Q : ℚ) : ℝ) ^ Fintype.card ι := by
  classical
  let box : Finset (ι → ℕ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc 1 Q)
  have hsubset : positiveProductTuples ι Q ⊆ box := by
    intro a ha
    apply Fintype.mem_piFinset.mpr
    exact (mem_positiveProductTuples_iff.mp ha).1
  calc
    (∑ a ∈ positiveProductTuples ι Q, (∏ i, (a i : ℝ))⁻¹) ≤
        ∑ a ∈ box, (∏ i, (a i : ℝ))⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro a ha _
      positivity
    _ = ∏ _i : ι, ∑ n ∈ Finset.Icc 1 Q, (n : ℝ)⁻¹ := by
      dsimp [box]
      simp_rw [← Finset.prod_inv_distrib]
      rw [Finset.sum_prod_piFinset (Finset.Icc 1 Q)
        (fun _ n => (n : ℝ)⁻¹)]
    _ = (∑ n ∈ Finset.Icc 1 Q, (n : ℝ)⁻¹) ^ Fintype.card ι := by
      rw [Finset.prod_const, Finset.card_univ]
    _ = ((harmonic Q : ℚ) : ℝ) ^ Fintype.card ι := by
      congr 1
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem card_divisors_eq_two_pow_omega {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ ω n := by
  rw [Nat.card_divisors hn.ne_zero]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1)) =
        ∏ _p ∈ n.primeFactors, 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hn
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    _ = 2 ^ n.primeFactors.card := by simp
    _ = 2 ^ ω n := by rw [omega_eq_card_primeFactors]

private theorem tauSquare_mul_twoPow (d w : ℕ) :
    (d ^ w) ^ 2 * 2 ^ w = (2 * d ^ 2) ^ w := by
  rw [mul_pow]
  rw [← pow_mul, ← pow_mul]
  rw [Nat.mul_comm w 2, Nat.mul_comm (d ^ (2 * w)) (2 ^ w)]

theorem squarefree_tauPow_sq_div_totient_le
    (d : ℕ) {n : ℕ} (hn : Squarefree n) :
    (((d ^ ω n : ℕ) : ℝ) ^ 2) / (Nat.totient n : ℝ) ≤
      (((2 * d ^ 2) ^ ω n : ℕ) : ℝ) / n := by
  have hinv := inv_totient_le_card_divisors_div hn
  calc
    (((d ^ ω n : ℕ) : ℝ) ^ 2) / (Nat.totient n : ℝ) =
        (((d ^ ω n : ℕ) : ℝ) ^ 2) * (Nat.totient n : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ (((d ^ ω n : ℕ) : ℝ) ^ 2) *
        ((n.divisors.card : ℝ) / n) :=
      mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = (((2 * d ^ 2) ^ ω n : ℕ) : ℝ) / n := by
      rw [card_divisors_eq_two_pow_omega hn]
      push_cast
      rw [← mul_div_assoc]
      congr 1
      exact_mod_cast tauSquare_mul_twoPow d (ω n)

private def finMulAntidiagSigma (d Q : ℕ) :
    Finset (Σ _n : ℕ, Fin d → ℕ) :=
  (Finset.Icc 1 Q).sigma fun n => Nat.finMulAntidiag d n

theorem sum_card_finMulAntidiag_div_eq_sum_inv_product
    (d Q : ℕ) :
    (∑ n ∈ Finset.Icc 1 Q,
        ((Nat.finMulAntidiag d n).card : ℝ) / n) =
      ∑ a ∈ positiveProductTuples (Fin d) Q,
        (∏ i, (a i : ℝ))⁻¹ := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 Q,
        ((Nat.finMulAntidiag d n).card : ℝ) / n) =
        ∑ n ∈ Finset.Icc 1 Q, ∑ _a ∈ Nat.finMulAntidiag d n,
          (n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ = ∑ x ∈ finMulAntidiagSigma d Q, (x.1 : ℝ)⁻¹ := by
      rw [finMulAntidiagSigma, Finset.sum_sigma']
    _ = ∑ a ∈ positiveProductTuples (Fin d) Q,
        (∏ i, (a i : ℝ))⁻¹ := by
      refine Finset.sum_bij'
        (fun x _ => x.2)
        (fun a _ => ⟨∏ i, a i, a⟩) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        have hn := Finset.mem_Icc.mp hmem.1
        have hprod := Nat.prod_eq_of_mem_finMulAntidiag hmem.2
        rw [mem_positiveProductTuples_iff]
        refine ⟨?_, hprod.trans_le hn.2⟩
        intro i
        have hne := Nat.ne_zero_of_mem_finMulAntidiag hmem.2 i
        have hdvd := Nat.dvd_of_mem_finMulAntidiag hmem.2 i
        have hnpos : 0 < x.1 := zero_lt_one.trans_le hn.1
        exact Finset.mem_Icc.mpr
          ⟨Nat.pos_of_ne_zero hne, (Nat.le_of_dvd hnpos hdvd).trans hn.2⟩
      · intro a ha
        have hmem := mem_positiveProductTuples_iff.mp ha
        have hprod_pos : 0 < ∏ i, a i := by
          apply Finset.prod_pos
          intro i hi
          exact (Finset.mem_Icc.mp (hmem.1 i)).1
        rw [finMulAntidiagSigma, Finset.mem_sigma]
        exact ⟨Finset.mem_Icc.mpr ⟨hprod_pos, hmem.2⟩,
          Nat.mem_finMulAntidiag.mpr ⟨rfl, hprod_pos.ne'⟩⟩
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        apply Sigma.ext
        · exact Nat.prod_eq_of_mem_finMulAntidiag hmem.2
        · simp
      · intro a ha
        rfl
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        have hprodR : (x.1 : ℝ) = ∏ i, (x.2 i : ℝ) := by
          exact_mod_cast (Nat.prod_eq_of_mem_finMulAntidiag hmem.2).symm
        rw [hprodR]

theorem sum_card_finMulAntidiag_div_le_harmonic
    (d Q : ℕ) :
    (∑ n ∈ Finset.Icc 1 Q,
        ((Nat.finMulAntidiag d n).card : ℝ) / n) ≤
      ((harmonic Q : ℚ) : ℝ) ^ d := by
  rw [sum_card_finMulAntidiag_div_eq_sum_inv_product]
  simpa using sum_inv_product_positiveProductTuples_le_harmonic (Fin d) Q

def squarefreeTauMean (d Q : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Q,
    if Squarefree n then
      (((d ^ ω n : ℕ) : ℝ) ^ 2) / (Nat.totient n : ℝ)
    else 0

theorem squarefreeTauMean_le_harmonic (d Q : ℕ) :
    squarefreeTauMean d Q ≤
      ((harmonic Q : ℚ) : ℝ) ^ (2 * d ^ 2) := by
  unfold squarefreeTauMean
  calc
    (∑ n ∈ Finset.Icc 1 Q,
        if Squarefree n then
          (((d ^ ω n : ℕ) : ℝ) ^ 2) / (Nat.totient n : ℝ)
        else 0) ≤
        ∑ n ∈ Finset.Icc 1 Q,
          ((Nat.finMulAntidiag (2 * d ^ 2) n).card : ℝ) / n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hsq : Squarefree n
      · rw [if_pos hsq]
        calc
          (((d ^ ω n : ℕ) : ℝ) ^ 2) / (Nat.totient n : ℝ) ≤
              (((2 * d ^ 2) ^ ω n : ℕ) : ℝ) / n :=
            squarefree_tauPow_sq_div_totient_le d hsq
          _ = ((Nat.finMulAntidiag (2 * d ^ 2) n).card : ℝ) / n := by
            rw [Nat.card_finMulAntidiag_of_squarefree hsq]
      · rw [if_neg hsq]
        positivity
    _ ≤ ((harmonic Q : ℚ) : ℝ) ^ (2 * d ^ 2) :=
      sum_card_finMulAntidiag_div_le_harmonic (2 * d ^ 2) Q

theorem squarefreeTauMean_le_one_add_log (d Q : ℕ) :
    squarefreeTauMean d Q ≤
      (1 + Real.log Q) ^ (2 * d ^ 2) := by
  refine (squarefreeTauMean_le_harmonic d Q).trans ?_
  have hnonneg : 0 ≤ ((harmonic Q : ℚ) : ℝ) := by
    by_cases hQ : Q = 0
    · simp [hQ, harmonic]
    · rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun n _ =>
        inv_nonneg.mpr (Nat.cast_nonneg n)
  have hle : ((harmonic Q : ℚ) : ℝ) ≤ 1 + Real.log Q :=
    harmonic_le_one_add_log Q
  exact pow_le_pow_left₀ hnonneg hle _

end BoundedGaps.Maynard
