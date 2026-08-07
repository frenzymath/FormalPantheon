import BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthCoefficient
import BoundedGaps.BombieriVinogradov.Analytic.VaughanTwistedDecomposition

/-!
# Vaughan's fourth-term endpoint reindex

This file rewrites the fourth Vaughan term as the exact positive factor-pair
sum used before the dyadic decomposition in Akbary--Hambrook2013v2,
Section 6, pp. 22--23. The source's outer minus sign is retained.

Semantic review: `SEM-458`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Positive factor pairs in the fourth Vaughan term at endpoint `y`. -/
def vaughanFourthPairIndices (U V : ℝ) (y : ℕ) : Finset (ℕ × ℕ) :=
  (positiveFactorPairs y).filter (fun mk ↦
    U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ))

private theorem mem_positiveFactorPairs_iff
    {y : ℕ} (p : ℕ × ℕ) :
    p ∈ positiveFactorPairs y ↔
      p.1 ∈ Finset.Icc 1 y ∧ p.2 ∈ Finset.Icc 1 (y / p.1) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact ⟨Finset.mem_Icc.mpr ⟨hp₁.1, hp₁.2⟩,
      Finset.mem_Icc.mpr ⟨hp₂.1,
        (Nat.le_div_iff_mul_le hp₁.1).mpr (by
          simpa only [Nat.mul_comm] using hprod)⟩⟩
  · rintro ⟨hm, hk⟩
    rw [Finset.mem_Icc] at hm hk
    have hprod : p.1 * p.2 ≤ y := by
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hm.1).mp hk.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr hm,
          Finset.mem_Ioc.mpr
            ⟨hk.1, hk.2.trans (Nat.div_le_self y p.1)⟩⟩,
        hprod⟩

/-- Exact positive factor-pair form of the fourth Vaughan term. -/
theorem vaughanTwistedSumFour_eq_sum_positiveFactorPairs
    (U V : ℝ) (y q : ℕ) (chi : DirichletCharacter ℂ q) :
    vaughanTwistedSumFour U V y q chi =
      -∑ mk ∈ vaughanFourthPairIndices U V y,
        ((ArithmeticFunction.vonMangoldt mk.1 : ℝ) : ℂ) *
          ((vaughanFourthCoefficient V mk.2 : ℝ) : ℂ) *
          chi (mk.1 * mk.2) := by
  let f : ℕ → ℕ → ℂ := fun m k ↦
    if U < (m : ℝ) ∧ V < (k : ℝ) then
      ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
        ((vaughanFourthCoefficient V k : ℝ) : ℂ) * chi (m * k)
    else 0
  unfold vaughanTwistedSumFour
  calc
    (∑ n ∈ Finset.Icc 1 y,
        chi n *
          ((-∑ mk ∈ n.divisorsAntidiagonal.filter
              (fun mk : ℕ × ℕ ↦
                U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
              ArithmeticFunction.vonMangoldt mk.1 *
                ∑ d ∈ mk.2.divisors.filter
                  (fun d : ℕ ↦ (d : ℝ) ≤ V),
                  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d : ℝ) : ℂ)) =
        -(∑ n ∈ Finset.Ioc 0 y,
          ∑ mk ∈ n.divisorsAntidiagonal, f mk.1 mk.2) := by
      rw [show Finset.Icc 1 y = Finset.Ioc 0 y by
        simpa using Finset.Icc_succ_left_eq_Ioc 0 y]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Complex.ofReal_neg, Complex.ofReal_sum, mul_neg, neg_inj,
        Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mk hmk
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hmk).1
      by_cases hcut : U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)
      · simp only [if_pos hcut, f]
        rw [← hprod, Complex.ofReal_mul,
          show (∑ d ∈ mk.2.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ V),
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d) =
              vaughanFourthCoefficient V mk.2 by rfl]
        simp only [Nat.cast_mul, map_mul]
        ring
      · simp only [f, if_neg hcut]
        simp
    _ = -(∑ mk ∈ positiveFactorPairs y, f mk.1 mk.2) := by
      rw [sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs f]
    _ = -∑ mk ∈ vaughanFourthPairIndices U V y,
        ((ArithmeticFunction.vonMangoldt mk.1 : ℝ) : ℂ) *
          ((vaughanFourthCoefficient V mk.2 : ℝ) : ℂ) *
          chi (mk.1 * mk.2) := by
      unfold vaughanFourthPairIndices
      rw [Finset.sum_filter]

/-- Nested source form with the exact endpoint support `m*k ≤ y`. -/
theorem vaughanTwistedSumFour_eq_nestedFactorSum
    (U V : ℝ) (y q : ℕ) (chi : DirichletCharacter ℂ q) :
    vaughanTwistedSumFour U V y q chi =
      -∑ m ∈ (Finset.Icc 1 y).filter (fun m : ℕ ↦ U < (m : ℝ)),
        ∑ k ∈ (Finset.Icc 1 (y / m)).filter (fun k : ℕ ↦ V < (k : ℝ)),
          ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
            ((vaughanFourthCoefficient V k : ℝ) : ℂ) * chi (m * k) := by
  rw [vaughanTwistedSumFour_eq_sum_positiveFactorPairs]
  apply congrArg Neg.neg
  let f : ℕ → ℕ → ℂ := fun m k ↦
    ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
      ((vaughanFourthCoefficient V k : ℝ) : ℂ) * chi (m * k)
  change (∑ mk ∈ vaughanFourthPairIndices U V y, f mk.1 mk.2) = _
  rw [vaughanFourthPairIndices, Finset.sum_filter]
  calc
    (∑ mk ∈ positiveFactorPairs y,
        if U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ) then f mk.1 mk.2 else 0) =
        ∑ m ∈ Finset.Icc 1 y,
          ∑ k ∈ Finset.Icc 1 (y / m),
            if U < (m : ℝ) ∧ V < (k : ℝ) then f m k else 0 := by
      exact Finset.sum_finset_product
        (positiveFactorPairs y) (Finset.Icc 1 y)
        (fun m ↦ Finset.Icc 1 (y / m)) mem_positiveFactorPairs_iff
    _ = ∑ m ∈ (Finset.Icc 1 y).filter (fun m : ℕ ↦ U < (m : ℝ)),
        ∑ k ∈ (Finset.Icc 1 (y / m)).filter (fun k : ℕ ↦ V < (k : ℝ)),
          f m k := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hmU : U < (m : ℝ)
      · simp only [if_true, hmU, true_and]
      · simp only [if_false, hmU, false_and, Finset.sum_const_zero]

end

end BoundedGaps.Maynard
