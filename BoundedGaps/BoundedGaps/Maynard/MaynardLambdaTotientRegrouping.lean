import BoundedGaps.Maynard.MaynardLambdaQuotientFibers

noncomputable section

/-!
# Totient factorization and quotient-product regrouping for lambda

Maynard2013v3, equation `eq:LambdaSize` (source lines 304--316), replaces the
tuple denominator by the totient of the total squarefree product and groups
quotient tuples by that product. This file proves those exact finite steps.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance totientRegroupingDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem divisorTupleCoordinatePair_mul_dvd_product
    {H : Finset ℕ} (r : H → ℕ) {a b : H} (hab : a ≠ b) :
    r a * r b ∣ divisorTupleProduct H r := by
  classical
  let s : Finset H := Finset.univ.erase a
  have hb : b ∈ s := by simp [s, Ne.symm hab]
  refine ⟨∏ h ∈ s.erase b, r h, ?_⟩
  unfold divisorTupleProduct
  rw [← Finset.prod_erase_mul Finset.univ r (Finset.mem_univ a)]
  rw [← Finset.prod_erase_mul s r hb]
  ring

theorem divisorTupleCoordinates_coprime_of_squarefree_product
    {H : Finset ℕ} {r : H → ℕ}
    (hr : Squarefree (divisorTupleProduct H r))
    {a b : H} (hab : a ≠ b) :
    Nat.Coprime (r a) (r b) := by
  apply Nat.coprime_of_squarefree_mul
  exact hr.squarefree_of_dvd
    (divisorTupleCoordinatePair_mul_dvd_product r hab)

theorem totient_finsetProd_of_pairwise_coprime
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℕ)
    (hpair : Set.Pairwise (s : Set ι) (Function.onFun Nat.Coprime r)) :
    Nat.totient (∏ i ∈ s, r i) = ∏ i ∈ s, Nat.totient (r i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | @cons a s ha ih =>
      rw [Finset.coe_cons, Set.pairwise_insert] at hpair
      rw [Finset.prod_cons, Finset.prod_cons, Nat.totient_mul]
      · rw [ih hpair.1]
      · apply Nat.Coprime.prod_right
        intro i hi
        exact hpair.2 i (by simp [hi]) (fun hai => ha (hai ▸ hi)) |>.1

theorem totient_divisorTupleProduct_eq_prod
    {H : Finset ℕ} {r : H → ℕ}
    (hr : Squarefree (divisorTupleProduct H r)) :
    Nat.totient (divisorTupleProduct H r) =
      ∏ h : H, Nat.totient (r h) := by
  unfold divisorTupleProduct
  apply totient_finsetProd_of_pairwise_coprime
  intro a ha b hb hab
  exact divisorTupleCoordinates_coprime_of_squarefree_product hr hab

def lambdaQuotientWeightSum
    (H : Finset ℕ) (R : ℕ) (d : H → ℕ) : ℝ :=
  ∑ s ∈ lambdaQuotientTupleSupport H R d,
    (divisorTupleProduct H d : ℝ) /
      (Nat.totient
        (divisorTupleProduct H d * divisorTupleProduct H s) : ℝ)

theorem lambdaQuotientWeightSum_eq_fiber_sum
    (H : Finset ℕ) (R : ℕ) (d : H → ℕ) :
    lambdaQuotientWeightSum H R d =
      ∑ t ∈ (lambdaQuotientTupleSupport H R d).image
          (divisorTupleProduct H),
        (modulusFiberCard (lambdaQuotientTupleSupport H R d)
          (divisorTupleProduct H) t : ℝ) *
        ((divisorTupleProduct H d : ℝ) /
          (Nat.totient (divisorTupleProduct H d * t) : ℝ)) := by
  unfold lambdaQuotientWeightSum
  exact sum_comp_eq_sum_modulusFiberCard
    (lambdaQuotientTupleSupport H R d) (divisorTupleProduct H)
      (fun t => (divisorTupleProduct H d : ℝ) /
        (Nat.totient (divisorTupleProduct H d * t) : ℝ))

theorem lambdaQuotientWeightSum_le_tau_fiber_sum
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    lambdaQuotientWeightSum H R d ≤
      ∑ t ∈ (lambdaQuotientTupleSupport H R d).image
          (divisorTupleProduct H),
        ((Fintype.card H) ^ ω t : ℕ) *
        ((divisorTupleProduct H d : ℝ) /
          (Nat.totient (divisorTupleProduct H d * t) : ℝ)) := by
  rw [lambdaQuotientWeightSum_eq_fiber_sum]
  apply Finset.sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast lambdaQuotientProductFiberCard_le_tauPow hd ht
  · positivity

end BoundedGaps.Maynard
