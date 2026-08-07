import BoundedGaps.Maynard.MaynardLambdaQuotients

noncomputable section

/-!
# Quotient-product fibers in the Maynard lambda bound

Maynard2013v3, equation `eq:LambdaSize` (source lines 304--316), counts the
quotient tuples of fixed product by `tau_k`. This file defines the exact finite
quotient support and embeds each product fiber into Mathlib's multiplicative
antidiagonal.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance quotientFiberDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def lambdaAuxiliaryTupleSupport
    (H : Finset ℕ) (R : ℕ) (d : H → ℕ) : Finset (H → ℕ) :=
  (maynardDivisorTupleBox H R).filter fun r =>
    divisorTupleProduct H r < R ∧
      (∀ h : H, d h ∣ r h) ∧
      Squarefree (divisorTupleProduct H r)

def lambdaQuotientTupleSupport
    (H : Finset ℕ) (R : ℕ) (d : H → ℕ) : Finset (H → ℕ) :=
  (lambdaAuxiliaryTupleSupport H R d).image (divisorTupleQuotient d)

theorem mem_lambdaAuxiliaryTupleSupport_iff
    {H : Finset ℕ} {R : ℕ} {d r : H → ℕ} :
    r ∈ lambdaAuxiliaryTupleSupport H R d ↔
      r ∈ maynardDivisorTupleBox H R ∧
      divisorTupleProduct H r < R ∧
      (∀ h : H, d h ∣ r h) ∧
      Squarefree (divisorTupleProduct H r) := by
  simp [lambdaAuxiliaryTupleSupport]

theorem lambdaQuotientTupleSupport_data
    {H : Finset ℕ} {R W : ℕ} {d s : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (hs : s ∈ lambdaQuotientTupleSupport H R d) :
    (∀ h : H, 0 < s h) ∧
      divisorTupleProduct H d * divisorTupleProduct H s < R ∧
      Squarefree (divisorTupleProduct H s) ∧
      Nat.Coprime (divisorTupleProduct H d) (divisorTupleProduct H s) := by
  classical
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hrData := mem_lambdaAuxiliaryTupleSupport_iff.mp hr
  have hdpos : ∀ h : H, 0 < d h := fun h =>
    Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero
  have hrpos : ∀ h : H, 0 < r h := fun h =>
    zero_lt_one.trans_le ((mem_maynardDivisorTupleBox_iff.mp hrData.1) h).1
  refine ⟨fun h => divisorTupleQuotient_coordinate_pos hdpos hrpos
      hrData.2.2.1 h, ?_, ?_, ?_⟩
  · exact (divisorTupleProduct_quotient_cutoff_iff hrData.2.2.1).mpr
      hrData.2.1
  · exact (squarefree_divisorTupleProduct_and_quotient
      hrData.2.2.1 hrData.2.2.2).2
  · exact coprime_divisorTupleProduct_quotient
      hrData.2.2.1 hrData.2.2.2

def lambdaQuotientFinEncoding
    (H : Finset ℕ) (s : H → ℕ) : Fin (Fintype.card H) → ℕ :=
  fun i => s ((Fintype.equivFin H).symm i)

theorem lambdaQuotientFinEncoding_prod
    (H : Finset ℕ) (s : H → ℕ) :
    (∏ i, lambdaQuotientFinEncoding H s i) = divisorTupleProduct H s := by
  unfold divisorTupleProduct
  apply Fintype.prod_equiv (Fintype.equivFin H).symm
  intro i
  rfl

theorem lambdaQuotientFinEncoding_injective (H : Finset ℕ) :
    Function.Injective (lambdaQuotientFinEncoding H) := by
  intro s t hst
  funext h
  have hh := congrFun hst ((Fintype.equivFin H) h)
  simpa [lambdaQuotientFinEncoding] using hh

theorem lambdaQuotientProductFiberCard_le_finMulAntidiag
    {H : Finset ℕ} {R W t : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    modulusFiberCard (lambdaQuotientTupleSupport H R d)
        (divisorTupleProduct H) t ≤
      (Nat.finMulAntidiag (Fintype.card H) t).card := by
  unfold modulusFiberCard
  apply Finset.card_le_card_of_injOn (lambdaQuotientFinEncoding H)
  · intro s hs
    have hsData := Finset.mem_filter.mp hs
    have hsupport := lambdaQuotientTupleSupport_data hd hsData.1
    apply Nat.mem_finMulAntidiag.mpr
    refine ⟨?_, ?_⟩
    · rw [lambdaQuotientFinEncoding_prod]
      exact hsData.2
    · rw [← hsData.2]
      unfold divisorTupleProduct
      exact (Finset.prod_pos fun h hh => hsupport.1 h).ne'
  · exact (lambdaQuotientFinEncoding_injective H).injOn

theorem squarefree_of_mem_lambdaQuotientProduct_image
    {H : Finset ℕ} {R W t : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (ht : t ∈ (lambdaQuotientTupleSupport H R d).image
      (divisorTupleProduct H)) :
    Squarefree t := by
  classical
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  exact (lambdaQuotientTupleSupport_data hd hs).2.2.1

theorem lambdaQuotientProductFiberCard_le_tauPow
    {H : Finset ℕ} {R W t : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (ht : t ∈ (lambdaQuotientTupleSupport H R d).image
      (divisorTupleProduct H)) :
    modulusFiberCard (lambdaQuotientTupleSupport H R d)
        (divisorTupleProduct H) t ≤
      (Fintype.card H) ^ ω t := by
  calc
    modulusFiberCard (lambdaQuotientTupleSupport H R d)
        (divisorTupleProduct H) t ≤
        (Nat.finMulAntidiag (Fintype.card H) t).card :=
      lambdaQuotientProductFiberCard_le_finMulAntidiag hd
    _ = (Fintype.card H) ^ ω t :=
      Nat.card_finMulAntidiag_of_squarefree
        (squarefree_of_mem_lambdaQuotientProduct_image hd ht)

end BoundedGaps.Maynard
