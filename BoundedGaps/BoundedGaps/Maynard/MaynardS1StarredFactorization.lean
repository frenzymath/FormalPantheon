import BoundedGaps.Maynard.MaynardS1StarredYSum
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

noncomputable section

/-!
# Totient factorization for starred S1 cross tuples

The starred coprimality conditions turn every row and column lcm into a
product.  Consequently both lower-tuple totient products factor into one
totient for each common variable and one for each cross variable.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def outgoingCrossIndices (H : Finset ℕ) (h : H) :
    Finset ↑(offDiagonalPairs H) :=
  (offDiagonalPairs H).attach.filter (fun x => x.1.1 = h)

def incomingCrossIndices (H : Finset ℕ) (h : H) :
    Finset ↑(offDiagonalPairs H) :=
  (offDiagonalPairs H).attach.filter (fun x => x.1.2 = h)

def outgoingCrossProduct
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (h : H) : ℕ :=
  ∏ x ∈ outgoingCrossIndices H h, s x.1 x.2

def incomingCrossProduct
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (h : H) : ℕ :=
  ∏ x ∈ incomingCrossIndices H h, s x.1 x.2

def crossTotientProduct
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : ℕ :=
  ∏ x ∈ (offDiagonalPairs H).attach, Nat.totient (s x.1 x.2)

theorem outgoingCross_pairwise
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    Set.Pairwise (outgoingCrossIndices H h : Set ↑(offDiagonalPairs H))
      (Function.onFun Nat.Coprime (fun x => s x.1 x.2)) := by
  intro x hx z hz hxz
  have hxFirst := (Finset.mem_filter.mp hx).2
  have hzFirst := (Finset.mem_filter.mp hz).2
  apply hstar.2 x.1 z.1 x.2 z.2
  · intro hxzPair
    apply hxz
    exact Subtype.ext hxzPair
  · exact Or.inl (hxFirst.trans hzFirst.symm)

theorem incomingCross_pairwise
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    Set.Pairwise (incomingCrossIndices H h : Set ↑(offDiagonalPairs H))
      (Function.onFun Nat.Coprime (fun x => s x.1 x.2)) := by
  intro x hx z hz hxz
  have hxSecond := (Finset.mem_filter.mp hx).2
  have hzSecond := (Finset.mem_filter.mp hz).2
  apply hstar.2 x.1 z.1 x.2 z.2
  · intro hxzPair
    apply hxz
    exact Subtype.ext hxzPair
  · exact Or.inr (hxSecond.trans hzSecond.symm)

theorem outgoingCrossLcm_eq_product
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    outgoingCrossLcm H s h = outgoingCrossProduct H s h := by
  unfold outgoingCrossLcm outgoingCrossProduct outgoingCrossIndices
  exact Finset.lcm_eq_prod (outgoingCross_pairwise hstar h)

theorem incomingCrossLcm_eq_product
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    incomingCrossLcm H s h = incomingCrossProduct H s h := by
  unfold incomingCrossLcm incomingCrossProduct incomingCrossIndices
  exact Finset.lcm_eq_prod (incomingCross_pairwise hstar h)

theorem u_coprime_outgoingCrossProduct
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    Nat.Coprime (u h) (outgoingCrossProduct H s h) := by
  unfold outgoingCrossProduct
  apply Nat.Coprime.prod_right
  intro x hx
  have hxFirst := (Finset.mem_filter.mp hx).2
  simpa [hxFirst] using (hstar.1 x.1 x.2).1.symm

theorem u_coprime_incomingCrossProduct
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    Nat.Coprime (u h) (incomingCrossProduct H s h) := by
  unfold incomingCrossProduct
  apply Nat.Coprime.prod_right
  intro x hx
  have hxSecond := (Finset.mem_filter.mp hx).2
  simpa [hxSecond] using (hstar.1 x.1 x.2).2.symm

theorem totient_outgoingCrossProduct
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    Nat.totient (outgoingCrossProduct H s h) =
      ∏ x ∈ outgoingCrossIndices H h, Nat.totient (s x.1 x.2) := by
  unfold outgoingCrossProduct
  exact totient_finsetProd_of_pairwise_coprime _ _
    (outgoingCross_pairwise hstar h)

theorem totient_incomingCrossProduct
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    Nat.totient (incomingCrossProduct H s h) =
      ∏ x ∈ incomingCrossIndices H h, Nat.totient (s x.1 x.2) := by
  unfold incomingCrossProduct
  exact totient_finsetProd_of_pairwise_coprime _ _
    (incomingCross_pairwise hstar h)

theorem totient_leftCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    Nat.totient (leftCrossLowerTuple H u s h) =
      Nat.totient (u h) *
        ∏ x ∈ outgoingCrossIndices H h, Nat.totient (s x.1 x.2) := by
  rw [leftCrossLowerTuple, outgoingCrossLcm_eq_product hstar]
  rw [Nat.Coprime.lcm_eq_mul (u_coprime_outgoingCrossProduct hstar h)]
  rw [Nat.totient_mul (u_coprime_outgoingCrossProduct hstar h)]
  rw [totient_outgoingCrossProduct hstar h]

theorem totient_rightCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    Nat.totient (rightCrossLowerTuple H u s h) =
      Nat.totient (u h) *
        ∏ x ∈ incomingCrossIndices H h, Nat.totient (s x.1 x.2) := by
  rw [rightCrossLowerTuple, incomingCrossLcm_eq_product hstar]
  rw [Nat.Coprime.lcm_eq_mul (u_coprime_incomingCrossProduct hstar h)]
  rw [Nat.totient_mul (u_coprime_incomingCrossProduct hstar h)]
  rw [totient_incomingCrossProduct hstar h]

theorem prod_outgoingCrossTotients_eq_crossTotientProduct
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :
    (∏ h : H, ∏ x ∈ outgoingCrossIndices H h,
      Nat.totient (s x.1 x.2)) = crossTotientProduct H s := by
  unfold outgoingCrossIndices crossTotientProduct
  exact Finset.prod_fiberwise (offDiagonalPairs H).attach
    (fun x => x.1.1) (fun x => Nat.totient (s x.1 x.2))

theorem prod_incomingCrossTotients_eq_crossTotientProduct
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :
    (∏ h : H, ∏ x ∈ incomingCrossIndices H h,
      Nat.totient (s x.1 x.2)) = crossTotientProduct H s := by
  unfold incomingCrossIndices crossTotientProduct
  exact Finset.prod_fiberwise (offDiagonalPairs H).attach
    (fun x => x.1.2) (fun x => Nat.totient (s x.1 x.2))

theorem prod_totient_leftCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) :
    (∏ h : H, Nat.totient (leftCrossLowerTuple H u s h)) =
      (∏ h : H, Nat.totient (u h)) * crossTotientProduct H s := by
  simp_rw [totient_leftCrossLowerTuple hstar]
  rw [Finset.prod_mul_distrib]
  rw [prod_outgoingCrossTotients_eq_crossTotientProduct]

theorem prod_totient_rightCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) :
    (∏ h : H, Nat.totient (rightCrossLowerTuple H u s h)) =
      (∏ h : H, Nat.totient (u h)) * crossTotientProduct H s := by
  simp_rw [totient_rightCrossLowerTuple hstar]
  rw [Finset.prod_mul_distrib]
  rw [prod_incomingCrossTotients_eq_crossTotientProduct]

end BoundedGaps.Maynard
