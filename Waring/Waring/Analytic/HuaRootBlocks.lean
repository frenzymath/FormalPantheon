import Waring.Analytic.HuaCancellation

/-!
# Root blocks after Hua's digit cancellation

This file reassembles the residues surviving Hua's `t+1`-digit cancellation
into one full block for each distinct root of the normalized derivative
[HUA1957-BOOK, p. 6].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The full residue system modulo `p^(t+1)*m`, ordered first by its low
base-`p` digit and then by the remaining `p^t*m` digits. -/
def huaRootBlocks (p t m : Nat) :
    Fin (p ^ t * m) × Fin p ≃ Fin (p ^ (t + 1) * m) :=
  (finPrimeBlocks p (p ^ t * m)).trans
    (finCongr (by rw [pow_succ]; ring))

@[simp] theorem huaRootBlocks_val (p t m : Nat)
    (x : Fin (p ^ t * m) × Fin p) :
    (huaRootBlocks p t m x).val = x.2.val + p * x.1.val := by
  rfl

/-- Reduction modulo `p` of a root-block index is its low digit. -/
theorem huaRootBlocks_mod (p t m : Nat) [NeZero p]
    (k : Fin (p ^ t * m)) (r : Fin p) :
    (((huaRootBlocks p t m (k, r)).val : Nat) : ZMod p) =
      ((r.val : Nat) : ZMod p) := by
  rw [huaRootBlocks_val]
  push_cast
  rw [ZMod.natCast_self]
  simp

/-- The representative in the full modulus lying above a chosen normalized
derivative root. -/
def huaRootBlockIndex (p t m : Nat) [NeZero p]
    (x : ZMod p) (k : Fin (p ^ t * m)) :
    Fin (p ^ (t + 1) * m) :=
  huaRootBlocks p t m (k, (ZMod.finEquiv p).symm x)

/-- The root-block representative reduces to its indexing root modulo `p`. -/
theorem huaRootBlockIndex_mod (p t m : Nat) [NeZero p]
    (x : ZMod p) (k : Fin (p ^ t * m)) :
    (((huaRootBlockIndex p t m x k).val : Nat) : ZMod p) = x := by
  rw [huaRootBlockIndex, huaRootBlocks_mod]
  rw [← zmod_finEquiv_apply]
  exact (ZMod.finEquiv p).apply_symm_apply x

/-- Exact root-block decomposition after Hua's digit cancellation. -/
theorem integerFormalPolynomialCompleteSum_eq_sum_huaRootBlocks
    {p t m : Nat} [Fact p.Prime] [NeZero p] [NeZero m]
    (hm : p ^ (t + 1) ∣ m) (F D : Polynomial Int)
    (hderivative :
      F.derivative = Polynomial.C ((p : Int) ^ t) * D)
    (hD : D.map (Int.castRingHom (ZMod p)) ≠ 0) :
    integerFormalPolynomialCompleteSum
        (q := p ^ (t + 1) * m) F =
      ∑ x ∈ (D.map (Int.castRingHom (ZMod p))).roots.toFinset,
        ∑ k : Fin (p ^ t * m),
          ZMod.stdAddChar
            ((F.map (Int.castRingHom
              (ZMod (p ^ (t + 1) * m)))).eval
                (((huaRootBlockIndex p t m x k).val : Nat) :
                  ZMod (p ^ (t + 1) * m))) := by
  rw [integerFormalPolynomialCompleteSum_eq_huaSurvivingResidues
    hm F D hderivative]
  rw [← (huaRootBlocks p t m).sum_comp, Fintype.sum_prod_type]
  let roots := (D.map (Int.castRingHom (ZMod p))).roots.toFinset
  calc
    (∑ k : Fin (p ^ t * m), ∑ r : Fin p,
        if (D.map (Int.castRingHom (ZMod p))).eval
            (((huaRootBlocks p t m (k, r)).val : Nat) : ZMod p) = 0
        then ZMod.stdAddChar
          ((F.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              (((huaRootBlocks p t m (k, r)).val : Nat) :
                ZMod (p ^ (t + 1) * m)))
        else 0) =
      ∑ k : Fin (p ^ t * m), ∑ x ∈ roots,
        ZMod.stdAddChar
          ((F.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              (((huaRootBlockIndex p t m x k).val : Nat) :
                ZMod (p ^ (t + 1) * m))) := by
      apply Finset.sum_congr rfl
      intro k _
      let block : ZMod p → Complex := fun x ↦
        ZMod.stdAddChar
          ((F.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              (((huaRootBlockIndex p t m x k).val : Nat) :
                ZMod (p ^ (t + 1) * m)))
      have hr (r : Fin p) :
          (ZMod.finEquiv p).symm ((r.val : Nat) : ZMod p) = r := by
        rw [← zmod_finEquiv_apply]
        exact (ZMod.finEquiv p).symm_apply_apply r
      have hmem (r : Fin p) :
          (D.map (Int.castRingHom (ZMod p))).eval
              ((r.val : Nat) : ZMod p) = 0 ↔
            ((r.val : Nat) : ZMod p) ∈ roots := by
        dsimp only [roots]
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hD]
        rfl
      simpa only [huaRootBlocks_mod, hmem, block,
        huaRootBlockIndex, hr] using
          sum_fin_ite_mem_zmod p roots block
    _ = ∑ x ∈ roots, ∑ k : Fin (p ^ t * m),
        ZMod.stdAddChar
          ((F.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              (((huaRootBlockIndex p t m x k).val : Nat) :
                ZMod (p ^ (t + 1) * m))) := by
      rw [Finset.sum_comm]

-- The nonzero modulus remains in this reviewed root-block contract so it has
-- the same admissible-modulus interface as the definitions used with it.
attribute [nolint unusedArguments] huaRootBlocks_mod

end Waring.Analytic
