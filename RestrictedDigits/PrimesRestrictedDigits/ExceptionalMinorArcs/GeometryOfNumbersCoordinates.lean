import PrimesRestrictedDigits.BasicEstimates.IntegerVectors
import PrimesRestrictedDigits.BasicEstimates.Lattices
import Mathlib.Tactic.FieldSimp

/-!
# Rank-three integral coordinate boxes

This proves the exact factor `27` coordinate count used in the repaired proof
of `MAYNARD-PRD-PUBLISHED`, Lemma 13.2, pp. 193--195.
-/

noncomputable section

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- A rank-three integral coordinate box has cardinality times the product of
its positive coordinate weights at most `27*B^3`. -/
theorem card_mul_basisWeights_finThree_le
    {M : Type*} [AddCommGroup M] [Module Int M]
    (b : Module.Basis (Fin 3) Int M) (s : Finset M)
    (V : Fin 3 -> Real) (B : Real)
    (hV : ∀ i, 0 < V i) (hVB : ∀ i, V i <= B)
    (hs : ∀ x ∈ s, ∀ i,
      (((|b.repr x i| : Int) : Real)) * V i <= B) :
    (s.card : Real) * (V 0 * V 1 * V 2) <= 27 * B ^ 3 := by
  let R : Fin 3 -> Nat := fun i => Nat.floor (B / V i)
  have hRatio : ∀ i, 1 <= B / V i := by
    intro i
    exact (le_div_iff₀ (hV i)).2 (by simpa using hVB i)
  have hrepr : ∀ x ∈ s, ∀ i, |b.repr x i| <= (R i : Int) := by
    intro x hx i
    have hcast : (((|b.repr x i| : Int) : Real)) <= B / V i :=
      (le_div_iff₀ (hV i)).2 (hs x hx i)
    have hnatCast : (((b.repr x i).natAbs : Nat) : Real) <=
        B / V i := by
      simpa [Nat.cast_natAbs, Int.cast_abs] using hcast
    have hnat : (b.repr x i).natAbs <= R i :=
      Nat.le_floor hnatCast
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_le.2 hnat
  have hcardNat : s.card <= ∏ i, (2 * R i + 1) :=
    card_le_prod_two_mul_add_one_of_basis_repr_le b R s hrepr
  have hcard : (s.card : Real) <=
      ((2 * R 0 + 1 : Nat) : Real) *
        ((2 * R 1 + 1 : Nat) : Real) *
          ((2 * R 2 + 1 : Nat) : Real) := by
    exact_mod_cast (hcardNat.trans_eq (Fin.prod_univ_three _))
  have hfactor : ∀ i, ((2 * R i + 1 : Nat) : Real) <=
      3 * (B / V i) := by
    intro i
    simpa [R, card_integerCoordinateBox] using
      card_integerCoordinateBox_real_le (hRatio i)
  have hfactorNonneg : ∀ i, 0 <= 3 * (B / V i) := by
    intro i
    exact mul_nonneg (by norm_num) (zero_le_one.trans (hRatio i))
  have hproduct : (s.card : Real) <=
      (3 * (B / V 0)) * (3 * (B / V 1)) *
        (3 * (B / V 2)) := by
    calc
      (s.card : Real) <=
          ((2 * R 0 + 1 : Nat) : Real) *
            ((2 * R 1 + 1 : Nat) : Real) *
              ((2 * R 2 + 1 : Nat) : Real) := hcard
      _ <= (3 * (B / V 0)) * (3 * (B / V 1)) *
          (3 * (B / V 2)) := by
        exact mul_le_mul
          (mul_le_mul (hfactor 0) (hfactor 1)
            (Nat.cast_nonneg _) (hfactorNonneg 0))
          (hfactor 2) (Nat.cast_nonneg _)
          (mul_nonneg (hfactorNonneg 0) (hfactorNonneg 1))
  calc
    (s.card : Real) * (V 0 * V 1 * V 2) <=
        ((3 * (B / V 0)) * (3 * (B / V 1)) *
          (3 * (B / V 2))) * (V 0 * V 1 * V 2) := by
      exact mul_le_mul_of_nonneg_right hproduct
        (mul_nonneg (mul_nonneg (hV 0).le (hV 1).le) (hV 2).le)
    _ = 27 * B ^ 3 := by
      field_simp [(hV 0).ne', (hV 1).ne', (hV 2).ne']
      ring

end PrimesRestrictedDigits
