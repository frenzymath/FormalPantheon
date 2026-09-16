import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientCases
import Mathlib.NumberTheory.Divisors

/-!
# Generic fibers for zero-coefficient plane witnesses

This packages the signed divisor-fiber argument shared by the `v3 = 0` and
`v4 = 0` branches of `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 210--211.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- A finite carrier whose keyed fibers inject into nonzero signed factor
pairs is bounded by the number of keys times a uniform factor-pair bound. -/
theorem lineZeroCoefficient_card_nonzero_target_real_le
    {W K : Type*} [DecidableEq W] [DecidableEq K]
    (S : Finset W) (outer : Finset K) (key : W -> K)
    (target : K -> Int) (embedding : W -> Prod Int Int) (B Q : Real)
    (hmaps : Set.MapsTo key (S : Set W) (outer : Set K))
    (htarget : forall w, w ∈ S -> target (key w) ≠ 0)
    (hproduct : forall w, w ∈ S ->
      (embedding w).1 * (embedding w).2 = target (key w))
    (hinjective : forall k, Set.InjOn embedding
      (S.filter fun w => key w = k : Set W))
    (hbound : forall w, w ∈ S -> (target (key w)).natAbs <= B)
    (hQ : 0 <= Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) <= B ->
      (z.divisorsAntidiag.card : Real) <= Q) :
    (S.card : Real) <= (outer.card : Real) * Q := by
  have hfiber : forall k, k ∈ outer ->
      ((S.filter fun w => key w = k).card : Real) <= Q := by
    intro k _hk
    have hcard : (S.filter fun w => key w = k).card <=
        (target k).divisorsAntidiag.card := by
      apply Finset.card_le_card_of_injOn embedding
      · intro w hw
        have hwData := Finset.mem_filter.mp hw
        change ((embedding w).1, (embedding w).2) ∈
          (target k).divisorsAntidiag
        rw [Int.prodMk_mem_divisorsAntidiag]
        · simpa only [hwData.2] using hproduct w hwData.1
        · simpa only [hwData.2] using htarget w hwData.1
      · exact hinjective k
    by_cases hnonempty : (S.filter fun w => key w = k).Nonempty
    · let w := hnonempty.choose
      have hw := Finset.mem_filter.mp hnonempty.choose_spec
      have htargetBound : ((target k).natAbs : Real) <= B := by
        have hb := hbound w hw.1
        rw [hw.2] at hb
        exact hb
      calc
        ((S.filter fun w => key w = k).card : Real) <=
            ((target k).divisorsAntidiag.card : Real) := by
          exact_mod_cast hcard
        _ <= Q := hfactor (target k) htargetBound
    · have hempty : S.filter (fun w => key w = k) = Finset.empty :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      rw [hempty]
      simpa using hQ
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (S.card : Real) =
        ∑ k ∈ outer, ((S.filter fun w => key w = k).card : Real) := by
      simpa only [Nat.cast_sum] using
        congrArg (fun n : Nat => (n : Real)) hdecomp
    _ <= ∑ _k ∈ outer, Q :=
      Finset.sum_le_sum fun k hk => hfiber k hk
    _ = (outer.card : Real) * Q := by simp

/-- The common outer key box for either last-coordinate case has at most
`#C * #B(V)^2` elements. -/
theorem lineZeroCoefficient_last_case_outer_card_real_le
    {X : Nat} (C : Finset (Fin X)) (V : Real) :
    ((((C.filter fun a => 0 < a.val).product
        ((lineCoefficientBox V).product (lineCoefficientBox V))).card : Nat) :
        Real) <=
      (C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2 := by
  rw [Finset.product_eq_sprod, Finset.card_product,
    Finset.product_eq_sprod, Finset.card_product]
  push_cast
  have hpos : ((C.filter fun a => 0 < a.val).card : Real) <= C.card := by
    exact_mod_cast Finset.card_filter_le C fun a => 0 < a.val
  nlinarith [sq_nonneg ((lineCoefficientBox V).card : Real)]

end PrimesRestrictedDigits
