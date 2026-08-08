import Waring.Analytic.ChenTenCumulativeRounding
import Waring.Analytic.ChenTenRepresentation

/-!
# Cumulative fifteenth-power representation counts

This file expresses the cumulative positive representation count as a finite
tuple count and identifies it with `K15` in the range where the ambient tuple
bound does not truncate any contributing coordinate.
-/

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

/-- The number of positive fifteen-variable representations of targets below `X`. -/
def chenTenCumulativeRepresentationCount (P X : Nat) : Nat :=
  ∑ n ∈ Finset.range X, positiveFifthPowerRepresentationCount 15 P n

/-- The cumulative representation count is the cardinality of the corresponding tuple filter. -/
theorem chenTenCumulativeRepresentationCount_eq_filter_card
    (P X : Nat) :
    chenTenCumulativeRepresentationCount P X =
      ((Finset.univ : Finset (Fin 15 → Fin P)).filter
        (fun a => positiveFifthPowerTupleSum a < X)).card := by
  unfold chenTenCumulativeRepresentationCount
  simp_rw [positiveFifthPowerRepresentationCount]
  simpa only [Finset.mem_range] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin 15 → Fin P)) (Finset.range X)
        positiveFifthPowerTupleSum)

private theorem coordinate_pow_le_tuple_sum
    {P : Nat} (a : Fin 15 → Fin P) (i : Fin 15) :
    ((a i).val + 1) ^ 5 ≤ positiveFifthPowerTupleSum a := by
  unfold positiveFifthPowerTupleSum
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin 15)))
    (f := fun j : Fin 15 => ((a j).val + 1) ^ 5)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  simpa using hsingle

private theorem coordinate_lt_pred_of_tuple_sum_lt
    {P X : Nat} (hX : 2 ≤ X) (a : Fin 15 → Fin P)
    (ha : positiveFifthPowerTupleSum a < X) (i : Fin 15) :
    (a i).val < X - 1 := by
  have hterm := coordinate_pow_le_tuple_sum a i
  have hbase : (a i).val + 1 ≤ ((a i).val + 1) ^ 5 :=
    Nat.le_pow (by norm_num)
  omega

private theorem coordinate_lt_of_tuple_sum_lt_pow
    {P X : Nat} (hXPow : X ≤ (P + 1) ^ 5)
    (a : Fin 15 → Fin (X - 1))
    (ha : positiveFifthPowerTupleSum a < X) (i : Fin 15) :
    (a i).val < P := by
  have hterm := coordinate_pow_le_tuple_sum a i
  have hstrict : ((a i).val + 1) ^ 5 < (P + 1) ^ 5 :=
    lt_of_le_of_lt hterm (lt_of_lt_of_le ha hXPow)
  have hbase : (a i).val + 1 < P + 1 :=
    (Nat.pow_lt_pow_iff_left (by norm_num : (5 : Nat) ≠ 0)).mp hstrict
  omega

/-- Under the ambient power bound, the cumulative representation count equals `K15 (X - 1)`. -/
theorem chenTenCumulativeRepresentationCount_eq_K15_pred
    {P X : Nat} (hX : 2 ≤ X) (hXPow : X ≤ (P + 1) ^ 5) :
    chenTenCumulativeRepresentationCount P X = K15 (X - 1) := by
  classical
  rw [chenTenCumulativeRepresentationCount_eq_filter_card]
  rw [K15_eq_validTuples15_card]
  let sP := (Finset.univ : Finset (Fin 15 → Fin P)).filter
    (fun a => positiveFifthPowerTupleSum a < X)
  let sX := validTuples15 (X - 1)
  change sP.card = sX.card
  let forward : ∀ a ∈ sP, Fin 15 → Fin (X - 1) :=
    fun a ha i =>
      (⟨(a i).val,
        coordinate_lt_pred_of_tuple_sum_lt hX a
          ((Finset.mem_filter.mp ha).2) i⟩ : Fin (X - 1))
  let backward : ∀ a ∈ sX, Fin 15 → Fin P :=
    fun a ha i =>
      (⟨(a i).val,
        coordinate_lt_of_tuple_sum_lt_pow hXPow a (by
          have havalid : valid15 (X - 1) a := by
            exact (Finset.mem_filter.mp ha).2
          have hlt : ∑ j, ((a j).val + 1) ^ 5 < X := by
            unfold valid15 at havalid
            omega
          simpa [positiveFifthPowerTupleSum, Nat.succ_eq_add_one] using hlt) i⟩ : Fin P)
  refine Finset.card_bij' forward backward ?_ ?_ ?_ ?_
  · intro a ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold valid15
    change (∑ i, ((a i).val + 1) ^ 5) ≤ X - 1
    have ha' := (Finset.mem_filter.mp ha).2
    unfold positiveFifthPowerTupleSum at ha'
    simp only [Nat.succ_eq_add_one] at ha'
    omega
  · intro a ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have ha' : valid15 (X - 1) a := (Finset.mem_filter.mp ha).2
    unfold valid15 at ha'
    unfold positiveFifthPowerTupleSum
    change (∑ i, ((a i).val + 1) ^ 5) < X
    simpa only [Nat.succ_eq_add_one] using (show
      (∑ i, ((a i).val + 1) ^ 5) < X by omega)
  · intro a ha
    apply funext
    intro i
    apply Fin.ext
    rfl
  · intro a ha
    apply funext
    intro i
    apply Fin.ext
    rfl

end

end Waring.Analytic
