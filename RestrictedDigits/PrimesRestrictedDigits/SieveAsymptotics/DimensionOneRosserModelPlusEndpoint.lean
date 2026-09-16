import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelRegularity

/-!
# Closed endpoint for the raw upper dimension-one Rosser model

The published raw limit is source-facing only for `s > 1`. The implemented term definition
nevertheless gives a canonical value at `s = 1`: every positive-rank term agrees there with
its value at three, while rank zero is a single finite correction. This file proves that
internal closure without changing the source statement. See `IWANIEC-ROSSER-SIEVE-1980`,
Section 7, printed pp. 194--196.
-/

open Filter Set

namespace PrimesRestrictedDigits

private theorem plusTerm_succ_eq_at_three
    (r : Nat) {s : Real} (hs1 : 1 <= s) (hs3 : s <= 3) :
    dimensionOneRosserModelPlusTerm (r + 1) s =
      dimensionOneRosserModelPlusTerm (r + 1) 3 := by
  rw [dimensionOneRosserModelPlusTerm_succ_eq,
    dimensionOneRosserModelPlusTerm_succ_eq]
  rw [if_pos hs1, if_pos (by norm_num : (1 : Real) <= 3),
    max_eq_left hs3, max_self]

private theorem plusTerm_succ_one_eq_three (r : Nat) :
    dimensionOneRosserModelPlusTerm (r + 1) 1 =
      dimensionOneRosserModelPlusTerm (r + 1) 3 :=
  plusTerm_succ_eq_at_three r (by norm_num) (by norm_num)

private theorem plusTerm_succ_one_eq_two (r : Nat) :
    dimensionOneRosserModelPlusTerm (r + 1) 1 =
      dimensionOneRosserModelPlusTerm (r + 1) 2 := by
  rw [dimensionOneRosserModelPlusTerm_succ_eq,
    dimensionOneRosserModelPlusTerm_succ_eq]
  norm_num

private theorem sum_range_succ_plusTerm (R : Nat) (s : Real) :
    (∑ r ∈ Finset.range (R + 1),
      dimensionOneRosserModelPlusTerm r s) =
        dimensionOneRosserModelPlusPartialSum R s :=
  rfl

private theorem plusPartialSum_boundary_of_one_le
    (R : Nat) {s : Real} (hs1 : 1 <= s) (hs3 : s <= 3) :
    dimensionOneRosserModelPlusPartialSum R s + s =
      3 + dimensionOneRosserModelPlusPartialSum R 3 := by
  induction R with
  | zero =>
      rw [dimensionOneRosserModelPlusPartialSum_zero,
        dimensionOneRosserModelPlusPartialSum_zero,
        dimensionOneRosserModelPlusTerm_zero,
        dimensionOneRosserModelPlusTerm_zero]
      rw [if_pos ⟨hs1, hs3⟩]
      norm_num
  | succ R ih =>
      calc
        dimensionOneRosserModelPlusPartialSum (R + 1) s + s =
            (dimensionOneRosserModelPlusPartialSum R s + s) +
              dimensionOneRosserModelPlusTerm (R + 1) s := by
          rw [dimensionOneRosserModelPlusPartialSum_succ]
          ring
        _ = (3 + dimensionOneRosserModelPlusPartialSum R 3) +
              dimensionOneRosserModelPlusTerm (R + 1) s := by rw [ih]
        _ = 3 + (dimensionOneRosserModelPlusPartialSum R 3 +
              dimensionOneRosserModelPlusTerm (R + 1) 3) := by
          rw [plusTerm_succ_eq_at_three R hs1 hs3]
          ring
        _ = 3 + dimensionOneRosserModelPlusPartialSum (R + 1) 3 := by
          rw [dimensionOneRosserModelPlusPartialSum_succ]

private theorem endpoint_summable :
    Summable (fun r => dimensionOneRosserModelPlusTerm r 1) := by
  apply (summable_nat_add_iff (f := fun r =>
    dimensionOneRosserModelPlusTerm r 1) 1).mp
  have htail : Summable (fun r =>
      dimensionOneRosserModelPlusTerm (r + 1) 3) :=
    (summable_nat_add_iff (f := fun r =>
      dimensionOneRosserModelPlusTerm r 3) 1).mpr
      (summable_dimensionOneRosserModelPlusTerm (s := 3) (by norm_num))
  exact htail.congr (fun r => (plusTerm_succ_one_eq_three r).symm)

private theorem endpoint_affine :
    dimensionOneRosserModelPlusRaw 1 + 1 =
      dimensionOneRosserModelPlusAffineConstant := by
  have hsum1 := endpoint_summable
  have hsum2 := summable_dimensionOneRosserModelPlusTerm
    (s := 2) (by norm_num)
  rw [dimensionOneRosserModelPlusRaw, hsum1.tsum_eq_zero_add,
    dimensionOneRosserModelPlusAffineConstant,
    dimensionOneRosserModelPlusRaw, hsum2.tsum_eq_zero_add]
  simp only [dimensionOneRosserModelPlusTerm_zero]
  norm_num
  have htail :
      (∑' r, dimensionOneRosserModelPlusTerm (r + 1) 1) =
        ∑' r, dimensionOneRosserModelPlusTerm (r + 1) 2 :=
    tsum_congr plusTerm_succ_one_eq_two
  rw [htail]
  ring

theorem summable_dimensionOneRosserModelPlusTerm_of_one_le
    {s : Real} (hs : 1 <= s) :
    Summable (fun r => dimensionOneRosserModelPlusTerm r s) := by
  rcases hs.eq_or_lt with h | h
  · rw [<- h]
    exact endpoint_summable
  · exact summable_dimensionOneRosserModelPlusTerm h

theorem dimensionOneRosserModelPlusPartialSum_tendsto_raw_of_one_le
    {s : Real} (hs : 1 <= s) :
    Tendsto (fun R => dimensionOneRosserModelPlusPartialSum R s)
      atTop (nhds (dimensionOneRosserModelPlusRaw s)) := by
  have h := (summable_dimensionOneRosserModelPlusTerm_of_one_le hs).hasSum
    |>.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert h using 1
  · funext R
    exact (sum_range_succ_plusTerm R s).symm
  · rfl

theorem dimensionOneRosserModelPlusRaw_add_eq_affineConstant_of_one_le
    {s : Real} (hs1 : 1 <= s) (hs3 : s <= 3) :
    dimensionOneRosserModelPlusRaw s + s =
      dimensionOneRosserModelPlusAffineConstant := by
  rcases hs1.eq_or_lt with h | h
  · rw [<- h]
    exact endpoint_affine
  · exact dimensionOneRosserModelPlusRaw_add_eq_affineConstant h hs3

theorem dimensionOneRosserModelPlusRaw_antitoneOn_Ici_one :
    AntitoneOn dimensionOneRosserModelPlusRaw (Ici 1) := by
  intro x hx y hy hxy
  unfold dimensionOneRosserModelPlusRaw
  exact (summable_dimensionOneRosserModelPlusTerm_of_one_le hy).tsum_le_tsum
    (fun r => (dimensionOneRosserModelTerm_antitoneOn r).1 hx hy hxy)
      (summable_dimensionOneRosserModelPlusTerm_of_one_le hx)

theorem continuousOn_dimensionOneRosserModelPlusRaw_Ici_one :
    ContinuousOn dimensionOneRosserModelPlusRaw (Ici 1) := by
  have hleft : ContinuousOn dimensionOneRosserModelPlusRaw (Icc 1 2) := by
    have hbase : ContinuousOn
        (fun s : Real => dimensionOneRosserModelPlusAffineConstant - s)
        (Icc 1 2) :=
      (continuous_const.sub continuous_id).continuousOn
    apply hbase.congr
    intro s hs
    have hplus :=
      dimensionOneRosserModelPlusRaw_add_eq_affineConstant_of_one_le hs.1
        (hs.2.trans (by norm_num))
    linarith
  have hright : ContinuousOn dimensionOneRosserModelPlusRaw (Ici 2) :=
    continuousOn_dimensionOneRosserModelPlusRaw.mono (by
      intro s hs
      exact mem_Ioi.mpr (by linarith [mem_Ici.mp hs]))
  rw [<- Icc_union_Ici_eq_Ici (show (1 : Real) <= 2 by norm_num)]
  exact hleft.union_of_isClosed hright isClosed_Icc isClosed_Ici

end PrimesRestrictedDigits
