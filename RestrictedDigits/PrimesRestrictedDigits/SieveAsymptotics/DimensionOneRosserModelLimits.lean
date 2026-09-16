import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelComparison
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelTermPositivity
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Raw infinite-rank dimension-one Rosser model limits

This constructs the pointwise series in Iwaniec's Lemma 18 and proves their positivity,
uniform delay comparison, decay, antitonicity, and upper affine branch. See
`IWANIEC-ROSSER-SIEVE-1980`, printed pp. 194--195.
-/

open scoped BigOperators Topology
open Filter Set

namespace PrimesRestrictedDigits

/-- The raw infinite-rank upper Section 7 model series. Its proved summability
domain is `s > 1`; no value claim is made at `s = 1`. -/
noncomputable def dimensionOneRosserModelPlusRaw (s : Real) : Real :=
  ∑' r, dimensionOneRosserModelPlusTerm r s

/-- The raw infinite-rank lower Section 7 model series. This is zero-totalized
below two and is not the paper's later affine continuation. -/
noncomputable def dimensionOneRosserModelMinusRaw (s : Real) : Real :=
  ∑' r, dimensionOneRosserModelMinusTerm r s

private theorem sum_range_succ_dimensionOneRosserModelPlusTerm
    (R : Nat) (s : Real) :
    (∑ r ∈ Finset.range (R + 1),
      dimensionOneRosserModelPlusTerm r s) =
        dimensionOneRosserModelPlusPartialSum R s :=
  rfl

private theorem sum_range_succ_dimensionOneRosserModelMinusTerm
    (R : Nat) (s : Real) :
    (∑ r ∈ Finset.range (R + 1),
      dimensionOneRosserModelMinusTerm r s) =
        dimensionOneRosserModelMinusPartialSum R s := by
  rw [Nat.range_succ_eq_Icc_zero]
  rw [<- Finset.sum_erase_add (a := 0) (Finset.Icc 0 R)
    (fun r => dimensionOneRosserModelMinusTerm r s) (by simp)]
  simp only [dimensionOneRosserModelMinusTerm_zero, add_zero,
    Finset.Icc_erase_left]
  rw [<- Finset.Icc_succ_left_eq_Ioc 0 R]
  rfl

/-- Pointwise summability of the upper model terms on the source domain. -/
theorem summable_dimensionOneRosserModelPlusTerm
    {s : Real} (hs : 1 < s) :
    Summable (fun r => dimensionOneRosserModelPlusTerm r s) := by
  rcases exists_dimensionOneRosserModelPartialSums_lt_delay with
    ⟨c, hc, hplus, hminus⟩
  apply summable_of_sum_range_le
    (fun r => dimensionOneRosserModelPlusTerm_nonneg r s)
  intro n
  cases n with
  | zero =>
      exact le_trans (by simp)
        ((dimensionOneRosserModelPlusPartialSum_nonneg 0 s).trans
          (hplus 0 hs).le)
  | succ R =>
      rw [sum_range_succ_dimensionOneRosserModelPlusTerm]
      exact (hplus R hs).le

/-- Pointwise summability of the lower model terms, including the source-used
endpoint two. -/
theorem summable_dimensionOneRosserModelMinusTerm
    {s : Real} (hs : 2 <= s) :
    Summable (fun r => dimensionOneRosserModelMinusTerm r s) := by
  rcases exists_dimensionOneRosserModelPartialSums_lt_delay with
    ⟨c, hc, hplus, hminus⟩
  apply summable_of_sum_range_le
    (fun r => dimensionOneRosserModelMinusTerm_nonneg r s)
  intro n
  cases n with
  | zero =>
      exact le_trans (by simp)
        ((dimensionOneRosserModelMinusPartialSum_nonneg 0 s).trans
          (hminus 0 hs).le)
  | succ R =>
      rw [sum_range_succ_dimensionOneRosserModelMinusTerm]
      exact (hminus R hs).le

/-- The finite upper model sums tend pointwise to the raw upper series. -/
theorem dimensionOneRosserModelPlusPartialSum_tendsto_raw
    {s : Real} (hs : 1 < s) :
    Tendsto (fun R => dimensionOneRosserModelPlusPartialSum R s)
      atTop (nhds (dimensionOneRosserModelPlusRaw s)) := by
  have h := (summable_dimensionOneRosserModelPlusTerm hs).hasSum
    |>.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert h using 1
  · funext R
    exact (sum_range_succ_dimensionOneRosserModelPlusTerm R s).symm
  · rfl

/-- The finite lower model sums tend pointwise to the raw lower series. -/
theorem dimensionOneRosserModelMinusPartialSum_tendsto_raw
    {s : Real} (hs : 2 <= s) :
    Tendsto (fun R => dimensionOneRosserModelMinusPartialSum R s)
      atTop (nhds (dimensionOneRosserModelMinusRaw s)) := by
  have h := (summable_dimensionOneRosserModelMinusTerm hs).hasSum
    |>.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert h using 1
  · funext R
    exact (sum_range_succ_dimensionOneRosserModelMinusTerm R s).symm
  · rfl

theorem dimensionOneRosserModelPlusRaw_nonneg (s : Real) :
    0 <= dimensionOneRosserModelPlusRaw s :=
  tsum_nonneg (fun r => dimensionOneRosserModelPlusTerm_nonneg r s)

theorem dimensionOneRosserModelMinusRaw_nonneg (s : Real) :
    0 <= dimensionOneRosserModelMinusRaw s :=
  tsum_nonneg (fun r => dimensionOneRosserModelMinusTerm_nonneg r s)

theorem dimensionOneRosserModelPlusRaw_eq_zero_of_lt
    {s : Real} (hs : s < 1) :
    dimensionOneRosserModelPlusRaw s = 0 := by
  simp [dimensionOneRosserModelPlusRaw,
    dimensionOneRosserModelPlusTerm_eq_zero_of_lt _ hs]

theorem dimensionOneRosserModelMinusRaw_eq_zero_of_lt
    {s : Real} (hs : s < 2) :
    dimensionOneRosserModelMinusRaw s = 0 := by
  simp [dimensionOneRosserModelMinusRaw,
    dimensionOneRosserModelMinusTerm_eq_zero_of_lt _ hs]

/-- Strict positivity in the upper source domain is witnessed by a sufficiently
large finite-rank term. -/
theorem dimensionOneRosserModelPlusRaw_pos
    {s : Real} (hs : 1 < s) :
    0 < dimensionOneRosserModelPlusRaw s := by
  obtain ⟨r, hr⟩ := exists_nat_gt ((s - 3) / 2)
  apply (summable_dimensionOneRosserModelPlusTerm hs).tsum_pos
    (fun n => dimensionOneRosserModelPlusTerm_nonneg n s) r
  apply dimensionOneRosserModelPlusTerm_pos r hs
  nlinarith

/-- Strict positivity of the raw lower series includes the endpoint two. -/
theorem dimensionOneRosserModelMinusRaw_pos
    {s : Real} (hs : 2 <= s) :
    0 < dimensionOneRosserModelMinusRaw s := by
  obtain ⟨r, hr⟩ := exists_nat_gt ((s - 2) / 2)
  apply (summable_dimensionOneRosserModelMinusTerm hs).tsum_pos
    (fun n => dimensionOneRosserModelMinusTerm_nonneg n s) r
  apply dimensionOneRosserModelMinusTerm_pos r hs
  nlinarith

/-- Iwaniec's Lemma 18 comparison at dimension one, with one weak limit
constant uniform in sign and argument. -/
theorem exists_dimensionOneRosserModelRaw_le_delay :
    exists c : Real, 0 < c /\
      (forall {s : Real}, 1 < s ->
        dimensionOneRosserModelPlusRaw s <=
          c * dimensionOneDelayScaledPlus s) /\
      (forall {s : Real}, 2 <= s ->
        dimensionOneRosserModelMinusRaw s <=
          c * dimensionOneDelayScaledMinus s) := by
  rcases exists_dimensionOneRosserModelPartialSums_lt_delay with
    ⟨c, hc, hplus, hminus⟩
  refine ⟨c, hc, ?_, ?_⟩
  · intro s hs
    rw [dimensionOneRosserModelPlusRaw]
    apply Real.tsum_le_of_sum_range_le
      (fun r => dimensionOneRosserModelPlusTerm_nonneg r s)
    intro n
    cases n with
    | zero =>
        exact le_trans (by simp)
          ((dimensionOneRosserModelPlusPartialSum_nonneg 0 s).trans
            (hplus 0 hs).le)
    | succ R =>
        rw [sum_range_succ_dimensionOneRosserModelPlusTerm]
        exact (hplus R hs).le
  · intro s hs
    rw [dimensionOneRosserModelMinusRaw]
    apply Real.tsum_le_of_sum_range_le
      (fun r => dimensionOneRosserModelMinusTerm_nonneg r s)
    intro n
    cases n with
    | zero =>
        exact le_trans (by simp)
          ((dimensionOneRosserModelMinusPartialSum_nonneg 0 s).trans
            (hminus 0 hs).le)
    | succ R =>
        rw [sum_range_succ_dimensionOneRosserModelMinusTerm]
        exact (hminus R hs).le

/-- The raw limits inherit the finite model's antitonicity on exactly their
proved convergence domains. -/
theorem dimensionOneRosserModelRaw_antitoneOn :
    AntitoneOn dimensionOneRosserModelPlusRaw (Ioi 1) /\
      AntitoneOn dimensionOneRosserModelMinusRaw (Ici 2) := by
  constructor
  · intro x hx y hy hxy
    apply le_of_tendsto_of_tendsto
      (dimensionOneRosserModelPlusPartialSum_tendsto_raw
        (mem_Ioi.mp hy))
      (dimensionOneRosserModelPlusPartialSum_tendsto_raw
        (mem_Ioi.mp hx))
    exact Filter.Eventually.of_forall (fun R =>
      (dimensionOneRosserModelPartialSum_antitoneOn R).1
        (mem_Ici.mpr (mem_Ioi.mp hx).le)
        (mem_Ici.mpr (mem_Ioi.mp hy).le) hxy)
  · intro x hx y hy hxy
    apply le_of_tendsto_of_tendsto
      (dimensionOneRosserModelMinusPartialSum_tendsto_raw
        (mem_Ici.mp hy))
      (dimensionOneRosserModelMinusPartialSum_tendsto_raw
        (mem_Ici.mp hx))
    exact Filter.Eventually.of_forall (fun R =>
      (dimensionOneRosserModelPartialSum_antitoneOn R).2 hx hy hxy)

/-- The raw upper limit inherits the finite affine branch on `1 < s <= 3`. -/
theorem dimensionOneRosserModelPlusRaw_add_eq_at_three
    {s : Real} (hs1 : 1 < s) (hs3 : s <= 3) :
    dimensionOneRosserModelPlusRaw s + s =
      3 + dimensionOneRosserModelPlusRaw 3 := by
  have hleft :=
    (dimensionOneRosserModelPlusPartialSum_tendsto_raw hs1).add_const s
  have hright :=
    (dimensionOneRosserModelPlusPartialSum_tendsto_raw
      (s := (3 : Real)) (by norm_num)).const_add 3
  apply tendsto_nhds_unique hleft
  have heq :
      (fun R => dimensionOneRosserModelPlusPartialSum R s + s) =
        fun R => 3 + dimensionOneRosserModelPlusPartialSum R 3 := by
    funext R
    exact dimensionOneRosserModelPlusPartialSum_boundary R hs1 hs3
  rw [heq]
  exact hright

/-- The raw upper model tends to zero at positive infinity. -/
theorem dimensionOneRosserModelPlusRaw_tendsto_zero :
    Tendsto dimensionOneRosserModelPlusRaw atTop (nhds 0) := by
  rcases exists_dimensionOneRosserModelRaw_le_delay with
    ⟨c, hc, hplus, hminus⟩
  refine squeeze_zero'
    (f := dimensionOneRosserModelPlusRaw)
    (g := fun s => c * dimensionOneDelayScaledPlus s) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall dimensionOneRosserModelPlusRaw_nonneg
  · filter_upwards [eventually_gt_atTop (1 : Real)] with s hs
    exact hplus hs
  · simpa using dimensionOneDelayScaledPlus_tendsto_zero.const_mul c

/-- The raw lower model tends to zero at positive infinity. -/
theorem dimensionOneRosserModelMinusRaw_tendsto_zero :
    Tendsto dimensionOneRosserModelMinusRaw atTop (nhds 0) := by
  rcases exists_dimensionOneRosserModelRaw_le_delay with
    ⟨c, hc, hplus, hminus⟩
  refine squeeze_zero'
    (f := dimensionOneRosserModelMinusRaw)
    (g := fun s => c * dimensionOneDelayScaledMinus s) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall dimensionOneRosserModelMinusRaw_nonneg
  · filter_upwards [eventually_ge_atTop (2 : Real)] with s hs
    exact hminus hs
  · simpa using dimensionOneDelayScaledMinus_tendsto_zero.const_mul c

end PrimesRestrictedDigits
