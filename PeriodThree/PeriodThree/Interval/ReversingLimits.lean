module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import PeriodThree.Interval.Reversing

/-!
# Limits of reversing nested intervals

The shrinking endpoints in the reversing construction converge to a pair of
points exchanged by the map.
-/

@[expose] public section

open Set Filter

namespace PeriodThree

private theorem ReversingNest.interval_subset_zero
    {F : ℝ → ℝ} {b c : ℝ} (N : ReversingNest F b c) (n : ℕ) :
    Icc (N.lower n) (N.upper n) ⊆ Icc b c := by
  induction n with
  | zero => simp [N.lower_zero, N.upper_zero]
  | succ n ih =>
    simpa [Nat.succ_eq_add_one] using (N.nested n).trans ih

private theorem ReversingNest.lower_mem_base
    {F : ℝ → ℝ} {b c : ℝ} (N : ReversingNest F b c) (n : ℕ) :
    N.lower n ∈ Icc b c :=
  N.interval_subset_zero n ⟨le_rfl, (N.lower_lt_upper n).le⟩

private theorem ReversingNest.upper_mem_base
    {F : ℝ → ℝ} {b c : ℝ} (N : ReversingNest F b c) (n : ℕ) :
    N.upper n ∈ Icc b c :=
  N.interval_subset_zero n ⟨(N.lower_lt_upper n).le, le_rfl⟩

private theorem ReversingNest.lower_monotone
    {F : ℝ → ℝ} {b c : ℝ} (N : ReversingNest F b c) : Monotone N.lower :=
  monotone_nat_of_le_succ fun n => (N.nested n ⟨le_rfl, (N.lower_lt_upper _).le⟩).1

private theorem ReversingNest.upper_antitone
    {F : ℝ → ℝ} {b c : ℝ} (N : ReversingNest F b c) : Antitone N.upper :=
  antitone_nat_of_succ_le fun n => (N.nested n ⟨(N.lower_lt_upper _).le, le_rfl⟩).2

private theorem ReversingNest.interval_subset_of_le
    {F : ℝ → ℝ} {b c : ℝ} (N : ReversingNest F b c) {i j : ℕ} (hji : j ≤ i) :
    Icc (N.lower i) (N.upper i) ⊆ Icc (N.lower j) (N.upper j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
  induction k with
  | zero => simp
  | succ k ih =>
    change Icc (N.lower (j + k + 1)) (N.upper (j + k + 1)) ⊆
      Icc (N.lower j) (N.upper j)
    exact (N.nested (j + k)).trans (ih (Nat.le_add_right j k))

private theorem ReversingNest.lower_le_upper
    {F : ℝ → ℝ} {b c : ℝ} (N : ReversingNest F b c) (i j : ℕ) :
    N.lower i ≤ N.upper j := by
  rcases le_total i j with hij | hji
  · exact (N.lower_monotone hij).trans (N.lower_lt_upper j).le
  · exact (N.interval_subset_of_le hji ⟨le_rfl, (N.lower_lt_upper i).le⟩).2

/-- Limit data for a reversing nest.  The endpoint convergence and exchanged
limit equations are the compactness step used after [LY75, Lemma 0, p. 987]. -/
structure ReversingNestLimits (F : ℝ → ℝ) (b c : ℝ)
    (N : ReversingNest F b c) where
  /-- Limit of the lower endpoint sequence. -/
  lowerLimit : ℝ
  /-- Limit of the upper endpoint sequence. -/
  upperLimit : ℝ
  /-- Every lower endpoint lies in the base interval. -/
  lower_mem : ∀ n, N.lower n ∈ Icc b c
  /-- Every upper endpoint lies in the base interval. -/
  upper_mem : ∀ n, N.upper n ∈ Icc b c
  /-- Lower endpoints lie below their limit. -/
  lower_le_limit : ∀ n, N.lower n ≤ lowerLimit
  /-- The two limits have the expected order. -/
  limits_ordered : lowerLimit ≤ upperLimit
  /-- The upper limit lies below every upper endpoint. -/
  limit_le_upper : ∀ n, upperLimit ≤ N.upper n
  /-- Lower endpoints converge to the lower limit. -/
  lower_tendsto : Tendsto N.lower atTop (nhds lowerLimit)
  /-- Upper endpoints converge to the upper limit. -/
  upper_tendsto : Tendsto N.upper atTop (nhds upperLimit)
  /-- The lower limit maps to the upper limit. -/
  map_lowerLimit : F lowerLimit = upperLimit
  /-- The upper limit maps to the lower limit. -/
  map_upperLimit : F upperLimit = lowerLimit

/-- Every reversing nest has exchanged endpoint limits, by monotone convergence
on its compact base interval as in [LY75, Lemma 0, p. 987]. -/
theorem ReversingNest.existsLimits
    {F : ℝ → ℝ} {b c : ℝ} (N : ReversingNest F b c)
    (hF : ContinuousOn F (Icc b c)) :
    Nonempty (ReversingNestLimits F b c N) := by
  let l : ℝ := ⨆ n, N.lower n
  let u : ℝ := ⨅ n, N.upper n
  have hLowerBdd : BddAbove (range N.lower) :=
    ⟨c, by rintro _ ⟨n, rfl⟩; exact (N.lower_mem_base n).2⟩
  have hUpperBdd : BddBelow (range N.upper) :=
    ⟨b, by rintro _ ⟨n, rfl⟩; exact (N.upper_mem_base n).1⟩
  have hLowerTend : Tendsto N.lower atTop (nhds l) := by
    simpa [l] using tendsto_atTop_ciSup N.lower_monotone hLowerBdd
  have hUpperTend : Tendsto N.upper atTop (nhds u) := by
    simpa [u] using tendsto_atTop_ciInf N.upper_antitone hUpperBdd
  have hlower_le (n : ℕ) : N.lower n ≤ l := by simpa [l] using le_ciSup hLowerBdd n
  have hu_le_upper (n : ℕ) : u ≤ N.upper n := by simpa [u] using ciInf_le hUpperBdd n
  have hlimits : l ≤ u := by
    dsimp [l, u]
    apply le_ciInf
    intro n
    apply ciSup_le
    intro m
    exact N.lower_le_upper m n
  have hl_mem : l ∈ Icc b c := by
    constructor
    · exact (N.lower_mem_base 0).1.trans (hlower_le 0)
    · exact hlimits.trans ((hu_le_upper 0).trans (N.upper_mem_base 0).2)
  have hu_mem : u ∈ Icc b c := by
    constructor
    · exact ((N.lower_mem_base 0).1.trans (hlower_le 0)).trans hlimits
    · exact (hu_le_upper 0).trans (N.upper_mem_base 0).2
  have hLowerShift : Tendsto (fun n => N.lower (n + 1)) atTop (nhds l) := by
    convert hLowerTend.comp (tendsto_add_atTop_nat 1) using 1
    all_goals simp [Function.comp_def]
  have hUpperShift : Tendsto (fun n => N.upper (n + 1)) atTop (nhds u) := by
    convert hUpperTend.comp (tendsto_add_atTop_nat 1) using 1
    all_goals simp [Function.comp_def]
  have hmap_lower : F l = u := by
    have hleft : Tendsto (fun n => F (N.lower (n + 1))) atTop (nhds (F l)) := by
      have hwithin : Tendsto (fun n => N.lower (n + 1)) atTop (nhdsWithin l (Icc b c)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hLowerShift, Eventually.of_forall fun n => N.lower_mem_base _⟩
      simpa [Function.comp_def] using (hF.continuousWithinAt hl_mem).tendsto.comp hwithin
    have hright : Tendsto (fun n => F (N.lower (n + 1))) atTop (nhds u) := by
      simpa [N.map_lower] using hUpperTend
    exact tendsto_nhds_unique hleft hright
  have hmap_upper : F u = l := by
    have hleft : Tendsto (fun n => F (N.upper (n + 1))) atTop (nhds (F u)) := by
      have hwithin : Tendsto (fun n => N.upper (n + 1)) atTop (nhdsWithin u (Icc b c)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hUpperShift, Eventually.of_forall fun n => N.upper_mem_base _⟩
      simpa [Function.comp_def] using (hF.continuousWithinAt hu_mem).tendsto.comp hwithin
    have hright : Tendsto (fun n => F (N.upper (n + 1))) atTop (nhds l) := by
      simpa [N.map_upper] using hLowerTend
    exact tendsto_nhds_unique hleft hright
  exact ⟨{
    lowerLimit := l
    upperLimit := u
    lower_mem := N.lower_mem_base
    upper_mem := N.upper_mem_base
    lower_le_limit := hlower_le
    limits_ordered := hlimits
    limit_le_upper := hu_le_upper
    lower_tendsto := hLowerTend
    upper_tendsto := hUpperTend
    map_lowerLimit := hmap_lower
    map_upperLimit := hmap_upper
  }⟩

namespace ReversingNestLimits

variable {F : ℝ → ℝ} {b c : ℝ} {N : ReversingNest F b c}

/-- The lower limit bridge remains in the original compact interval
[LY75, Appendix 2, p. 991]. -/
theorem lowerBridge_subset_base
    (E : ReversingNestLimits F b c N) (m : ℕ) :
    Icc (N.lower (m + 1)) E.lowerLimit ⊆ Icc b c := by
  apply Icc_subset_Icc
  · exact (E.lower_mem _).1
  · exact E.limits_ordered.trans ((E.limit_le_upper 0).trans (E.upper_mem 0).2)

/-- The upper limit bridge remains in the original compact interval
[LY75, Appendix 2, p. 991]. -/
theorem upperBridge_subset_base
    (E : ReversingNestLimits F b c N) (m : ℕ) :
    Icc E.upperLimit (N.upper (m + 1)) ⊆ Icc b c := by
  apply Icc_subset_Icc
  · exact ((E.lower_mem 0).1.trans (E.lower_le_limit 0)).trans E.limits_ordered
  · exact (E.upper_mem _).2

/-- The lower bridge covers the corresponding upper bridge by the intermediate
value theorem, as in the bridge argument following [LY75, Lemma 0, p. 987]. -/
theorem lowerToUpperCover (E : ReversingNestLimits F b c N)
    (hF : ContinuousOn F (Icc b c)) (m : ℕ) :
    Icc E.upperLimit (N.upper m) ⊆
      F '' Icc (N.lower (m + 1)) E.lowerLimit := by
  simpa [N.map_lower, E.map_lowerLimit] using
    intermediate_value_Icc' (E.lower_le_limit _) (hF.mono (E.lowerBridge_subset_base m))

/-- The upper bridge covers the corresponding lower bridge by the intermediate
value theorem, as in the bridge argument following [LY75, Lemma 0, p. 987]. -/
theorem upperToLowerCover (E : ReversingNestLimits F b c N)
    (hF : ContinuousOn F (Icc b c)) (m : ℕ) :
    Icc (N.lower m) E.lowerLimit ⊆
      F '' Icc E.upperLimit (N.upper (m + 1)) := by
  simpa [N.map_upper, E.map_upperLimit] using
    intermediate_value_Icc' (E.limit_le_upper _) (hF.mono (E.upperBridge_subset_base m))

/-- The top bridge covers the preceding interval; this is the terminal bridge
used in the reversing Li--Yorke construction [LY75, p. 987]. -/
theorem upperZero_covers_K (E : ReversingNestLimits F b c N)
    (hF : ContinuousOn F (Icc b c))
    {a d : ℝ} (hFc : F c = d) (hda : d ≤ a) (_hab : a < b) :
    Icc a b ⊆ F '' Icc E.upperLimit c := by
  have hsub : Icc E.upperLimit c ⊆ Icc b c := by
    apply Icc_subset_Icc
    · exact ((E.lower_mem 0).1.trans (E.lower_le_limit 0)).trans E.limits_ordered
    · exact le_rfl
  have hcover : Icc d E.lowerLimit ⊆ F '' Icc E.upperLimit c := by
    simpa [E.map_upperLimit, hFc] using
      intermediate_value_Icc' ((E.limit_le_upper 0).trans (by simp [N.upper_zero]))
        (hF.mono hsub)
  have hbl : b ≤ E.lowerLimit := by simpa [N.lower_zero] using E.lower_le_limit 0
  exact (Icc_subset_Icc hda hbl).trans hcover

end ReversingNestLimits

/-- The increasing orbit-order data enriched with a reversing nest and its
limit bridges; it packages the construction in [LY75, Appendix 2(a)-(c), p. 991]. -/
structure IncreasingReversingData (J : Set ℝ) (F : ℝ → ℝ) (a : ℝ) where
  /-- The recursively nested reversing intervals. -/
  nest : ReversingNest F (F a) ((F^[2]) a)
  /-- The exchanged endpoint limits of `nest`. -/
  limits : ReversingNestLimits F (F a) ((F^[2]) a) nest
  /-- The `K` interval lies in the ambient set. -/
  k_subset : Icc a (F a) ⊆ J
  /-- The base interval lies in the ambient set. -/
  base_subset : Icc (F a) ((F^[2]) a) ⊆ J
  /-- Continuity on the base interval. -/
  continuousOn_base : ContinuousOn F (Icc (F a) ((F^[2]) a))
  /-- The base interval is covered by the image of `K`. -/
  base_subset_image_k : Icc (F a) ((F^[2]) a) ⊆ F '' Icc a (F a)
  /-- The `K` interval is covered by the image of the base interval. -/
  k_subset_image_base : Icc a (F a) ⊆ F '' Icc (F a) ((F^[2]) a)
  /-- The base interval covers itself under the map. -/
  base_subset_image_base : Icc (F a) ((F^[2]) a) ⊆ F '' Icc (F a) ((F^[2]) a)
  /-- The upper limit covers the `K` interval under the map. -/
  upperZero_covers_k : Icc a (F a) ⊆ F '' Icc limits.upperLimit ((F^[2]) a)

/-- The increasing Li--Yorke order configuration supplies the reversing nest,
all required interval covers, and its endpoint limits [LY75, Appendix 2(a)-(c), p. 991]. -/
theorem existsReversingNestOfIncreasingOrder
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (hJ : J.OrdConnected) (hF : ContinuousOn F J)
    (hFJ : MapsTo F J J) (haJ : a ∈ J)
    (horder : (F^[3]) a ≤ a ∧ a < F a ∧ F a < (F^[2]) a) :
    Nonempty (IncreasingReversingData J F a) := by
  let b := F a
  let c := F b
  let d := F c
  have hiter2 : (F^[2]) a = c := by simp [b, c, Function.iterate_succ_apply']
  have hiter3 : (F^[3]) a = d := by simp [b, c, d, Function.iterate_succ_apply']
  have hda : d ≤ a := hiter3 ▸ horder.1
  have hab : a < b := horder.2.1
  have hbc : b < c := hiter2 ▸ horder.2.2
  have hbJ : b ∈ J := hFJ haJ
  have hcJ : c ∈ J := hFJ hbJ
  have hKJ : Icc a b ⊆ J := hJ.out haJ hbJ
  have hLJ : Icc b c ⊆ J := hJ.out hbJ hcJ
  have hbase : ContinuousOn F (Icc b c) := hF.mono hLJ
  have hFb : F b = c := rfl
  have hFc : F c ≤ b := hda.trans hab.le
  rcases existsReversingNest hbc hbase hFb hFc with ⟨N⟩
  rcases N.existsLimits hbase with ⟨E⟩
  refine ⟨{
    nest := N
    limits := E
    k_subset := by simpa [b] using hKJ
    base_subset := by simpa [b, hiter2] using hLJ
    continuousOn_base := by simpa [b, hiter2] using hbase
    base_subset_image_k := by
      simpa [b, c, hiter2] using intermediate_value_Icc hab.le (hF.mono hKJ)
    k_subset_image_base := by
      have hdc : Icc d c ⊆ F '' Icc b c := by
        simpa [hFb] using intermediate_value_Icc' hbc.le hbase
      simpa [b, c, d, hiter2, hiter3] using (Icc_subset_Icc hda hbc.le).trans hdc
    base_subset_image_base := by
      have hdc : Icc d c ⊆ F '' Icc b c := by
        simpa [hFb] using intermediate_value_Icc' hbc.le hbase
      simpa [b, c, d, hiter2, hiter3] using
        ((Icc_subset_Icc hab.le le_rfl).trans ((Icc_subset_Icc hda le_rfl).trans hdc))
    upperZero_covers_k := by
      simpa [b, c, d, hiter2] using E.upperZero_covers_K hbase (by rfl) hda hab
  }⟩

end PeriodThree
