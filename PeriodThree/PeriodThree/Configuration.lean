module

public import PeriodThree.Statement

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by the orbit-order proof)

/-!
# Period-three orbit configurations

A least-period-three orbit consists of three distinct points.  Ordering those
points yields one of Li and Yorke's two orbit-order alternatives [LY75,
remark following Theorem I, p. 987].
-/

@[expose] public section

open Set

namespace PeriodThree

/-- A point of least period three has a cyclic rotation satisfying one of the
two orbit-order alternatives in [LY75, p. 987]. -/
theorem existsOrbitOrderOfMinimalPeriodEqThree
    {J : Set ℝ} {F : ℝ → ℝ} (hFJ : MapsTo F J J)
    {x : ℝ} (hxJ : x ∈ J) (hx : Function.minimalPeriod F x = 3) :
    ∃ a ∈ J, OrbitOrder F a := by
  have hperiod : Function.IsPeriodicPt F 3 x := by
    simpa [hx] using Function.isPeriodicPt_minimalPeriod F x
  let x0 := x
  let x1 := F x
  let x2 := (F^[2]) x
  have hx0J : x0 ∈ J := hxJ
  have hx1J : x1 ∈ J := hFJ hxJ
  have hx2J : x2 ∈ J := by
    simpa [x2, Function.iterate_succ_apply'] using hFJ (hFJ hxJ)
  have hx01 : x0 ≠ x1 := by
    intro h
    have heq : (0 : ℕ) = 1 :=
      Function.iterate_injOn_Iio_minimalPeriod
        (f := F) (x := x) (by simp [hx]) (by simp [hx]) (by simpa [x0, x1] using h)
    omega
  have hx02 : x0 ≠ x2 := by
    intro h
    have heq : (0 : ℕ) = 2 :=
      Function.iterate_injOn_Iio_minimalPeriod
        (f := F) (x := x) (by simp [hx]) (by simp [hx]) (by simpa [x0, x2] using h)
    omega
  have hx12 : x1 ≠ x2 := by
    intro h
    have heq : (1 : ℕ) = 2 :=
      Function.iterate_injOn_Iio_minimalPeriod
        (f := F) (x := x) (by simp [hx]) (by simp [hx]) (by simpa [x1, x2] using h)
    omega
  have hmap01 : F x0 = x1 := rfl
  have hmap12 : F x1 = x2 := by simp [x1, x2, Function.iterate_succ_apply']
  have hmap20 : F x2 = x0 := by
    simpa [x0, x2, Function.iterate_succ_apply'] using hperiod.eq
  have hiter2_0 : (F^[2]) x0 = x2 := by simp [x0, x2]
  have hiter2_1 : (F^[2]) x1 = x0 := by
    simp [Function.iterate_succ_apply', hmap12, hmap20]
  have hiter2_2 : (F^[2]) x2 = x1 := by
    simp [Function.iterate_succ_apply', hmap20, hmap01]
  have hiter3_0 : (F^[3]) x0 = x0 := by simpa [x0] using hperiod.eq
  have hiter3_1 : (F^[3]) x1 = x1 := by
    simp [Function.iterate_succ_apply', hmap12, hmap20, hmap01]
  have hiter3_2 : (F^[3]) x2 = x2 := by
    simp [Function.iterate_succ_apply', hmap20, hmap01, hmap12]
  rcases lt_or_gt_of_ne hx01 with hx0x1 | hx1x0
  · rcases lt_or_gt_of_ne hx12 with hx1x2 | hx2x1
    · refine ⟨x0, hx0J, Or.inl ?_⟩
      rw [hiter3_0, hmap01, hiter2_0]
      exact ⟨le_rfl, hx0x1, hx1x2⟩
    · rcases lt_or_gt_of_ne hx02 with hx0x2 | hx2x0
      · refine ⟨x1, hx1J, Or.inr ?_⟩
        rw [hiter3_1, hmap12, hiter2_1]
        exact ⟨le_rfl, hx2x1, hx0x2⟩
      · refine ⟨x2, hx2J, Or.inl ?_⟩
        rw [hiter3_2, hmap20, hiter2_2]
        exact ⟨le_rfl, hx2x0, hx0x1⟩
  · rcases lt_or_gt_of_ne hx12 with hx1x2 | hx2x1
    · rcases lt_or_gt_of_ne hx02 with hx0x2 | hx2x0
      · refine ⟨x2, hx2J, Or.inr ?_⟩
        rw [hiter3_2, hmap20, hiter2_2]
        exact ⟨le_rfl, hx0x2, hx1x0⟩
      · refine ⟨x1, hx1J, Or.inl ?_⟩
        rw [hiter3_1, hmap12, hiter2_1]
        exact ⟨le_rfl, hx1x2, hx2x0⟩
    · refine ⟨x0, hx0J, Or.inr ?_⟩
      rw [hiter3_0, hmap01, hiter2_0]
      exact ⟨le_rfl, hx1x0, hx2x1⟩

/-- The complete Li-Yorke theorem implies its advertised period-three
corollary by ordering the three orbit points [LY75, remark following Theorem I,
p. 987]. -/
theorem periodThreeImpliesChaosOfLiYorkeTheorem
    (hLiYorke : LiYorkeTheorem) : PeriodThreeImpliesChaos := by
  intro J F hJ hF hFJ hperiodThree
  obtain ⟨x, hxJ, hxperiod⟩ := hperiodThree
  obtain ⟨a, haJ, horder⟩ :=
    existsOrbitOrderOfMinimalPeriodEqThree hFJ hxJ hxperiod
  exact hLiYorke J F a hJ hF hFJ haJ horder

end PeriodThree
