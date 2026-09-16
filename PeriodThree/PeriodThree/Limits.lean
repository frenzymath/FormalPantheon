module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Order.LiminfLimsup

/-!
# Extended-real limit bridges

This file translates the frequent real inequalities used in the interval
construction into the extended-real `limsup` and `liminf` clauses of the public
Li-Yorke statement.
-/

@[expose] public section

namespace PeriodThree

/-- A positive real lower bound attained frequently implies positive extended-real
upper limit. This is the `limsup` direction of [LY75, equation (2.1), p. 987]
and condition (B) on the same page. -/
theorem positiveLimsupOfFrequentlyLe
    {u : ℕ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hu : ∃ᶠ n in Filter.atTop, delta ≤ u n) :
    0 < Filter.limsup (fun n => ENNReal.ofReal (u n)) Filter.atTop := by
  have he : ∃ᶠ n in Filter.atTop, ENNReal.ofReal delta ≤ ENNReal.ofReal (u n) :=
    hu.mono fun _ hn => ENNReal.ofReal_le_ofReal hn
  exact (ENNReal.ofReal_pos.mpr hdelta).trans_le
    (Filter.le_limsup_of_frequently_le' he)

/-- Positive extended-real upper limit supplies a positive real lower bound
attained frequently. This is the converse bridge for [LY75, equation (2.1),
p. 987] and condition (B) on the same page. -/
theorem existsPositiveFrequentlyLeOfPositiveLimsup
    {u : ℕ → ℝ}
    (hu : 0 < Filter.limsup (fun n => ENNReal.ofReal (u n)) Filter.atTop) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ᶠ n in Filter.atTop, delta ≤ u n := by
  obtain ⟨delta, hdelta_pos, hdelta_limsup⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hu
  have hdelta_real : 0 < (delta : ℝ) := by
    exact NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hdelta_pos)
  refine ⟨delta, hdelta_real, ?_⟩
  refine (Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hdelta_limsup).mono
    fun _ hn => ?_
  exact (ENNReal.coe_lt_ofReal.mp hn).le

/-- The positive `ENNReal` limsup used in the public Li-Yorke statement is
equivalent to a positive real lower bound occurring frequently. This is [LY75,
equation (2.1) and condition (B), p. 987]. -/
theorem positiveLimsupIffExistsFrequentlyLe
    {u : ℕ → ℝ} :
    0 < Filter.limsup (fun n => ENNReal.ofReal (u n)) Filter.atTop ↔
      ∃ delta : ℝ, 0 < delta ∧ ∃ᶠ n in Filter.atTop, delta ≤ u n := by
  constructor
  · exact existsPositiveFrequentlyLeOfPositiveLimsup
  · rintro ⟨delta, hdelta, hu⟩
    exact positiveLimsupOfFrequentlyLe hdelta hu

/-- If a real sequence is frequently below every positive real threshold, then
its embedded extended-real lower limit is zero. This is the `liminf` direction
of [LY75, equation (2.2), p. 987]. -/
theorem liminfEqZeroOfFrequentlyLt
    {u : ℕ → ℝ}
    (hu : ∀ epsilon : ℝ, 0 < epsilon → ∃ᶠ n in Filter.atTop, u n < epsilon) :
    Filter.liminf (fun n => ENNReal.ofReal (u n)) Filter.atTop = 0 := by
  apply le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun epsilon hepsilon _ => ?_
  rw [ENNReal.bot_eq_zero, zero_add]
  apply Filter.liminf_le_of_frequently_le'
  have hepsilon_real : 0 < (epsilon : ℝ) := NNReal.coe_pos.mpr hepsilon
  refine (hu epsilon hepsilon_real).mono fun _ hn => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hn.le

/-- A zero embedded extended-real lower limit forces the sequence to be
frequently below every positive real threshold. This is the converse bridge
for [LY75, equation (2.2), p. 987]. -/
theorem frequentlyLtOfLiminfEqZero
    {u : ℕ → ℝ}
    (hu : Filter.liminf (fun n => ENNReal.ofReal (u n)) Filter.atTop = 0) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ᶠ n in Filter.atTop, u n < epsilon := by
  intro epsilon hepsilon
  by_contra hfrequent
  have heventual : ∀ᶠ n in Filter.atTop, ¬u n < epsilon :=
    Filter.not_frequently.mp hfrequent
  have hbound : ENNReal.ofReal epsilon ≤
      Filter.liminf (fun n => ENNReal.ofReal (u n)) Filter.atTop := by
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    exact heventual.mono fun _ hn => ENNReal.ofReal_le_ofReal (not_lt.mp hn)
  rw [hu] at hbound
  exact (not_lt_of_ge hbound) (ENNReal.ofReal_pos.mpr hepsilon)

/-- The zero `ENNReal` liminf used in the public Li-Yorke statement is
equivalent to being frequently below every positive real threshold. This is
[LY75, equation (2.2), p. 987]. -/
theorem liminfEqZeroIffFrequentlyLt
    {u : ℕ → ℝ} :
    Filter.liminf (fun n => ENNReal.ofReal (u n)) Filter.atTop = 0 ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∃ᶠ n in Filter.atTop, u n < epsilon := by
  constructor
  · exact frequentlyLtOfLiminfEqZero
  · exact liminfEqZeroOfFrequentlyLt

/-- The positive `ENNReal` limsup condition is equivalent to the elementary
tail formulation from [LY75, equation (2.1) and condition (B), p. 987]. -/
theorem positiveLimsupIffExistsForallExistsGe
    {u : ℕ → ℝ} :
    0 < Filter.limsup (fun n => ENNReal.ofReal (u n)) Filter.atTop ↔
      ∃ delta : ℝ, 0 < delta ∧ ∀ N : ℕ, ∃ n ≥ N, delta ≤ u n := by
  rw [positiveLimsupIffExistsFrequentlyLe]
  constructor
  · rintro ⟨delta, hdelta, hu⟩
    exact ⟨delta, hdelta, Filter.frequently_atTop.mp hu⟩
  · rintro ⟨delta, hdelta, hu⟩
    exact ⟨delta, hdelta, Filter.frequently_atTop.mpr hu⟩

/-- The zero `ENNReal` liminf condition is equivalent to the elementary tail
formulation from [LY75, equation (2.2), p. 987]. -/
theorem liminfEqZeroIffForallForallExistsLt
    {u : ℕ → ℝ} :
    Filter.liminf (fun n => ENNReal.ofReal (u n)) Filter.atTop = 0 ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∀ N : ℕ, ∃ n ≥ N, u n < epsilon := by
  rw [liminfEqZeroIffFrequentlyLt]
  constructor
  · intro hu epsilon hepsilon N
    exact Filter.frequently_atTop.mp (hu epsilon hepsilon) N
  · intro hu epsilon hepsilon
    exact Filter.frequently_atTop.mpr fun N => hu epsilon hepsilon N

end PeriodThree
