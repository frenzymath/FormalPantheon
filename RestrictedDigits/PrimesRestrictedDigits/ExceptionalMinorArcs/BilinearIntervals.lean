import PrimesRestrictedDigits.Foundations.Intervals

/-!
# Factor-ten natural intervals for exceptional bilinear sums

This is the literal source convention `Y / 10 < n <= Y` from `MAYNARD-PRD-PUBLISHED`, Lemma
13.1.
-/

namespace PrimesRestrictedDigits

/-- Natural numbers in the source's strict-lower, weak-upper factor-ten
interval. -/
noncomputable def sourceFactorTenNaturalInterval (Y : Real) : Finset Nat :=
  Finset.Ioc (Nat.floor (Y / 10)) (Nat.floor Y)

@[simp]
theorem mem_sourceFactorTenNaturalInterval_iff
    {Y : Real} (hY : 0 <= Y) {n : Nat} :
    n ∈ sourceFactorTenNaturalInterval Y ↔
      Y / 10 < (n : Real) ∧ (n : Real) <= Y := by
  rw [sourceFactorTenNaturalInterval, Finset.mem_Ioc]
  rw [Nat.floor_lt (by positivity), Nat.le_floor_iff hY]

/-- The real cardinality of the source interval is at most its upper scale. -/
theorem card_sourceFactorTenNaturalInterval_le
    {Y : Real} (hY : 0 <= Y) :
    ((sourceFactorTenNaturalInterval Y).card : Real) <= Y := by
  rw [sourceFactorTenNaturalInterval, Nat.card_Ioc]
  calc
    (((Nat.floor Y - Nat.floor (Y / 10) : Nat) : Real)) <=
        (Nat.floor Y : Real) := by
      exact_mod_cast Nat.sub_le _ _
    _ <= Y := Nat.floor_le hY

/-- Every member is positive once the source scale is positive. -/
theorem sourceFactorTenNaturalInterval_pos
    {Y : Real} (hY : 0 < Y) {n : Nat}
    (hn : n ∈ sourceFactorTenNaturalInterval Y) :
    0 < n := by
  have hnBounds := (mem_sourceFactorTenNaturalInterval_iff hY.le).mp hn
  have hnReal : (0 : Real) < n := (div_pos hY (by norm_num)).trans hnBounds.1
  exact_mod_cast hnReal

end PrimesRestrictedDigits
