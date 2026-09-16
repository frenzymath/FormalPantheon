import PrimesRestrictedDigits.MajorArcs.Weights
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Projected prime boxes

This gives the finite normalized-log box used for `Lambda_C` in Eqs. (11.2)
and (11.3) of `MAYNARD-PRD-PUBLISHED`. It represents exactly the product fibers
below `X`; the full `R_X` region and its last coordinate remain separate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The normalized logarithmic coordinate used in Eq. (9.1) of
`MAYNARD-PRD-PUBLISHED`. -/
noncomputable def normalizedPrimeLog (X p : ℕ) : ℝ :=
  Real.log (p : ℝ) / Real.log (X : ℝ)

/-- The finite ordered prime tuples in the projected box
`prod_i (a_i, a_i + delta]`, truncated coordinatewise at `X`. -/
noncomputable def projectedPrimeBoxTuples (X : ℕ) {k : ℕ}
    (a : Fin k → ℝ) (δ : ℝ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => Nat.primesLE X)).filter fun p =>
    ∀ i, normalizedPrimeLog X (p i) ∈ Set.Ioc (a i) (a i + δ)

/-- The product fiber weight of the `X`-truncated projected prime box. -/
noncomputable def projectedPrimeBoxWeightAtProduct
    (X : ℕ) {k : ℕ} (a : Fin k → ℝ) (δ : ℝ) (m : ℕ) : ℝ :=
  primeTupleWeightAtProduct (projectedPrimeBoxTuples X a δ) m

theorem normalizedPrimeLog_mem_Ioc_iff_rpow {X p : ℕ}
    (hX : 1 < X) (hp : p.Prime) (lower upper : ℝ) :
    normalizedPrimeLog X p ∈ Set.Ioc lower upper ↔
      (X : ℝ) ^ lower < (p : ℝ) ∧ (p : ℝ) ≤ (X : ℝ) ^ upper := by
  have hXreal : (1 : ℝ) < X := by exact_mod_cast hX
  have hpreal : (0 : ℝ) < p := by exact_mod_cast hp.pos
  change (lower < Real.logb (X : ℝ) (p : ℝ) ∧
      Real.logb (X : ℝ) (p : ℝ) ≤ upper) ↔ _
  rw [Real.lt_logb_iff_rpow_lt hXreal hpreal,
    Real.logb_le_iff_le_rpow hXreal hpreal]

theorem mem_projectedPrimeBoxTuples_iff {X k : ℕ} {a : Fin k → ℝ} {δ : ℝ}
    {p : Fin k → ℕ} :
    p ∈ projectedPrimeBoxTuples X a δ ↔
      (∀ i, p i ∈ Nat.primesLE X) ∧
        ∀ i, normalizedPrimeLog X (p i) ∈ Set.Ioc (a i) (a i + δ) := by
  simp [projectedPrimeBoxTuples, Fintype.mem_piFinset]

theorem mem_projectedPrimeBoxTuples_iff_rpow {X k : ℕ} (hX : 1 < X)
    {a : Fin k → ℝ} {δ : ℝ} {p : Fin k → ℕ} :
    p ∈ projectedPrimeBoxTuples X a δ ↔
      (∀ i, p i ∈ Nat.primesLE X) ∧
        ∀ i, (X : ℝ) ^ (a i) < (p i : ℝ) ∧
          (p i : ℝ) ≤ (X : ℝ) ^ (a i + δ) := by
  rw [mem_projectedPrimeBoxTuples_iff]
  apply and_congr_right
  intro hp
  apply forall_congr'
  intro i
  exact normalizedPrimeLog_mem_Ioc_iff_rpow hX
    (Nat.prime_of_mem_primesLE (hp i)) _ _

theorem prime_of_mem_projectedPrimeBoxTuples {X k : ℕ} {a : Fin k → ℝ} {δ : ℝ}
    {p : Fin k → ℕ} (hp : p ∈ projectedPrimeBoxTuples X a δ) (i : Fin k) :
    (p i).Prime :=
  Nat.prime_of_mem_primesLE ((mem_projectedPrimeBoxTuples_iff.mp hp).1 i)

theorem mem_projectedPrimeBoxTuples_of_prime_of_product_lt
    {X k : ℕ} {a : Fin k → ℝ} {δ : ℝ} {p : Fin k → ℕ}
    (hprime : ∀ i, (p i).Prime) (hproduct : primeTupleProduct p < X)
    (hbox : ∀ i, normalizedPrimeLog X (p i) ∈ Set.Ioc (a i) (a i + δ)) :
    p ∈ projectedPrimeBoxTuples X a δ := by
  rw [mem_projectedPrimeBoxTuples_iff]
  refine ⟨?_, hbox⟩
  intro i
  rw [Nat.mem_primesLE]
  refine ⟨?_, hprime i⟩
  exact (Finset.single_le_prod' (fun j hj => (hprime j).one_le)
    (Finset.mem_univ i)).trans hproduct.le

/-- For `m < X`, the truncated carrier gives exactly the ordered prime tuples
in the source box with product `m`. -/
theorem mem_projectedPrimeBox_productFiber_iff
    {X k m : ℕ} {a : Fin k → ℝ} {δ : ℝ} {p : Fin k → ℕ} (hm : m < X) :
    p ∈ (projectedPrimeBoxTuples X a δ).filter (fun q => primeTupleProduct q = m) ↔
      (∀ i, (p i).Prime) ∧
        (∀ i, normalizedPrimeLog X (p i) ∈ Set.Ioc (a i) (a i + δ)) ∧
          primeTupleProduct p = m := by
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hproduct⟩
    exact ⟨fun i => prime_of_mem_projectedPrimeBoxTuples hp i,
      (mem_projectedPrimeBoxTuples_iff.mp hp).2, hproduct⟩
  · rintro ⟨hprime, hbox, hproduct⟩
    refine ⟨mem_projectedPrimeBoxTuples_of_prime_of_product_lt hprime ?_ hbox, hproduct⟩
    rwa [hproduct]

theorem sum_projectedPrimeBoxWeight_div_le_prime_sum_pow
    (X : ℕ) {k : ℕ} (a : Fin k → ℝ) (δ : ℝ) :
    (∑ m ∈ Finset.range X, projectedPrimeBoxWeightAtProduct X a δ m / (m : ℝ)) ≤
      (∑ p ∈ Nat.primesLE X, Real.log (p : ℝ) / (p : ℝ)) ^ k := by
  unfold projectedPrimeBoxWeightAtProduct
  apply sum_primeTupleWeightAtProduct_div_le_prime_sum_pow
  intro p hp i
  exact prime_of_mem_projectedPrimeBoxTuples hp i

theorem sum_projectedPrimeBoxWeight_div_le_log_pow
    (X : ℕ) {k : ℕ} (a : Fin k → ℝ) (δ : ℝ) (hX : 3 ≤ X) :
    (∑ m ∈ Finset.range X, projectedPrimeBoxWeightAtProduct X a δ m / (m : ℝ)) ≤
      (2 * Real.log 4 * Real.log (X : ℝ)) ^ k := by
  unfold projectedPrimeBoxWeightAtProduct
  apply sum_primeTupleWeightAtProduct_div_le_log_pow
  · intro p hp i
    exact prime_of_mem_projectedPrimeBoxTuples hp i
  · exact hX

/-- The elementary width estimate hidden in the support observation after
Eq. (11.3) of `MAYNARD-PRD-PUBLISHED`. -/
theorem natCast_mul_delta_le_eta_div_six
    {k : ℕ} {eta delta : ℝ} (heta : 0 < eta)
    (hk : (k : ℝ) ≤ 2 / eta) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ eta ^ 2 / 12) :
    (k : ℝ) * delta ≤ eta / 6 := by
  calc
    (k : ℝ) * delta ≤ (2 / eta) * (eta ^ 2 / 12) :=
      mul_le_mul hk hdelta hdelta0 (by positivity)
    _ = eta / 6 := by field_simp; ring

/-- Multiplying coordinate power bounds gives the product bound in the
support observation after Eq. (11.3) of `MAYNARD-PRD-PUBLISHED`. -/
theorem primeTupleProduct_le_rpow_of_coordinate_le
    {X k : ℕ} {a : Fin k → ℝ} {delta : ℝ} {p : Fin k → ℕ}
    (hX : 0 < X)
    (hupper : ∀ i, (p i : ℝ) ≤ (X : ℝ) ^ (a i + delta)) :
    (primeTupleProduct p : ℝ) ≤
      (X : ℝ) ^ ((∑ i, a i) + (k : ℝ) * delta) := by
  rw [primeTupleProduct, Nat.cast_prod]
  calc
    (∏ i, (p i : ℝ)) ≤ ∏ i, (X : ℝ) ^ (a i + delta) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact hupper i
    _ = (X : ℝ) ^ (∑ i, (a i + delta)) := by
      rw [Real.rpow_sum_of_pos (by exact_mod_cast hX)]
    _ = (X : ℝ) ^ ((∑ i, a i) + (k : ℝ) * delta) := by
      congr 1
      rw [Finset.sum_add_distrib, Fin.sum_const]
      simp

/-- The exact weak/strict product-support chain stated after Eq. (11.3), for
an unrestricted tuple satisfying the source coordinate upper bounds. -/
theorem primeTupleProduct_support_bounds_of_coordinate_le
    {X k : ℕ} {a : Fin k → ℝ} {delta eta : ℝ} {p : Fin k → ℕ}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : ℕ) : ℝ) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hupper : ∀ i, (p i : ℝ) ≤ (X : ℝ) ^ (a i + delta)) :
    (primeTupleProduct p : ℝ) ≤
        (X : ℝ) ^ ((∑ i, a i) + (k : ℝ) * delta) ∧
      (X : ℝ) ^ ((∑ i, a i) + (k : ℝ) * delta) <
        (X : ℝ) ^ (1 - eta / 3) := by
  have hk : (k : ℝ) ≤ 2 / eta := by
    calc
      (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      _ ≤ 2 / eta := hell
  have hdeltaBound :=
    natCast_mul_delta_le_eta_div_six heta hk hdelta0 hdelta
  have hexponent : (∑ i, a i) + (k : ℝ) * delta < 1 - eta / 3 := by
    linarith
  exact ⟨primeTupleProduct_le_rpow_of_coordinate_le
      (Nat.zero_lt_of_lt hX) hupper,
    Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hX) hexponent⟩

/-- Nonzero projected-box weight is supported on the exact range stated after
Eq. (11.3) of `MAYNARD-PRD-PUBLISHED`. -/
theorem projectedPrimeBoxWeightAtProduct_support_bounds
    {X k m : ℕ} {a : Fin k → ℝ} {delta eta : ℝ}
    (hX : 1 < X) (heta : 0 < eta)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : ℕ) : ℝ) ≤ 2 / eta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta ^ 2 / 12)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0) :
    (m : ℝ) ≤ (X : ℝ) ^ ((∑ i, a i) + (k : ℝ) * delta) ∧
      (X : ℝ) ^ ((∑ i, a i) + (k : ℝ) * delta) <
        (X : ℝ) ^ (1 - eta / 3) := by
  unfold projectedPrimeBoxWeightAtProduct primeTupleWeightAtProduct at hweight
  obtain ⟨p, hp⟩ := Finset.nonempty_of_sum_ne_zero hweight
  rcases Finset.mem_filter.mp hp with ⟨hpbox, hproduct⟩
  rw [← hproduct]
  apply primeTupleProduct_support_bounds_of_coordinate_le
    hX heta hsum hell hdelta0 hdelta
  intro i
  exact ((mem_projectedPrimeBoxTuples_iff_rpow hX).mp hpbox).2 i |>.2

/-- A concrete double-exponential threshold implies the logarithmic
small-width threshold used after Eq. (11.3). -/
theorem twelve_div_eta_sq_le_log_log_of_exp_exp_le {X eta : ℝ}
    (hlarge : Real.exp (Real.exp (12 / eta ^ 2)) ≤ X) :
    12 / eta ^ 2 ≤ Real.log (Real.log X) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos (by
    have : 1 < Real.exp (Real.exp (12 / eta ^ 2)) := by
      rw [Real.one_lt_exp_iff]
      exact Real.exp_pos _
    exact this.trans_le hlarge)
  apply (Real.le_log_iff_exp_le hlogXpos).2
  rw [← Real.exp_le_exp, Real.exp_log hXpos]
  exact hlarge

/-- The logarithmic threshold makes Maynard's choice
`delta = (log (log X))⁻¹` at most `eta ^ 2 / 12`. -/
theorem inv_log_log_le_eta_sq_div_twelve {X eta : ℝ} (heta : 0 < eta)
    (hloglog : 12 / eta ^ 2 ≤ Real.log (Real.log X)) :
    (Real.log (Real.log X))⁻¹ ≤ eta ^ 2 / 12 := by
  have hpos : 0 < 12 / eta ^ 2 := by positivity
  calc
    (Real.log (Real.log X))⁻¹ = 1 / Real.log (Real.log X) := by rw [one_div]
    _ ≤ 1 / (12 / eta ^ 2) := one_div_le_one_div_of_le hpos hloglog
    _ = eta ^ 2 / 12 := by field_simp

/-- The support statement after Eq. (11.3) with the paper's exact
`delta = (log (log X))⁻¹` and an explicit sufficient lower bound on `X`. -/
theorem projectedPrimeBoxWeightAtProduct_logLog_support_bounds
    {X k m : ℕ} {a : Fin k → ℝ} {eta : ℝ}
    (heta : 0 < eta) (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : ℕ) : ℝ) ≤ 2 / eta)
    (hlarge : Real.exp (Real.exp (12 / eta ^ 2)) ≤ (X : ℝ))
    (hweight : projectedPrimeBoxWeightAtProduct X a
      (Real.log (Real.log (X : ℝ)))⁻¹ m ≠ 0) :
    (m : ℝ) ≤ (X : ℝ) ^ ((∑ i, a i) +
        (k : ℝ) * (Real.log (Real.log (X : ℝ)))⁻¹) ∧
      (X : ℝ) ^ ((∑ i, a i) +
        (k : ℝ) * (Real.log (Real.log (X : ℝ)))⁻¹) <
        (X : ℝ) ^ (1 - eta / 3) := by
  have hXreal : (1 : ℝ) < X := by
    have : 1 < Real.exp (Real.exp (12 / eta ^ 2)) := by
      rw [Real.one_lt_exp_iff]
      exact Real.exp_pos _
    exact this.trans_le hlarge
  have hX : 1 < X := by exact_mod_cast hXreal
  have hloglog := twelve_div_eta_sq_le_log_log_of_exp_exp_le hlarge
  have hdelta0 : 0 ≤ (Real.log (Real.log (X : ℝ)))⁻¹ :=
    inv_nonneg.mpr ((show (0 : ℝ) ≤ 12 / eta ^ 2 by positivity).trans hloglog)
  exact projectedPrimeBoxWeightAtProduct_support_bounds hX heta hsum hell hdelta0
    (inv_log_log_le_eta_sq_div_twelve heta hloglog) hweight

end PrimesRestrictedDigits
