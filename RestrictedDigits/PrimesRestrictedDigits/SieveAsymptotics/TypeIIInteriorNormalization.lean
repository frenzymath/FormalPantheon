import PrimesRestrictedDigits.SieveAsymptotics.TypeIIInteriorFiber

/-!
# Interior major-arc cell normalization

This file formalizes the additive logarithmic-weight normalization in
Eq. (9.9) of `MAYNARD-PRD-PUBLISHED`.  The singleton-fiber input is supplied
by the verified interior ordering layer in `TypeIIInteriorFiber`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The nominal normalized-log product of an interior cell. -/
noncomputable def typeIICellCoefficient {k : Nat} (a : Fin k -> Real) : Real :=
  (1 - ∑ i, a i) * ∏ i, a i

/-- The eta-only coordinate floor used uniformly over admissible cells. -/
noncomputable def typeIIEtaCoordinateFloor (eta : Real) : Real :=
  min 1 (eta / 2)

/-- The eta-only ceiling for the number of prime coordinates. -/
noncomputable def typeIIEtaArityCeiling (eta : Real) : Nat :=
  Nat.ceil (2 / eta)

/-- A positive eta-only lower bound for every admissible cell coefficient. -/
noncomputable def typeIIEtaCellFloor (eta : Real) : Real :=
  typeIIEtaCoordinateFloor eta ^ typeIIEtaArityCeiling eta

/-- Products on a finite unit cube are one-Lipschitz for the `l1` distance. -/
theorem abs_finsetProd_sub_finsetProd_le_sum_abs_sub
    {index : Type*} (s : Finset index) (x y : index -> Real)
    (hx0 : ∀ i ∈ s, 0 <= x i) (hx1 : ∀ i ∈ s, x i <= 1)
    (hy0 : ∀ i ∈ s, 0 <= y i) (hy1 : ∀ i ∈ s, y i <= 1) :
    |∏ i ∈ s, x i - ∏ i ∈ s, y i| <=
      ∑ i ∈ s, |x i - y i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hx0a : 0 <= x a := hx0 a (Finset.mem_insert_self _ _)
      have hx1a : x a <= 1 := hx1 a (Finset.mem_insert_self _ _)
      have hy0s : ∀ i ∈ s, 0 <= y i := fun i hi =>
        hy0 i (Finset.mem_insert_of_mem hi)
      have hy1s : ∀ i ∈ s, y i <= 1 := fun i hi =>
        hy1 i (Finset.mem_insert_of_mem hi)
      have hprodY0 : 0 <= ∏ i ∈ s, y i := Finset.prod_nonneg hy0s
      have hprodY1 : (∏ i ∈ s, y i) <= 1 :=
        Finset.prod_le_one hy0s hy1s
      have hsum0 : 0 <= ∑ i ∈ s, |x i - y i| :=
        Finset.sum_nonneg fun i hi => abs_nonneg _
      have ih' := ih
        (fun i hi => hx0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hx1 i (Finset.mem_insert_of_mem hi)) hy0s hy1s
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      calc
        |x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i| =
            |x a * ((∏ i ∈ s, x i) - ∏ i ∈ s, y i) +
              (x a - y a) * ∏ i ∈ s, y i| := by
              congr 1
              ring
        _ <= |x a * ((∏ i ∈ s, x i) - ∏ i ∈ s, y i)| +
              |(x a - y a) * ∏ i ∈ s, y i| := abs_add_le _ _
        _ = x a * |(∏ i ∈ s, x i) - ∏ i ∈ s, y i| +
              |x a - y a| * ∏ i ∈ s, y i := by
              rw [abs_mul, abs_mul, abs_of_nonneg hx0a,
                abs_of_nonneg hprodY0]
        _ <= x a * (∑ i ∈ s, |x i - y i|) +
              |x a - y a| * ∏ i ∈ s, y i := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left ih' hx0a) le_rfl
        _ <= (∑ i ∈ s, |x i - y i|) + |x a - y a| := by
              exact add_le_add
                (by simpa using mul_le_mul_of_nonneg_right hx1a hsum0)
                (by simpa using mul_le_mul_of_nonneg_left hprodY1 (abs_nonneg _))
        _ = |x a - y a| + ∑ i ∈ s, |x i - y i| := by ring

/-- Fintype form of the finite-product perturbation estimate. -/
theorem abs_fintypeProd_sub_fintypeProd_le_sum_abs_sub
    {index : Type*} [Fintype index] (x y : index -> Real)
    (hx : ∀ i, x i ∈ Set.Icc (0 : Real) 1)
    (hy : ∀ i, y i ∈ Set.Icc (0 : Real) 1) :
    |∏ i, x i - ∏ i, y i| <= ∑ i, |x i - y i| := by
  exact abs_finsetProd_sub_finsetProd_le_sum_abs_sub Finset.univ x y
    (fun i _ => (hx i).1) (fun i _ => (hx i).2)
    (fun i _ => (hy i).1) (fun i _ => (hy i).2)

/-- A tuple log-weight is a logarithmic power times the product of its
normalized logarithmic coordinates. -/
theorem primeTupleLogWeight_eq_log_pow_mul_normalizedPrimeLog_prod
    {X ell : Nat} (hX : 1 < X) (p : Fin ell -> Nat) :
    primeTupleLogWeight p =
      Real.log (X : Real) ^ ell * ∏ i, normalizedPrimeLog X (p i) := by
  have hXreal : (1 : Real) < X := by exact_mod_cast hX
  have hlogX : Real.log (X : Real) ≠ 0 := (Real.log_pos hXreal).ne'
  unfold primeTupleLogWeight
  calc
    (∏ i, Real.log (p i : Real)) =
        ∏ i, (Real.log (X : Real) * normalizedPrimeLog X (p i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      unfold normalizedPrimeLog
      field_simp
    _ = (∏ _i : Fin ell, Real.log (X : Real)) *
        ∏ i, normalizedPrimeLog X (p i) := by
      rw [Finset.prod_mul_distrib]
    _ = Real.log (X : Real) ^ ell *
        ∏ i, normalizedPrimeLog X (p i) := by simp

private theorem normalizedPrimeLog_mem_unitInterval_of_mem_majorArcPrimeTuples
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {q : Fin (k + 1) -> Nat} (hX : 1 < X)
    (hq : q ∈ majorArcPrimeTuples X a delta eta) :
    ∀ i, normalizedPrimeLog X (q i) ∈ Set.Icc (0 : Real) 1 := by
  let e := fun i => normalizedPrimeLog X (q i)
  have heRegion : e ∈ majorArcLogRegion a delta eta :=
    (mem_majorArcPrimeTuples_iff.mp hq).2
  have he0 : ∀ i, 0 <= e i := by
    intro i
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg (by
      exact_mod_cast hX.le))
  intro i
  refine ⟨he0 i, ?_⟩
  have hi : e i <= ∑ j, e j :=
    Finset.single_le_sum (fun j _ => he0 j) (Finset.mem_univ i)
  exact hi.trans heRegion.2.1

private theorem completeProjectedLogTuple_mem_unitInterval
    {k : Nat} {a : Fin k -> Real} {eta : Real} (heta : 0 < eta)
    (ha : ∀ i, eta / 2 <= a i)
    (hsum : (∑ i, a i) < 1 - eta / 2) :
    ∀ i, completeProjectedLogTuple a i ∈ Set.Icc (0 : Real) 1 := by
  have ha0 : ∀ i, 0 <= a i := fun i => (by linarith [ha i])
  have hsum0 : 0 <= ∑ i, a i := Finset.sum_nonneg fun i _ => ha0 i
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [last_completeProjectedLogTuple]
    constructor <;> linarith
  · simp only [completeProjectedLogTuple, Fin.snoc_castSucc]
    refine ⟨ha0 j, ?_⟩
    have hj : a j <= ∑ i, a i :=
      Finset.single_le_sum (fun i _ => ha0 i) (Finset.mem_univ j)
    linarith

private theorem sum_coordinate_errors_le
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {q : Fin (k + 1) -> Nat} (hdelta : 0 <= delta)
    (hq : q ∈ majorArcPrimeTuples X a delta eta) :
    (∑ i, |normalizedPrimeLog X (q i) - completeProjectedLogTuple a i|) <=
      2 * ((k + 1 : Nat) : Real) * delta := by
  let e := fun i => normalizedPrimeLog X (q i)
  have heRegion : e ∈ majorArcLogRegion a delta eta :=
    (mem_majorArcPrimeTuples_iff.mp hq).2
  have hprefix : ∀ i, e i.castSucc ∈ Set.Ioc (a i) (a i + delta) := by
    simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using heRegion.1
  have hprefixError : ∀ i, |e i.castSucc - a i| <= delta := by
    intro i
    rw [abs_of_nonneg (sub_nonneg.mpr (hprefix i).1.le)]
    linarith [(hprefix i).2]
  have hprefixSum : (∑ i, a i) <= ∑ i : Fin k, e i.castSucc := by
    exact Finset.sum_le_sum fun (i : Fin k) _ => (hprefix i).1.le
  have hlastUpper : e (Fin.last k) <= 1 - ∑ i, a i := by
    have htotal := heRegion.2.1
    rw [Fin.sum_univ_castSucc] at htotal
    linarith
  have hlastLower :
      1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta <=
        e (Fin.last k) :=
    (le_max_right _ _).trans heRegion.2.2
  have hlastError :
      |e (Fin.last k) - (1 - ∑ i, a i)| <=
        ((k + 1 : Nat) : Real) * delta := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlastUpper)]
    linarith
  change (∑ i, |e i - completeProjectedLogTuple a i|) <= _
  rw [Fin.sum_univ_castSucc]
  simp only [completeProjectedLogTuple, Fin.snoc_castSucc, Fin.snoc_last]
  calc
    (∑ i, |e i.castSucc - a i|) +
        |e (Fin.last k) - (1 - ∑ i, a i)| <=
      (∑ _i : Fin k, delta) + ((k + 1 : Nat) : Real) * delta :=
        add_le_add (Finset.sum_le_sum fun i _ => hprefixError i) hlastError
    _ = (k : Real) * delta + ((k + 1 : Nat) : Real) * delta := by simp
    _ <= 2 * ((k + 1 : Nat) : Real) * delta := by
      have hk : (k : Real) <= ((k + 1 : Nat) : Real) := by
        exact_mod_cast Nat.le_succ k
      nlinarith [mul_le_mul_of_nonneg_right hk hdelta]

/--
Every tuple in an admissible cell has normalized-log product within the `2 * (k + 1) * delta`
error of the nominal cell coefficient.
-/
theorem abs_normalizedPrimeLog_prod_sub_typeIICellCoefficient_le
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {q : Fin (k + 1) -> Nat} (hX : 1 < X) (heta : 0 < eta)
    (hdelta : 0 <= delta) (ha : ∀ i, eta / 2 <= a i)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hq : q ∈ majorArcPrimeTuples X a delta eta) :
    |∏ i, normalizedPrimeLog X (q i) - typeIICellCoefficient a| <=
      2 * ((k + 1 : Nat) : Real) * delta := by
  have hproduct := abs_fintypeProd_sub_fintypeProd_le_sum_abs_sub
    (fun i => normalizedPrimeLog X (q i)) (completeProjectedLogTuple a)
    (normalizedPrimeLog_mem_unitInterval_of_mem_majorArcPrimeTuples hX hq)
    (completeProjectedLogTuple_mem_unitInterval heta ha hsum)
  have hcompleteProduct :
      (∏ i, completeProjectedLogTuple a i) = typeIICellCoefficient a := by
    rw [Fin.prod_univ_castSucc]
    simp [completeProjectedLogTuple, typeIICellCoefficient, mul_comm]
  rw [hcompleteProduct] at hproduct
  exact hproduct.trans (sum_coordinate_errors_le hdelta hq)

/-- Tuple weights differ from the nominal cell scale by the accepted linear
error from Eq. (9.9). -/
theorem abs_primeTupleLogWeight_sub_typeIICellScale_le
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {q : Fin (k + 1) -> Nat} (hX : 1 < X) (heta : 0 < eta)
    (hdelta : 0 <= delta) (ha : ∀ i, eta / 2 <= a i)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hq : q ∈ majorArcPrimeTuples X a delta eta) :
    |primeTupleLogWeight q -
        typeIICellCoefficient a * Real.log (X : Real) ^ (k + 1)| <=
      2 * ((k + 1 : Nat) : Real) * delta *
        Real.log (X : Real) ^ (k + 1) := by
  rw [primeTupleLogWeight_eq_log_pow_mul_normalizedPrimeLog_prod hX]
  have hlogPow : 0 <= Real.log (X : Real) ^ (k + 1) := by positivity
  calc
    |Real.log (X : Real) ^ (k + 1) *
          (∏ i, normalizedPrimeLog X (q i)) -
        typeIICellCoefficient a * Real.log (X : Real) ^ (k + 1)| =
      Real.log (X : Real) ^ (k + 1) *
        |(∏ i, normalizedPrimeLog X (q i)) - typeIICellCoefficient a| := by
          have hfactor :
              Real.log (X : Real) ^ (k + 1) *
                    (∏ i, normalizedPrimeLog X (q i)) -
                  typeIICellCoefficient a * Real.log (X : Real) ^ (k + 1) =
                Real.log (X : Real) ^ (k + 1) *
                  ((∏ i, normalizedPrimeLog X (q i)) -
                    typeIICellCoefficient a) := by ring
          rw [hfactor, abs_mul, abs_of_nonneg hlogPow]
    _ <= Real.log (X : Real) ^ (k + 1) *
        (2 * ((k + 1 : Nat) : Real) * delta) :=
      mul_le_mul_of_nonneg_left
        (abs_normalizedPrimeLog_prod_sub_typeIICellCoefficient_le
          hX heta hdelta ha hsum hq) hlogPow
    _ = 2 * ((k + 1 : Nat) : Real) * delta *
        Real.log (X : Real) ^ (k + 1) := by ring

/-- Regroup a product-fiber weight over an arbitrary finite natural carrier. -/
theorem sum_primeTupleWeightAtProduct_eq_sum_filter_product_mem
    {ell : Nat} (tuples : Finset (Fin ell -> Nat)) (C : Finset Nat) :
    (∑ n ∈ C, primeTupleWeightAtProduct tuples n) =
      ∑ p ∈ tuples with primeTupleProduct p ∈ C, primeTupleLogWeight p := by
  classical
  unfold primeTupleWeightAtProduct
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hproduct : primeTupleProduct p ∈ C
  · rw [Finset.sum_eq_single (primeTupleProduct p)]
    · simp [hproduct]
    · intro n hn hne
      simp [hne.symm]
    · exact fun hnotmem => (hnotmem hproduct).elim
  · simp only [if_neg hproduct]
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg]
    intro heq
    exact hproduct (heq ▸ hn)

/-- An injective tuple product converts the weighted sum to its Boolean
support count with the accumulated pointwise normalization error. -/
theorem abs_sum_primeTupleWeightAtProduct_sub_scale_mul_supportCount_le
    {ell : Nat} (tuples : Finset (Fin ell -> Nat)) (C : Finset Nat)
    (scale error : Real)
    (hinj : Set.InjOn primeTupleProduct (tuples : Set (Fin ell -> Nat)))
    (hweight : ∀ p ∈ tuples, |primeTupleLogWeight p - scale| <= error) :
    |(∑ n ∈ C, primeTupleWeightAtProduct tuples n) -
        scale * (((primeTupleProductSupport tuples).filter
          (fun n => n ∈ C)).card : Real)| <=
      error * (((primeTupleProductSupport tuples).filter
        (fun n => n ∈ C)).card : Real) := by
  classical
  let selected := tuples.filter (fun p => primeTupleProduct p ∈ C)
  have hselectedInj :
      Set.InjOn primeTupleProduct (selected : Set (Fin ell -> Nat)) := by
    intro p hp q hq heq
    exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 heq
  have hsupport :
      (primeTupleProductSupport tuples).filter (fun n => n ∈ C) =
        selected.image primeTupleProduct := by
    simp [primeTupleProductSupport, selected, Finset.filter_image]
  have hcard :
      ((primeTupleProductSupport tuples).filter (fun n => n ∈ C)).card =
        selected.card := by
    rw [hsupport, Finset.card_image_of_injOn hselectedInj]
  rw [sum_primeTupleWeightAtProduct_eq_sum_filter_product_mem, hcard]
  change |(∑ p ∈ selected, primeTupleLogWeight p) -
      scale * (selected.card : Real)| <= error * (selected.card : Real)
  have hscale : scale * (selected.card : Real) = ∑ _p ∈ selected, scale := by
    simp [mul_comm]
  rw [hscale, ← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ selected, (primeTupleLogWeight p - scale)| <=
        ∑ p ∈ selected, |primeTupleLogWeight p - scale| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _p ∈ selected, error := by
      apply Finset.sum_le_sum
      intro p hp
      exact hweight p (Finset.mem_filter.mp hp).1
    _ = error * (selected.card : Real) := by simp [mul_comm]

/-- Eq. (9.9) summed over any finite natural carrier, with its accepted
coefficient `2 * (k + 1)`. -/
theorem abs_sum_majorArcRegionWeightAtProduct_sub_typeIICellScale_mul_supportCount_le
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    (C : Finset Nat) (hX : 1 < X) (heta : 0 < eta)
    (hdelta : 0 <= delta) (ha : ∀ i, eta / 2 <= a i)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hsep : typeIIInteriorCellSeparated a delta) :
    |(∑ n ∈ C, majorArcRegionWeightAtProduct X a delta eta n) -
        typeIICellCoefficient a * Real.log (X : Real) ^ (k + 1) *
          (((primeTupleProductSupport
            (majorArcPrimeTuples X a delta eta)).filter
              (fun n => n ∈ C)).card : Real)| <=
      (2 * ((k + 1 : Nat) : Real) * delta *
          Real.log (X : Real) ^ (k + 1)) *
        (((primeTupleProductSupport
          (majorArcPrimeTuples X a delta eta)).filter
            (fun n => n ∈ C)).card : Real) := by
  unfold majorArcRegionWeightAtProduct
  apply abs_sum_primeTupleWeightAtProduct_sub_scale_mul_supportCount_le
    (majorArcPrimeTuples X a delta eta) C
  · exact majorArcPrimeTuples_product_injOn_of_typeIIInteriorCellSeparated
      hX hsep
  · intro q hq
    exact abs_primeTupleLogWeight_sub_typeIICellScale_le
      hX heta hdelta ha hsum hq

/-- Every admissible nominal cell coefficient is strictly positive. -/
theorem typeIICellCoefficient_pos {k : Nat} {a : Fin k -> Real} {eta : Real}
    (heta : 0 < eta) (ha : ∀ i, eta / 2 <= a i)
    (hsum : (∑ i, a i) < 1 - eta / 2) :
    0 < typeIICellCoefficient a := by
  unfold typeIICellCoefficient
  have haPos : ∀ i, 0 < a i := fun i => lt_of_lt_of_le (by linarith) (ha i)
  exact mul_pos (by linarith) (Finset.prod_pos fun i _ => haPos i)

theorem typeIIEtaCoordinateFloor_pos {eta : Real} (heta : 0 < eta) :
    0 < typeIIEtaCoordinateFloor eta := by
  simp [typeIIEtaCoordinateFloor, heta]

theorem typeIIEtaCoordinateFloor_le_one (eta : Real) :
    typeIIEtaCoordinateFloor eta <= 1 := min_le_left _ _

/--
The eta floor is positive before any later cube or margin is chosen.
-/
theorem typeIIEtaCellFloor_pos {eta : Real} (heta : 0 < eta) :
    0 < typeIIEtaCellFloor eta := by
  exact pow_pos (typeIIEtaCoordinateFloor_pos heta) _

/-- The eta-only floor is below every admissible nominal cell coefficient. -/
theorem typeIIEtaCellFloor_le_typeIICellCoefficient
    {k : Nat} {a : Fin k -> Real} {eta : Real} (heta : 0 < eta)
    (ha : ∀ i, eta / 2 <= a i)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hell : ((k + 1 : Nat) : Real) <= 2 / eta) :
    typeIIEtaCellFloor eta <= typeIICellCoefficient a := by
  let q := typeIIEtaCoordinateFloor eta
  have hq0 : 0 <= q := (typeIIEtaCoordinateFloor_pos heta).le
  have hq1 : q <= 1 := typeIIEtaCoordinateFloor_le_one eta
  have hqEta : q <= eta / 2 := min_le_right _ _
  have hellNat : k + 1 <= typeIIEtaArityCeiling eta := by
    exact_mod_cast hell.trans (Nat.le_ceil (2 / eta))
  have hpower : q ^ typeIIEtaArityCeiling eta <= q ^ (k + 1) :=
    pow_le_pow_of_le_one hq0 hq1 hellNat
  have hcoordinate : ∀ i, q <= completeProjectedLogTuple a i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [last_completeProjectedLogTuple]
      exact hqEta.trans (by linarith)
    · simp only [completeProjectedLogTuple, Fin.snoc_castSucc]
      exact hqEta.trans (ha j)
  calc
    typeIIEtaCellFloor eta = q ^ typeIIEtaArityCeiling eta := rfl
    _ <= q ^ (k + 1) := hpower
    _ = ∏ _i : Fin (k + 1), q := by simp
    _ <= ∏ i, completeProjectedLogTuple a i := by
      exact Finset.prod_le_prod (fun i _ => hq0) (fun i _ => hcoordinate i)
    _ = typeIICellCoefficient a := by
      rw [Fin.prod_univ_castSucc]
      simp [typeIICellCoefficient, completeProjectedLogTuple, mul_comm]

private theorem scale_mul_abs_sub_mul_le_of_normalization
    {scale error u v w z lambda : Real} (hscale : 0 <= scale)
    (hlambda : 0 <= lambda)
    (hw : |w - scale * u| <= error * u)
    (hz : |z - scale * v| <= error * v) :
    scale * |u - lambda * v| <=
      |w - lambda * z| + error * (u + lambda * v) := by
  rw [← abs_of_nonneg hscale, ← abs_mul]
  have hid :
      scale * (u - lambda * v) =
        (scale * u - w) + (w - lambda * z) + lambda * (z - scale * v) := by
    ring
  rw [hid]
  calc
    |(scale * u - w) + (w - lambda * z) + lambda * (z - scale * v)| <=
        |scale * u - w| + |w - lambda * z| +
          |lambda * (z - scale * v)| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ = |w - scale * u| + |w - lambda * z| +
        lambda * |z - scale * v| := by
      rw [abs_sub_comm (scale * u), abs_mul, abs_of_nonneg hlambda]
    _ <= error * u + |w - lambda * z| + lambda * (error * v) := by
      exact add_le_add (add_le_add hw le_rfl)
        (mul_le_mul_of_nonneg_left hz hlambda)
    _ = |w - lambda * z| + error * (u + lambda * v) := by ring

/-- Two finite carriers can be compared at once after inserting their two
normalized logarithmic weights. -/
theorem typeIICellScale_mul_abs_supportCount_sub_mul_supportCount_le
    {X k : Nat} {a : Fin k -> Real} {delta eta lambda : Real}
    (C D : Finset Nat) (hX : 1 < X) (heta : 0 < eta)
    (hdelta : 0 <= delta) (hlambda : 0 <= lambda)
    (ha : ∀ i, eta / 2 <= a i)
    (hsum : (∑ i, a i) < 1 - eta / 2)
    (hsep : typeIIInteriorCellSeparated a delta) :
    let tuples := majorArcPrimeTuples X a delta eta
    let supportCount := fun E : Finset Nat =>
      (((primeTupleProductSupport tuples).filter (fun n => n ∈ E)).card : Real)
    let weightSum := fun E : Finset Nat =>
      ∑ n ∈ E, majorArcRegionWeightAtProduct X a delta eta n
    let cellScale := typeIICellCoefficient a * Real.log (X : Real) ^ (k + 1)
    let errorScale := 2 * ((k + 1 : Nat) : Real) * delta *
      Real.log (X : Real) ^ (k + 1)
    cellScale * |supportCount C - lambda * supportCount D| <=
      |weightSum C - lambda * weightSum D| +
        errorScale * (supportCount C + lambda * supportCount D) := by
  dsimp only
  apply scale_mul_abs_sub_mul_le_of_normalization
  · exact mul_nonneg (typeIICellCoefficient_pos heta ha hsum).le (by positivity)
  · exact hlambda
  · exact abs_sum_majorArcRegionWeightAtProduct_sub_typeIICellScale_mul_supportCount_le
      C hX heta hdelta ha hsum hsep
  · exact abs_sum_majorArcRegionWeightAtProduct_sub_typeIICellScale_mul_supportCount_le
      D hX heta hdelta ha hsum hsep

end

end PrimesRestrictedDigits
