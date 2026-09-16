import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionGeometry

/-!
# Type II source-region supports and near-scale normalization

This file defines the source indicator support with denominator `log n` and proves the exact
conversion to denominator `log X` on the near-`X` carrier. The corrected support sandwich is
assembled in the next module.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The literal existential prime-factor predicate defining the source
indicator `1_R(n)`. -/
def typeIIOriginalRegionPredicate {ell : Nat}
    (region : Set (Fin ell -> Real)) (n : Nat) : Prop :=
  ∃ p : Fin ell -> Nat,
    (forall i, (p i).Prime) ∧
      primeTupleProduct p = n ∧
        (fun i => normalizedPrimeLog n (p i)) ∈ region

/-- The finite source-region product support below `X`. -/
noncomputable def typeIIOriginalRegionSupport (X : Nat) {ell : Nat}
    (region : Set (Fin ell -> Real)) : Finset Nat := by
  classical
  exact (Finset.range X).filter (typeIIOriginalRegionPredicate region)

/-- The strict near-`X` carrier used in Eq. (9.3). -/
noncomputable def typeIINearXCarrier (X : Nat) (delta : Real) : Finset Nat :=
  (Finset.range X).filter fun n =>
    (X : Real) ^ (1 - delta ^ 2) < (n : Real)

/-- The finite union of existential major-arc cell product supports. -/
noncomputable def typeIICubeProductSupportUnion
    (X : Nat) {k : Nat} (delta eta : Real)
    (anchors : Finset (Fin k -> Nat)) : Finset Nat :=
  anchors.biUnion fun anchor =>
    primeTupleProductSupport
      (majorArcPrimeTuples X
        (scaledNaturalCubeAnchor delta anchor) delta eta)

@[simp] theorem mem_typeIIOriginalRegionSupport
    {X ell n : Nat} {region : Set (Fin ell -> Real)} :
    n ∈ typeIIOriginalRegionSupport X region <->
      n < X ∧ typeIIOriginalRegionPredicate region n := by
  classical
  simp [typeIIOriginalRegionSupport]

@[simp] theorem mem_typeIINearXCarrier
    {X n : Nat} {delta : Real} :
    n ∈ typeIINearXCarrier X delta <->
      n < X ∧ (X : Real) ^ (1 - delta ^ 2) < (n : Real) := by
  classical
  simp [typeIINearXCarrier]

@[simp] theorem mem_typeIICubeProductSupportUnion
    {X k n : Nat} {delta eta : Real}
    {anchors : Finset (Fin k -> Nat)} :
    n ∈ typeIICubeProductSupportUnion X delta eta anchors <->
      ∃ anchor ∈ anchors,
        n ∈ primeTupleProductSupport
          (majorArcPrimeTuples X
            (scaledNaturalCubeAnchor delta anchor) delta eta) := by
  classical
  simp [typeIICubeProductSupportUnion]

/-- A coordinate of a tuple of positive naturals is at most its product. -/
theorem primeTupleCoordinate_le_product
    {ell : Nat} {p : Fin ell -> Nat}
    (hp : forall i, 1 <= p i) (i : Fin ell) :
    p i <= primeTupleProduct p := by
  unfold primeTupleProduct
  exact Finset.single_le_prod' (fun j hj => hp j) (Finset.mem_univ i)

/-- A tuple of nonzero naturals has positive product. -/
theorem primeTupleProduct_pos
    {ell : Nat} {p : Fin ell -> Nat} (hp : forall i, p i ≠ 0) :
    0 < primeTupleProduct p := by
  unfold primeTupleProduct
  exact Finset.prod_pos fun i hi => Nat.pos_of_ne_zero (hp i)

/-- The normalized logarithms of a prime tuple with product `n>1` are
positive, at most one, and sum exactly to one. -/
theorem normalizedPrimeLog_product_coordinates
    {ell n : Nat} {p : Fin ell -> Nat}
    (hn : 1 < n) (hprime : forall i, (p i).Prime)
    (hproduct : primeTupleProduct p = n) :
    (∑ i, normalizedPrimeLog n (p i)) = 1 ∧
      forall i, normalizedPrimeLog n (p i) ∈ Set.Ioc (0 : Real) 1 := by
  have hnReal : (1 : Real) < n := by exact_mod_cast hn
  have hsum : (∑ i, normalizedPrimeLog n (p i)) = 1 := by
    rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
      (fun i => (hprime i).ne_zero), hproduct]
    change Real.logb (n : Real) (n : Real) = 1
    exact Real.logb_self_eq_one hnReal
  refine ⟨hsum, ?_⟩
  intro i
  have hpositive : 0 < normalizedPrimeLog n (p i) := by
    unfold normalizedPrimeLog
    exact div_pos (Real.log_pos (by exact_mod_cast (hprime i).one_lt))
      (Real.log_pos hnReal)
  have hnonneg : forall j, 0 <= normalizedPrimeLog n (p j) := fun j => by
    exact (div_pos (Real.log_pos (by exact_mod_cast (hprime j).one_lt))
      (Real.log_pos hnReal)).le
  have hleSum : normalizedPrimeLog n (p i) <=
      ∑ j, normalizedPrimeLog n (p j) :=
    Finset.single_le_sum (fun j hj => hnonneg j) (Finset.mem_univ i)
  exact ⟨hpositive, by simpa only [hsum] using hleSum⟩

/-- Exact change of logarithmic base for positive natural bases. -/
theorem normalizedPrimeLog_base_change
    {X n p : Nat} (hX : 1 < X) (hn : 1 < n) :
    normalizedPrimeLog X p =
      normalizedPrimeLog X n * normalizedPrimeLog n p := by
  have hlogX : Real.log (X : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hX)).ne'
  have hlogn : Real.log (n : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold normalizedPrimeLog
  field_simp

/-- A strict near-`X` product has normalized log strictly between the source
lower ratio and one. -/
theorem normalizedPrimeLog_near_bounds
    {X n : Nat} {delta : Real} (hX : 1 < X)
    (hnear : (X : Real) ^ (1 - delta ^ 2) < (n : Real))
    (hnX : n < X) :
    1 - delta ^ 2 < normalizedPrimeLog X n ∧
      normalizedPrimeLog X n < 1 := by
  have hXReal : (1 : Real) < X := by exact_mod_cast hX
  have hnReal : (0 : Real) < n :=
    (Real.rpow_pos_of_pos (by positivity : (0 : Real) < X) _).trans hnear
  constructor
  · change 1 - delta ^ 2 < Real.logb (X : Real) (n : Real)
    exact (Real.lt_logb_iff_rpow_lt hXReal hnReal).2 hnear
  · change Real.logb (X : Real) (n : Real) < 1
    rw [← Real.logb_self_eq_one hXReal]
    exact (Real.logb_lt_logb_iff hXReal hnReal (by positivity)).2 <| by
      exact_mod_cast hnX

/-- The strict near carrier contains only integers greater than one at the
accepted positive small width. -/
theorem one_lt_of_mem_typeIINearXCarrier
    {X n : Nat} {delta : Real} (hX : 1 < X)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= 1 / 2)
    (hn : n ∈ typeIINearXCarrier X delta) :
    1 < n := by
  have hexponent : 0 < 1 - delta ^ 2 := by nlinarith [sq_nonneg delta]
  have hXReal : (1 : Real) < X := by exact_mod_cast hX
  have hrpow : (1 : Real) < (X : Real) ^ (1 - delta ^ 2) :=
    Real.one_lt_rpow hXReal hexponent
  exact_mod_cast hrpow.trans (mem_typeIINearXCarrier.mp hn).2

/-- Scaling a unit-interval coordinate by a near-one factor sends a
one-width half-open cell into the doubled cell. -/
theorem mem_doubled_Ioc_of_near_scale
    {a delta t e : Real} (hdelta : 0 < delta)
    (hdeltaHalf : delta <= 1 / 2)
    (htLower : 1 - delta ^ 2 < t) (htUpper : t < 1)
    (he : e ∈ Set.Ioc (0 : Real) 1)
    (hz : t * e ∈ Set.Ioc a (a + delta)) :
    e ∈ Set.Ioc a (a + 2 * delta) := by
  have htNonneg : 0 <= t := by nlinarith [sq_nonneg delta]
  have hzLe : t * e <= e := by
    nlinarith [mul_nonneg he.1.le (sub_nonneg.mpr htUpper.le)]
  have honeMinus : 0 <= 1 - t := sub_nonneg.mpr htUpper.le
  have herrBound : (1 - t) * e < delta ^ 2 := by
    have hmul : (1 - t) * e <= (1 - t) * 1 :=
      mul_le_mul_of_nonneg_left he.2 honeMinus
    nlinarith
  have hdeltaSq : delta ^ 2 <= delta := by
    nlinarith [sq_nonneg delta]
  constructor
  · exact hz.1.trans_le hzLe
  · have heq : e = t * e + (1 - t) * e := by ring
    have herr : (1 - t) * e < delta := herrBound.trans_le hdeltaSq
    have hstrict : e < a + 2 * delta := by linarith [heq, herr, hz.2]
    exact hstrict.le

/-- A cell coordinate normalized by `log X` lies in the doubled cell after
normalization by the near product. -/
theorem normalizedPrimeLog_mem_doubled_Ioc_of_near
    {X n p : Nat} {a delta : Real}
    (hX : 1 < X) (hdelta : 0 < delta)
    (hdeltaHalf : delta <= 1 / 2)
    (hnear : n ∈ typeIINearXCarrier X delta)
    (hp : p.Prime) (hpLe : p <= n)
    (hcell : normalizedPrimeLog X p ∈ Set.Ioc a (a + delta)) :
    normalizedPrimeLog n p ∈ Set.Ioc a (a + 2 * delta) := by
  have hn : 1 < n :=
    one_lt_of_mem_typeIINearXCarrier hX hdelta hdeltaHalf hnear
  have hePositive : 0 < normalizedPrimeLog n p := by
    unfold normalizedPrimeLog
    exact div_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
      (Real.log_pos (by exact_mod_cast hn))
  have heUpper : normalizedPrimeLog n p <= 1 := by
    unfold normalizedPrimeLog
    have hlogn : 0 < Real.log (n : Real) :=
      Real.log_pos (by exact_mod_cast hn)
    apply (div_le_iff₀ hlogn).2
    simpa only [one_mul] using Real.log_le_log
      (by exact_mod_cast hp.pos : (0 : Real) < p) (by exact_mod_cast hpLe)
  have hratio := normalizedPrimeLog_near_bounds hX
    (mem_typeIINearXCarrier.mp hnear).2
    (mem_typeIINearXCarrier.mp hnear).1
  have hbase := normalizedPrimeLog_base_change (p := p) hX hn
  rw [hbase] at hcell
  exact mem_doubled_Ioc_of_near_scale hdelta hdeltaHalf
    hratio.1 hratio.2 ⟨hePositive, heUpper⟩ hcell

/-- Weakly increasing prime tuples with equal products agree, including when
prime factors repeat. -/
theorem eq_of_monotone_primeTupleProduct_eq
    {ell : Nat} {p q : Fin ell -> Nat}
    (hpprime : forall i, (p i).Prime)
    (hqprime : forall i, (q i).Prime)
    (hpmono : Monotone p) (hqmono : Monotone q)
    (hproduct : primeTupleProduct p = primeTupleProduct q) :
    p = q := by
  apply List.ofFn_injective
  apply (perm_of_prod_eq_prod (by
    simpa only [List.prod_ofFn, primeTupleProduct] using hproduct) (by
      simpa only [List.forall_mem_ofFn_iff] using
        fun i => (hpprime i).prime) (by
      simpa only [List.forall_mem_ofFn_iff] using
        fun i => (hqprime i).prime)).eq_of_sortedLE
  · exact hpmono.sortedLE_ofFn
  · exact hqmono.sortedLE_ofFn

/-- Source-region membership forces the witnessing prime tuple to be weakly
increasing. -/
theorem monotone_primeTuple_of_mem_typeIISourceRegion
    {ell n : Nat} {eta : Real} {region : Set (Fin ell -> Real)}
    {p : Fin ell -> Nat} (hn : 1 < n)
    (hprime : forall i, (p i).Prime)
    (hregion : IsTypeIISourceRegion eta region)
    (hpRegion : (fun i => normalizedPrimeLog n (p i)) ∈ region) :
    Monotone p := by
  have hmono := (hregion hpRegion).2.1
  intro i j hij
  by_contra hpj
  have hjpi : p j < p i := Nat.lt_of_not_ge hpj
  have hnReal : (1 : Real) < n := by exact_mod_cast hn
  have hpiReal : (0 : Real) < p i := by exact_mod_cast (hprime i).pos
  have hpjReal : (0 : Real) < p j := by exact_mod_cast (hprime j).pos
  have hlog : normalizedPrimeLog n (p j) <
      normalizedPrimeLog n (p i) := by
    change Real.logb (n : Real) (p j : Real) <
      Real.logb (n : Real) (p i : Real)
    exact (Real.logb_lt_logb_iff hnReal hpjReal hpiReal).2 <| by
      exact_mod_cast hjpi
  exact (not_lt_of_ge (hmono hij)) hlog

end

end PrimesRestrictedDigits
