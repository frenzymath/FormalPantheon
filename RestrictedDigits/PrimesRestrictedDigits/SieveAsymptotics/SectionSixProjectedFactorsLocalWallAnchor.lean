import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabCover
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICubeFamily
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearNormalization

/-!
# Locally admissible cells for projected factor walls

This internal support module assigns an exact prime factor tuple on one nonzero projected
affine wall to the margin, room, and convenience cell payload consumed by the existing
support-mass estimate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Assign a complete near-scale prime tuple on a nonzero projected wall to
its exact base-`X` natural-grid slab cell. -/
theorem projectedFactors_exists_crossedWallAnchor
    {delta rho gamma bound : Real} {length N n : Nat}
    {factors : Fin (n + 2) -> Nat}
    {normal : Fin (n + 1) -> Real}
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ i, (factors i).Prime)
    (hproduct : primeTupleProduct factors = N)
    (hlastLower : delta <= normalizedPrimeLog N
      (factors (Fin.last (n + 1))))
    (hnormal : normal ≠ 0)
    (hwall :
      |typeIIAffineValue normal
            (Fin.init (fun i => normalizedPrimeLog N (factors i))) - bound| <=
        gamma) :
    ∃ anchor,
      anchor ∈ typeIIAffineThickSlabAnchors rho gamma normal bound ∧
      factors ∈ majorArcPrimeTuples (10 ^ length)
        (scaledNaturalCubeAnchor rho anchor) rho delta := by
  let X : Nat := 10 ^ length
  let e : Fin (n + 2) -> Real :=
    fun i => normalizedPrimeLog N (factors i)
  let z : Fin (n + 1) -> Real :=
    fun i => normalizedPrimeLog X (factors i.castSucc)
  have hX : 1 < X := by
    dsimp only [X]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hN : 1 < N :=
    one_lt_of_mem_typeIINearXCarrier hX hrho hrhoHalf (by
      simpa only [X] using hnear)
  have hNX : N < X := by
    simpa only [X] using (mem_typeIINearXCarrier.mp hnear).1
  have hpLe (i : Fin (n + 2)) : factors i <= N := by
    rw [← hproduct]
    exact primeTupleCoordinate_le_product (fun q => (hprime q).one_le) i
  have hzPositive : ∀ i, 0 < z i := by
    intro i
    unfold z normalizedPrimeLog
    exact div_pos (Real.log_pos (by exact_mod_cast (hprime i.castSucc).one_lt))
      (Real.log_pos (by exact_mod_cast hX))
  have hsumZ : (∑ i, normalizedPrimeLog X (factors i)) < 1 :=
    sum_normalizedPrimeLog_lt_one_of_product_lt hX hprime (by
      rw [hproduct]
      exact hNX)
  have hzOne : ∀ i, z i <= 1 := by
    intro i
    have hnonneg : ∀ q, 0 <= normalizedPrimeLog X (factors q) := fun q => by
      unfold normalizedPrimeLog
      exact div_nonneg (Real.log_natCast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast hX.le))
    have hsingle : normalizedPrimeLog X (factors i.castSucc) <=
        ∑ q, normalizedPrimeLog X (factors q) :=
      Finset.single_le_sum (fun q _ => hnonneg q) (Finset.mem_univ i.castSucc)
    exact hsingle.trans hsumZ.le
  obtain ⟨anchor, ⟨hgrid, hzCell⟩, _⟩ :=
    existsUnique_typeIINaturalCubeGrid_anchor hrho hzPositive hzOne
  have hePrefixCube : Fin.init e ∈ typeIIDoubledProjectedCube rho anchor := by
    intro i
    have hcell : normalizedPrimeLog X (factors i.castSucc) ∈
        Set.Ioc (scaledNaturalCubeAnchor rho anchor i)
          (scaledNaturalCubeAnchor rho anchor i + rho) := by
      simpa only [z] using hzCell i
    simpa only [e, Fin.init_def, X] using
      normalizedPrimeLog_mem_doubled_Ioc_of_near hX hrho hrhoHalf
        (by simpa only [X] using hnear) (hprime i.castSucc)
        (hpLe i.castSucc) hcell
  have hslab : anchor ∈
      typeIIAffineThickSlabAnchors rho gamma normal bound := by
    rw [mem_typeIIAffineThickSlabAnchors]
    refine ⟨hgrid, hnormal, ?_⟩
    have hdistance :=
      abs_typeIIAffineValue_scaled_sub_le_of_mem_doubledProjectedCube
        hrho.le (normal := normal) hePrefixCube
    calc
      |typeIIAffineValue normal (scaledNaturalCubeAnchor rho anchor) - bound| <=
          |typeIIAffineValue normal (scaledNaturalCubeAnchor rho anchor) -
              typeIIAffineValue normal (Fin.init e)| +
            |typeIIAffineValue normal (Fin.init e) - bound| :=
        abs_sub_le _ _ _
      _ <= 2 * rho * typeIIAffineNormalMass normal + gamma := by
        apply add_le_add hdistance
        simpa only [e] using hwall
      _ = gamma + 2 * rho * typeIIAffineNormalMass normal := by ring
  have hratio := normalizedPrimeLog_near_bounds hX
    (by simpa only [X] using (mem_typeIINearXCarrier.mp hnear).2) hNX
  have hsumPrefixUpper : (∑ i, z i) <=
      (∑ i, scaledNaturalCubeAnchor rho anchor i) +
        ((n + 1 : Nat) : Real) * rho := by
    calc
      (∑ i, z i) <=
          ∑ i, (scaledNaturalCubeAnchor rho anchor i + rho) := by
        apply Finset.sum_le_sum
        intro i _
        exact (hzCell i).2
      _ = (∑ i, scaledNaturalCubeAnchor rho anchor i) +
          ((n + 1 : Nat) : Real) * rho := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hsumZEq : (∑ i, normalizedPrimeLog X (factors i)) =
      normalizedPrimeLog X N := by
    rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
      (fun i => (hprime i).ne_zero), hproduct]
  have hlastDecomposition :
      (∑ i, z i) + normalizedPrimeLog X
          (factors (Fin.last (n + 1))) = normalizedPrimeLog X N := by
    dsimp only [z]
    exact (Fin.sum_univ_castSucc (fun i =>
      normalizedPrimeLog X (factors i))).symm.trans hsumZEq
  have hrhoSq : rho ^ 2 <= rho := by
    nlinarith [sq_nonneg rho]
  have hlastGeometric :
      1 - (∑ i, scaledNaturalCubeAnchor rho anchor i) -
          (((n + 2 : Nat) : Real) * rho) <=
        normalizedPrimeLog X (factors (Fin.last (n + 1))) := by
    norm_num [Nat.cast_add, Nat.cast_one]
    norm_num [Nat.cast_add] at hsumPrefixUpper
    dsimp only [z] at hsumPrefixUpper hlastDecomposition
    linarith [hratio.1]
  have hratioThreeQuarters : (3 / 4 : Real) <= normalizedPrimeLog X N := by
    have : (3 / 4 : Real) <= 1 - rho ^ 2 := by
      nlinarith [sq_nonneg rho]
    exact this.trans hratio.1.le
  have hlastEta : delta / 4 <=
      normalizedPrimeLog X (factors (Fin.last (n + 1))) := by
    have hbase := normalizedPrimeLog_base_change
      (p := factors (Fin.last (n + 1))) hX hN
    calc
      delta / 4 <= (3 / 4 : Real) * delta := by linarith
      _ <= normalizedPrimeLog X N * delta :=
        mul_le_mul_of_nonneg_right hratioThreeQuarters hdelta.le
      _ <= normalizedPrimeLog X N *
          normalizedPrimeLog N (factors (Fin.last (n + 1))) :=
        mul_le_mul_of_nonneg_left hlastLower (by positivity)
      _ = normalizedPrimeLog X (factors (Fin.last (n + 1))) := hbase.symm
  have hpCell : factors ∈ majorArcPrimeTuples X
      (scaledNaturalCubeAnchor rho anchor) rho delta := by
    rw [mem_majorArcPrimeTuples_iff]
    refine ⟨?_, ?_⟩
    · intro i
      rw [Nat.mem_primesLE]
      exact ⟨(hpLe i).trans hNX.le, hprime i⟩
    · refine ⟨?_, hsumZ.le, max_le hlastEta hlastGeometric⟩
      simpa [projectedLogBox, Fin.init_def, z] using hzCell
  exact ⟨anchor, hslab, by simpa only [X] using hpCell⟩

private theorem oneWidthSubsetSum_bounds
    {k : Nat} {rho : Real} {anchor : Fin k -> Nat}
    {z : Fin k -> Real} (hrho : 0 <= rho)
    (hz : z ∈ projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho)
    (I : Finset (Fin k)) :
    (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) <= ∑ i ∈ I, z i ∧
      (∑ i ∈ I, z i) <=
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (k : Real) * rho := by
  constructor
  · exact Finset.sum_le_sum fun i _ => (hz i).1.le
  · calc
      (∑ i ∈ I, z i) <=
          ∑ i ∈ I, (scaledNaturalCubeAnchor rho anchor i + rho) :=
        Finset.sum_le_sum fun i _ => (hz i).2
      _ = (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (I.card : Real) * rho := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ <= (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (k : Real) * rho := by
        gcongr
        simpa using Finset.card_le_univ I

private theorem sum_prefixIndexSet_eq
    {k : Nat} (positions : Finset (Fin (k + 1)))
    (x : Fin (k + 1) -> Real) (hlast : Fin.last k ∉ positions) :
    (∑ i ∈ typeIIPrefixIndexSet positions, x i.castSucc) =
      ∑ j ∈ positions, x j := by
  rw [typeIIPrefixIndexSet, Finset.sum_filter]
  have hall := Fin.sum_univ_castSucc
    (fun j => if j ∈ positions then x j else 0)
  simp only [hlast, if_false, add_zero] at hall
  rw [← hall]
  have hfilter :=
    (Finset.sum_filter (s := Finset.univ) (fun j => j ∈ positions) x).symm
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hfilter
  exact hfilter

/--
Assign a complete prime tuple on one projected wall to an exact locally admissible cell,
preserving the tuple and its filtered product support.
-/
theorem projectedFactors_exists_locallyAdmissibleWallAnchor
    {epsilon delta rho gamma bound : Real} {length N n : Nat}
    {C : Finset Nat}
    {factors : Fin (n + 2) -> Nat}
    {normal : Fin (n + 1) -> Real}
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((n + 1 : Nat) : Real) * rho) <= epsilon)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ i, (factors i).Prime)
    (hproduct : primeTupleProduct factors = N)
    (hsimplex :
      (fun i => normalizedPrimeLog N (factors i)) ∈
        typeIIExponentSimplex delta)
    (hconvenientPoint :
      ∃ positions : Finset (Fin (n + 2)),
        (∑ q ∈ positions, normalizedPrimeLog N (factors q)) ∈
          Set.Icc (9 / 25 + 2 * epsilon) (17 / 40 - 2 * epsilon))
    (hNC : N ∈ C)
    (hnormal : normal ≠ 0)
    (hwall :
      |typeIIAffineValue normal
            (Fin.init (fun i => normalizedPrimeLog N (factors i))) - bound| <=
        gamma) :
    ∃ anchor,
      anchor ∈ typeIIAffineThickSlabAnchors rho gamma normal bound ∧
      (∀ i, delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ∧
      (∑ i, scaledNaturalCubeAnchor rho anchor i) < 1 - delta / 2 ∧
      (∃ I : Finset (Fin (n + 1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)) ∧
      factors ∈ majorArcPrimeTuples (10 ^ length)
        (scaledNaturalCubeAnchor rho anchor) rho delta ∧
      N ∈
        (primeTupleProductSupport
          (majorArcPrimeTuples (10 ^ length)
            (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
          (fun m => m ∈ C) := by
  let X : Nat := 10 ^ length
  let eN : Fin (n + 2) -> Real :=
    fun i => normalizedPrimeLog N (factors i)
  let eX : Fin (n + 2) -> Real :=
    fun i => normalizedPrimeLog X (factors i)
  have hX : 1 < X := by
    dsimp only [X]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hN : 1 < N :=
    one_lt_of_mem_typeIINearXCarrier hX hrho hrhoHalf (by
      simpa only [X] using hnear)
  have hNX : N < X := by
    simpa only [X] using (mem_typeIINearXCarrier.mp hnear).1
  obtain ⟨anchor, hslab, hcell⟩ :=
    projectedFactors_exists_crossedWallAnchor hlength hdelta hrho
      hrhoHalf hnear hprime hproduct (hsimplex.1 (Fin.last (n + 1)))
      hnormal hwall
  have hpLe (i : Fin (n + 2)) : factors i <= N := by
    rw [← hproduct]
    exact primeTupleCoordinate_le_product (fun q => (hprime q).one_le) i
  have hcellData := mem_majorArcPrimeTuples_iff.mp hcell
  have hzCell : (fun i : Fin (n + 1) => eX i.castSucc) ∈
      projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho := by
    simpa only [eX, X, Fin.init_def] using hcellData.2.1
  have heCell : ∀ i : Fin (n + 1),
      eN i.castSucc ∈ Set.Ioc (scaledNaturalCubeAnchor rho anchor i)
        (scaledNaturalCubeAnchor rho anchor i + 2 * rho) := by
    intro i
    exact normalizedPrimeLog_mem_doubled_Ioc_of_near hX hrho hrhoHalf
      (by simpa only [X] using hnear) (hprime i.castSucc) (hpLe i.castSucc)
      (by simpa only [eX, X] using hzCell i)
  have hmargin : ∀ i : Fin (n + 1),
      delta / 2 <= scaledNaturalCubeAnchor rho anchor i := by
    intro i
    have hiLower := hsimplex.1 i.castSucc
    have hiUpper := (heCell i).2
    dsimp only [eN] at hiUpper
    linarith
  have hanchorPrefix :
      (∑ i, scaledNaturalCubeAnchor rho anchor i) <=
        ∑ i : Fin (n + 1), eN i.castSucc := by
    exact Finset.sum_le_sum fun i _ => (heCell i).1.le
  have hsumDecomposition :
      (∑ i : Fin (n + 1), eN i.castSucc) + eN (Fin.last (n + 1)) = 1 := by
    simpa only [eN] using (Fin.sum_univ_castSucc (fun i =>
      normalizedPrimeLog N (factors i))).symm.trans hsimplex.2.2
  have hroom : (∑ i, scaledNaturalCubeAnchor rho anchor i) <
      1 - delta / 2 := by
    have hlastLower := hsimplex.1 (Fin.last (n + 1))
    dsimp only [eN] at hsumDecomposition
    linarith
  have htransport
      (positions : Finset (Fin (n + 2)))
      (hlast : Fin.last (n + 1) ∉ positions)
      (lower upper : Real)
      (hlower : lower + 2 * epsilon <= ∑ q ∈ positions, eN q)
      (hupper : (∑ q ∈ positions, eN q) <= upper - 2 * epsilon) :
      ∃ I : Finset (Fin (n + 1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
          Set.Icc (lower + epsilon) (upper - epsilon) := by
    let I := typeIIPrefixIndexSet positions
    have hprefixN : (∑ i ∈ I, eN i.castSucc) = ∑ q ∈ positions, eN q := by
      simpa only [I] using sum_prefixIndexSet_eq positions eN hlast
    have hprefixX : (∑ i ∈ I, eX i.castSucc) = ∑ q ∈ positions, eX q := by
      simpa only [I] using sum_prefixIndexSet_eq positions eX hlast
    have hbase :=
      abs_sum_normalizedPrimeLog_sub_sum_normalizedPrimeLog_le_sq_of_near
        hX hN (by simpa only [X] using (mem_typeIINearXCarrier.mp hnear).2)
          hNX hprime hproduct positions
    have hbasePrefix :
        |(∑ i ∈ I, eN i.castSucc) - ∑ i ∈ I, eX i.castSucc| <= rho ^ 2 := by
      rw [hprefixN, hprefixX]
      simpa only [eN, eX, X] using hbase
    have hbaseBounds := abs_le.mp hbasePrefix
    have hmove := oneWidthSubsetSum_bounds hrho.le hzCell I
    have hkRhoNonnegative : 0 <= ((n + 1 : Nat) : Real) * rho :=
      mul_nonneg (by positivity) hrho.le
    refine ⟨I, ?_, ?_⟩ <;> linarith
  obtain ⟨positions, htargetBounds⟩ := hconvenientPoint
  have hconvenient :
      ∃ I : Finset (Fin (n + 1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon) := by
    by_cases hlast : Fin.last (n + 1) ∈ positions
    · let complement : Finset (Fin (n + 2)) := Finset.univ \ positions
      have hlastComplement : Fin.last (n + 1) ∉ complement := by
        simp [complement, hlast]
      have hsumEN : (∑ q, eN q) = 1 := by
        simpa only [eN] using hsimplex.2.2
      have hsumComplement : (∑ q ∈ complement, eN q) =
          1 - ∑ q ∈ positions, eN q := by
        rw [show complement = Finset.univ \ positions by rfl,
          Finset.sum_sdiff_eq_sub (Finset.subset_univ positions)]
        change (∑ q, eN q) - (∑ q ∈ positions, eN q) = _
        rw [hsumEN]
      obtain ⟨I, hI⟩ := htransport complement hlastComplement
        (23 / 40) (16 / 25)
          (by rw [hsumComplement]; linarith [htargetBounds.2])
          (by rw [hsumComplement]; linarith [htargetBounds.1])
      exact ⟨I, Or.inr hI⟩
    · obtain ⟨I, hI⟩ := htransport positions hlast
        (9 / 25) (17 / 40) htargetBounds.1 htargetBounds.2
      exact ⟨I, Or.inl hI⟩
  refine ⟨anchor, hslab, hmargin, hroom, hconvenient, hcell, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨mem_primeTupleProductSupport.mpr ⟨factors, hcell, hproduct⟩, hNC⟩

end


end PrimesRestrictedDigits
