import PrimesRestrictedDigits.GenericMinorArcs.PrimeL2
import PrimesRestrictedDigits.MajorArcs.Factorization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.List.Prime
import Mathlib.Data.List.Permutation

/-!
# Prime-tuple coefficient bounds

This makes the logarithmic coefficient bound in Lemma 12.1 of
`MAYNARD-PRD-PUBLISHED` explicit. Product fibers of ordered prime tuples have
at most `ell!` elements, so their weights have a uniform logarithmic cap.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Ordered prime tuples whose normalized logarithms lie in a given region.
The coordinatewise cutoff at `X` is exact on every product fiber below `X`. -/
noncomputable def normalizedLogRegionPrimeTuples
    (X : Nat) {ell : Nat} (region : Set (Fin ell -> Real)) :
    Finset (Fin ell -> Nat) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin ell => Nat.primesLE X)).filter fun p =>
    (fun i => normalizedPrimeLog X (p i)) ∈ region

/-- The Eq. (9.1) logarithmic weight on a normalized-log region. -/
noncomputable def normalizedLogRegionWeightAtProduct
    (X : Nat) {ell : Nat} (region : Set (Fin ell -> Real))
    (n : Nat) : Real :=
  primeTupleWeightAtProduct (normalizedLogRegionPrimeTuples X region) n

@[simp] theorem mem_normalizedLogRegionPrimeTuples
    {X ell : Nat} {region : Set (Fin ell -> Real)} {p : Fin ell -> Nat} :
    p ∈ normalizedLogRegionPrimeTuples X region <->
      (∀ i, p i ∈ Nat.primesLE X) ∧
        (fun i => normalizedPrimeLog X (p i)) ∈ region := by
  classical
  simp [normalizedLogRegionPrimeTuples, Fintype.mem_piFinset]

/-- Below `X`, the finite coordinate cutoff gives exactly the source's
ordered prime-tuple product fiber. -/
theorem mem_normalizedLogRegion_productFiber_iff
    {X ell n : Nat} {region : Set (Fin ell -> Real)} {p : Fin ell -> Nat}
    (hn : n < X) :
    p ∈ (normalizedLogRegionPrimeTuples X region).filter
        (fun q => primeTupleProduct q = n) <->
      (∀ i, (p i).Prime) ∧
        (fun i => normalizedPrimeLog X (p i)) ∈ region ∧
          primeTupleProduct p = n := by
  rw [Finset.mem_filter, mem_normalizedLogRegionPrimeTuples]
  constructor
  · rintro ⟨⟨hp, hregion⟩, hproduct⟩
    exact ⟨fun i => Nat.prime_of_mem_primesLE (hp i), hregion, hproduct⟩
  · rintro ⟨hprime, hregion, hproduct⟩
    refine ⟨⟨?_, hregion⟩, hproduct⟩
    intro i
    rw [Nat.mem_primesLE]
    refine ⟨?_, hprime i⟩
    calc
      p i <= primeTupleProduct p :=
        Finset.single_le_prod' (fun j hj => (hprime j).one_le)
          (Finset.mem_univ i)
      _ = n := hproduct
      _ <= X := hn.le

/-- A product fiber of ordered prime `ell`-tuples has at most `ell!`
elements. Repeated primes can only reduce the number of distinct orderings. -/
theorem card_primeTupleProductFiber_le_factorial
    {ell m : Nat} (tuples : Finset (Fin ell -> Nat))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime) :
    (tuples.filter fun p => primeTupleProduct p = m).card <=
      Nat.factorial ell := by
  classical
  let fiber := tuples.filter fun p => primeTupleProduct p = m
  change fiber.card <= Nat.factorial ell
  by_cases hfiber : fiber.Nonempty
  · obtain ⟨p, hp⟩ := hfiber
    let target : Finset (List Nat) := (List.ofFn p).permutations.toFinset
    have hsubset : fiber.image List.ofFn ⊆ target := by
      intro l hl
      rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
      rw [List.mem_toFinset, List.mem_permutations]
      apply perm_of_prod_eq_prod
      · rw [List.prod_ofFn, List.prod_ofFn]
        exact (Finset.mem_filter.mp hq).2.trans
          (Finset.mem_filter.mp hp).2.symm
      · simpa only [List.forall_mem_ofFn_iff] using
          fun i => (hprime q (Finset.mem_filter.mp hq).1 i).prime
      · simpa only [List.forall_mem_ofFn_iff] using
          fun i => (hprime p (Finset.mem_filter.mp hp).1 i).prime
    calc
      fiber.card = (fiber.image List.ofFn).card :=
        (Finset.card_image_of_injective fiber List.ofFn_injective).symm
      _ <= target.card := Finset.card_le_card hsubset
      _ <= (List.ofFn p).permutations.length := by
        simpa only [target] using
          List.toFinset_card_le (List.ofFn p).permutations
      _ = Nat.factorial ell := by simp [List.length_permutations]
  · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfiber
    rw [hempty]
    simp

/-- A prime tuple with product below `X` has logarithmic weight at most
`log(X)^ell`. -/
theorem primeTupleLogWeight_le_log_pow_of_product_lt
    {X ell : Nat} {p : Fin ell -> Nat}
    (hprime : ∀ i, (p i).Prime) (hproduct : primeTupleProduct p < X) :
    primeTupleLogWeight p <= Real.log (X : Real) ^ ell := by
  unfold primeTupleLogWeight
  calc
    (∏ i, Real.log (p i : Real)) <=
        ∏ _i : Fin ell, Real.log (X : Real) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Real.log_natCast_nonneg (p i)
      · intro i hi
        apply Real.log_le_log
        · exact_mod_cast (hprime i).pos
        · exact_mod_cast (Finset.single_le_prod'
            (fun j hj => (hprime j).one_le)
            (Finset.mem_univ i)).trans hproduct.le
    _ = Real.log (X : Real) ^ ell := Fin.prod_const ell _

/-- The explicit pointwise logarithmic bound used in Lemma 12.1, retaining
the multiplicity of arbitrary ordered prime tuples. -/
theorem primeTupleWeightAtProduct_le_factorial_mul_log_pow
    (X m : Nat) {ell : Nat} (tuples : Finset (Fin ell -> Nat))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime) (hmX : m < X) :
    primeTupleWeightAtProduct tuples m <=
      (Nat.factorial ell : Real) * Real.log (X : Real) ^ ell := by
  classical
  let fiber := tuples.filter fun p => primeTupleProduct p = m
  have hcard : fiber.card <= Nat.factorial ell :=
    card_primeTupleProductFiber_le_factorial tuples hprime
  have hX : 1 <= X := by omega
  have hlogX : 0 <= Real.log (X : Real) :=
    Real.log_nonneg (by exact_mod_cast hX)
  unfold primeTupleWeightAtProduct
  change (∑ p ∈ fiber, primeTupleLogWeight p) <= _
  calc
    (∑ p ∈ fiber, primeTupleLogWeight p) <=
        ∑ _p ∈ fiber, Real.log (X : Real) ^ ell := by
      apply Finset.sum_le_sum
      intro p hp
      exact primeTupleLogWeight_le_log_pow_of_product_lt
        (fun i => hprime p (Finset.mem_filter.mp hp).1 i) (by
          rw [(Finset.mem_filter.mp hp).2]
          exact hmX)
    _ = (fiber.card : Real) * Real.log (X : Real) ^ ell := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ <= (Nat.factorial ell : Real) * Real.log (X : Real) ^ ell := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlogX ell)
      exact_mod_cast hcard

/-- The source region weight inherits the factorial logarithmic cap. -/
theorem normalizedLogRegionWeightAtProduct_le_factorial_mul_log_pow
    (X n : Nat) {ell : Nat} (region : Set (Fin ell -> Real)) (hn : n < X) :
    normalizedLogRegionWeightAtProduct X region n <=
      (Nat.factorial ell : Real) * Real.log (X : Real) ^ ell := by
  unfold normalizedLogRegionWeightAtProduct
  apply primeTupleWeightAtProduct_le_factorial_mul_log_pow X n _ _ hn
  intro p hp i
  exact Nat.prime_of_mem_primesLE
    ((mem_normalizedLogRegionPrimeTuples.mp hp).1 i)

/--
with the explicit pointwise cap for any finite ordered prime-tuple carrier.
-/
theorem card_primeTupleWeightLargeFrequencies_le
    (X ell : Nat) (hX : 0 < X)
    (tuples : Finset (Fin ell -> Nat))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime)
    (C : Real) (hC : 0 < C) :
    ((weightedPhaseLargeFrequencies X
      (fun n => (primeTupleWeightAtProduct tuples n : Complex))
      ((X : Real) / (10 * C))).card : Real) <=
      100 * C ^ 2 *
        ((Nat.factorial ell : Real) * Real.log (X : Real) ^ ell) ^ 2 := by
  apply card_weightedPhaseLargeFrequencies_le X hX _ C
    ((Nat.factorial ell : Real) * Real.log (X : Real) ^ ell) hC
  · have hXone : 1 <= X := hX
    exact mul_nonneg (by positivity)
      (pow_nonneg (Real.log_nonneg (by exact_mod_cast hXone)) ell)
  · intro n hn
    rw [Complex.norm_real, Real.norm_of_nonneg
      (primeTupleWeightAtProduct_nonneg tuples n)]
    exact primeTupleWeightAtProduct_le_factorial_mul_log_pow
      X n tuples hprime (Finset.mem_range.mp hn)

/-- The explicit normalized-region form of the prime-side estimate in
Lemma 12.1. -/
theorem card_normalizedLogRegionLargeFrequencies_le
    (X ell : Nat) (hX : 0 < X) (region : Set (Fin ell -> Real))
    (C : Real) (hC : 0 < C) :
    ((weightedPhaseLargeFrequencies X
      (fun n => (normalizedLogRegionWeightAtProduct X region n : Complex))
      ((X : Real) / (10 * C))).card : Real) <=
      100 * C ^ 2 *
        ((Nat.factorial ell : Real) * Real.log (X : Real) ^ ell) ^ 2 := by
  unfold normalizedLogRegionWeightAtProduct
  apply card_primeTupleWeightLargeFrequencies_le X ell hX _ _ C hC
  intro p hp i
  exact Nat.prime_of_mem_primesLE
    ((mem_normalizedLogRegionPrimeTuples.mp hp).1 i)

/-- Under the source arity bound, the factorial and logarithmic power are
uniformly bounded using the natural ceiling of `2 / eta`. -/
theorem factorial_mul_log_pow_le_arityCeil
    {X ell : Nat} {eta : Real} (hX : 4 <= X)
    (hell : (ell : Real) <= 2 / eta) :
    (Nat.factorial ell : Real) * Real.log (X : Real) ^ ell <=
      (Nat.factorial (Nat.ceil (2 / eta)) : Real) *
        Real.log (X : Real) ^ Nat.ceil (2 / eta) := by
  have hellCeil : ell <= Nat.ceil (2 / eta) := by
    exact_mod_cast hell.trans (Nat.le_ceil (2 / eta))
  have hfactorial : (Nat.factorial ell : Real) <=
      Nat.factorial (Nat.ceil (2 / eta)) := by
    exact_mod_cast Nat.monotone_factorial hellCeil
  have hXpos : (0 : Real) < X := by positivity
  have hlog : 1 <= Real.log (X : Real) := by
    exact ((Real.lt_log_iff_exp_lt hXpos).mpr
      (Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 <= X by omega)))).le
  exact mul_le_mul hfactorial (pow_le_pow_right₀ hlog hellCeil)
    (pow_nonneg (Real.log_nonneg
      (by exact_mod_cast (show 1 <= X by omega))) ell)
    (by exact_mod_cast (Nat.zero_le (Nat.factorial (Nat.ceil (2 / eta)))))

/-- The explicit eta-uniform realization of the prime side of Lemma 12.1. -/
theorem card_normalizedLogRegionLargeFrequencies_le_eta
    (X ell : Nat) (hX : 4 <= X) {eta : Real} (_heta : 0 < eta)
    (hell : (ell : Real) <= 2 / eta)
    (region : Set (Fin ell -> Real)) (C : Real) (hC : 0 < C) :
    ((weightedPhaseLargeFrequencies X
      (fun n => (normalizedLogRegionWeightAtProduct X region n : Complex))
      ((X : Real) / (10 * C))).card : Real) <=
      100 * C ^ 2 *
        ((Nat.factorial (Nat.ceil (2 / eta)) : Real) *
          Real.log (X : Real) ^ Nat.ceil (2 / eta)) ^ 2 := by
  have hbase := card_normalizedLogRegionLargeFrequencies_le
    X ell (by omega) region C hC
  have hcap := factorial_mul_log_pow_le_arityCeil hX hell
  have hleft : 0 <=
      (Nat.factorial ell : Real) * Real.log (X : Real) ^ ell := by
    positivity
  have hright : 0 <=
      (Nat.factorial (Nat.ceil (2 / eta)) : Real) *
        Real.log (X : Real) ^ Nat.ceil (2 / eta) := by
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ hleft hright).2 hcap) (by positivity))

/--
The normalized-region carrier agrees definitionally with major-arc carrier at the major-arc
region.
-/
theorem normalizedLogRegionPrimeTuples_majorArcLogRegion
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real) :
    normalizedLogRegionPrimeTuples X (majorArcLogRegion a delta eta) =
      majorArcPrimeTuples X a delta eta := by
  rfl

/-- The corresponding normalized-region and major-arc weights agree. -/
theorem normalizedLogRegionWeight_majorArcLogRegion
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real) (n : Nat) :
    normalizedLogRegionWeightAtProduct X (majorArcLogRegion a delta eta) n =
      majorArcRegionWeightAtProduct X a delta eta n := by
  rfl

end PrimesRestrictedDigits
