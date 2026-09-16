import PrimesRestrictedDigits.LatticeEstimates.DecompositionKey
import PrimesRestrictedDigits.LatticeEstimates.FinalScaleAggregation

/-!
# Generic outer aggregation of fixed scale cells

This finite sigma carrier sums a family of cells over admissible five-scale keys and both
exact decimal-smooth factor bands. It is shared by the two orientation branches of repaired
Lemma 14.3.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

abbrev LatticeScaleAggregationTarget
    (length : Nat) (P : Real) (alpha : Type*) [Fintype alpha]
    (cell : LatticeDecompositionScaleKey length -> Nat -> Nat -> Finset alpha) :=
  Σ key : {key // key ∈ LatticeDecompositionScaleKey.admissibleCarrier length P},
    Σ d0 : {d // d ∈ latticeSmoothFactorTenBand key.val.d0Scale},
      Σ d1 : {d // d ∈ latticeSmoothFactorTenBand key.val.d1Scale},
        {a // a ∈ cell key.val d0.val d1.val}

def latticeScaleAggregationTargetWeight
    {length : Nat} {P : Real} {alpha : Type*} [Fintype alpha]
    {cell : LatticeDecompositionScaleKey length -> Nat -> Nat -> Finset alpha}
    (sourceWeight : alpha -> Real)
    (target : LatticeScaleAggregationTarget length P alpha cell) : Real :=
  sourceWeight target.2.2.2.val

/-- The source element retained by an aggregation target. -/
def latticeScaleAggregationTargetSource
    {length : Nat} {P : Real} {alpha : Type*} [Fintype alpha]
    {cell : LatticeDecompositionScaleKey length -> Nat -> Nat -> Finset alpha}
    (target : LatticeScaleAggregationTarget length P alpha cell) : alpha :=
  target.2.2.2.val

theorem latticeScaleAggregationTargetWeight_nonneg
    {length : Nat} {P : Real} {alpha : Type*} [Fintype alpha]
    {cell : LatticeDecompositionScaleKey length -> Nat -> Nat -> Finset alpha}
    {sourceWeight : alpha -> Real} (hsourceNonneg : ∀ a, 0 <= sourceWeight a)
    (target : LatticeScaleAggregationTarget length P alpha cell) :
    0 <= latticeScaleAggregationTargetWeight sourceWeight target :=
  hsourceNonneg target.2.2.2.val

private theorem sum_smoothMinimum_eq
    (digit : Fin 10) (length : Nat) (P : Real)
    (key : LatticeDecompositionScaleKey length) :
    (∑ d0 : {d // d ∈ latticeSmoothFactorTenBand key.d0Scale},
      ∑ d1 : {d // d ∈ latticeSmoothFactorTenBand key.d1Scale},
        latticeExceptionalProductMinimum digit length d0.val d1.val
          key.qPrimeScale key.g1PrimeScale key.g2Scale (key.errorScale P)) =
      latticeExceptionalSmoothPairSum digit length key.qPrimeScale
        key.g1PrimeScale key.g2Scale key.d0Scale key.d1Scale
          (key.errorScale P) := by
  classical
  unfold latticeExceptionalSmoothPairSum
  calc
    (∑ d0 : {d // d ∈ latticeSmoothFactorTenBand key.d0Scale},
      ∑ d1 : {d // d ∈ latticeSmoothFactorTenBand key.d1Scale},
        latticeExceptionalProductMinimum digit length d0.val d1.val
          key.qPrimeScale key.g1PrimeScale key.g2Scale (key.errorScale P)) =
        ∑ d0 ∈ latticeSmoothFactorTenBand key.d0Scale,
          ∑ d1 : {d // d ∈ latticeSmoothFactorTenBand key.d1Scale},
            latticeExceptionalProductMinimum digit length d0 d1.val
              key.qPrimeScale key.g1PrimeScale key.g2Scale
                (key.errorScale P) := by
      exact (Finset.sum_subtype (M := Real)
        (latticeSmoothFactorTenBand key.d0Scale) (fun _ => Iff.rfl)
        (fun d0 : Nat =>
          ∑ d1 : {d // d ∈ latticeSmoothFactorTenBand key.d1Scale},
            latticeExceptionalProductMinimum digit length d0 d1.val
              key.qPrimeScale key.g1PrimeScale key.g2Scale
                (key.errorScale P))).symm
    _ = ∑ d0 ∈ latticeSmoothFactorTenBand key.d0Scale,
        ∑ d1 ∈ latticeSmoothFactorTenBand key.d1Scale,
          latticeExceptionalProductMinimum digit length d0 d1
            key.qPrimeScale key.g1PrimeScale key.g2Scale
              (key.errorScale P) := by
      apply Finset.sum_congr rfl
      intro d0 hd0
      exact (Finset.sum_subtype (M := Real)
        (latticeSmoothFactorTenBand key.d1Scale) (fun _ => Iff.rfl)
        (fun d1 : Nat =>
          latticeExceptionalProductMinimum digit length d0 d1
            key.qPrimeScale key.g1PrimeScale key.g2Scale
              (key.errorScale P))).symm

/-- A uniform bound for every admissible smooth-pair sum bounds the full
generic aggregation target by the number of admissible keys times that
bound. -/
theorem sum_latticeScaleAggregationTargetWeight_le
    (digit : Fin 10) (length : Nat) (P B : Real)
    (alpha : Type*) [Fintype alpha]
    (cell : LatticeDecompositionScaleKey length -> Nat -> Nat -> Finset alpha)
    (sourceWeight : alpha -> Real)
    (hcell : ∀ key d0 d1,
      d0 ∈ latticeSmoothFactorTenBand key.d0Scale ->
      d1 ∈ latticeSmoothFactorTenBand key.d1Scale ->
      (∑ a ∈ cell key d0 d1, sourceWeight a) <=
        latticeExceptionalProductMinimum digit length d0 d1 key.qPrimeScale
          key.g1PrimeScale key.g2Scale (key.errorScale P))
    (hmajorant : ∀ key,
      key ∈ LatticeDecompositionScaleKey.admissibleCarrier length P ->
      latticeExceptionalSmoothPairSum digit length key.qPrimeScale
        key.g1PrimeScale key.g2Scale key.d0Scale key.d1Scale
          (key.errorScale P) <= B) :
    (∑ target : LatticeScaleAggregationTarget length P alpha cell,
      latticeScaleAggregationTargetWeight sourceWeight target) <=
      (LatticeDecompositionScaleKey.admissibleCarrier length P).card * B := by
  classical
  simp only [Fintype.sum_sigma]
  calc
    (∑ key : {key // key ∈
        LatticeDecompositionScaleKey.admissibleCarrier length P},
      ∑ d0 : {d // d ∈ latticeSmoothFactorTenBand key.val.d0Scale},
        ∑ d1 : {d // d ∈ latticeSmoothFactorTenBand key.val.d1Scale},
          ∑ a : {a // a ∈ cell key.val d0.val d1.val},
            sourceWeight a.val) <=
        ∑ key : {key // key ∈
            LatticeDecompositionScaleKey.admissibleCarrier length P},
          ∑ d0 : {d // d ∈ latticeSmoothFactorTenBand key.val.d0Scale},
            ∑ d1 : {d // d ∈ latticeSmoothFactorTenBand key.val.d1Scale},
              latticeExceptionalProductMinimum digit length d0.val d1.val
                key.val.qPrimeScale key.val.g1PrimeScale key.val.g2Scale
                  (key.val.errorScale P) := by
      apply Finset.sum_le_sum
      intro key hkey
      apply Finset.sum_le_sum
      intro d0 hd0
      apply Finset.sum_le_sum
      intro d1 hd1
      calc
        (∑ a : {a // a ∈ cell key.val d0.val d1.val}, sourceWeight a.val) =
            ∑ a ∈ cell key.val d0.val d1.val, sourceWeight a :=
          (Finset.sum_subtype (cell key.val d0.val d1.val)
            (fun _ => Iff.rfl) sourceWeight).symm
        _ <= latticeExceptionalProductMinimum digit length d0.val d1.val
            key.val.qPrimeScale key.val.g1PrimeScale key.val.g2Scale
              (key.val.errorScale P) :=
          hcell key.val d0.val d1.val d0.property d1.property
    _ = ∑ key : {key // key ∈
        LatticeDecompositionScaleKey.admissibleCarrier length P},
        latticeExceptionalSmoothPairSum digit length key.val.qPrimeScale
          key.val.g1PrimeScale key.val.g2Scale key.val.d0Scale key.val.d1Scale
            (key.val.errorScale P) := by
      apply Finset.sum_congr rfl
      intro key hkey
      rw [sum_smoothMinimum_eq]
    _ <= ∑ _key : {key // key ∈
        LatticeDecompositionScaleKey.admissibleCarrier length P}, B := by
      exact Finset.sum_le_sum fun key _ => hmajorant key.val key.property
    _ = (LatticeDecompositionScaleKey.admissibleCarrier length P).card * B := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]

end

end PrimesRestrictedDigits
