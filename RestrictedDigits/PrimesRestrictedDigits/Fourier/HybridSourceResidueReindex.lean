import PrimesRestrictedDigits.Fourier.HybridDecimalDenominator
import PrimesRestrictedDigits.Fourier.HybridResidueCRT

/-!
# Reduced-residue reindexings for the alternative hybrid bound

The source's first two decimal coordinates are reduced only after their mixed-radix
combination. This file preserves that predicate and composes it with the weighted CRT
equivalences for the denominator factors.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

def HybridMixedRadixReducedPair (d₁ d₂ : Nat) :=
  {x : Fin d₁ × Fin d₂ //
    (lowHighFinEquiv d₁ d₂ x).val.Coprime (d₁ * d₂)}

instance instFintypeHybridMixedRadixReducedPair (d₁ d₂ : Nat) :
    Fintype (HybridMixedRadixReducedPair d₁ d₂) := by
  dsimp [HybridMixedRadixReducedPair]
  infer_instance

noncomputable def hybridMixedRadixReducedPairEquiv (d₁ d₂ : Nat) :
    HybridMixedRadixReducedPair d₁ d₂ ≃ ReducedResidue (d₁ * d₂) :=
  (lowHighFinEquiv d₁ d₂).subtypeEquiv (fun _ => Iff.rfl)

theorem hybridMixedRadixReducedPairEquiv_val (d₁ d₂ : Nat)
    (b : HybridMixedRadixReducedPair d₁ d₂) :
    (hybridMixedRadixReducedPairEquiv d₁ d₂ b).val.val =
      b.val.1.val + d₁ * b.val.2.val := by
  exact lowHighFinEquiv_val d₁ d₂ b.val.1 b.val.2

noncomputable def decimalHybridFirstTwoReducedResidueEquiv
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10) :
    ReducedResidue q ×
        ReducedResidue
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) ≃
      ReducedResidue
        (q *
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))) :=
  weightedReducedResidueEquiv hq
    (Nat.mul_pos (hybridDenominatorFirstFactor_pos hd)
      (hybridDenominatorSecondFactor_pos hd))
    (decimalHybridScale_mul_firstSecond_coprime hdvd hq10)
    (decimalHybridScaleDivThird_mul_coprime hd hdvd hq10)

noncomputable def decimalHybridFirstTwoSourceResidueEquiv
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10) :
    ReducedResidue q ×
        HybridMixedRadixReducedPair
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) ≃
      ReducedResidue
        (q *
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))) :=
  ((Equiv.refl (ReducedResidue q)).prodCongr
      (hybridMixedRadixReducedPairEquiv
        (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
        (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)))).trans
    (decimalHybridFirstTwoReducedResidueEquiv hq hd hdvd hq10)

noncomputable def decimalHybridFirstReducedResidueEquiv
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10) :
    ReducedResidue q ×
        ReducedResidue (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)) ≃
      ReducedResidue
        (q * hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)) :=
  weightedReducedResidueEquiv hq
    (hybridDenominatorFirstFactor_pos hd)
    (decimalHybridEnlargedScale_mul_first_coprime hdvd hq10)
    (decimalHybridEnlargedQuotient_mul_coprime hd hdvd hq10)

theorem sum_decimalHybridFirstTwoSourceResidueEquiv
    {M : Type*} [AddCommMonoid M]
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10)
    (f : ReducedResidue
      (q *
        (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
          hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))) → M) :
    (∑ x, f (decimalHybridFirstTwoSourceResidueEquiv hq hd hdvd hq10 x)) =
      ∑ y, f y := by
  exact (decimalHybridFirstTwoSourceResidueEquiv hq hd hdvd hq10).sum_comp f

theorem sum_decimalHybridFirstReducedResidueEquiv
    {M : Type*} [AddCommMonoid M]
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10)
    (f : ReducedResidue
      (q * hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)) → M) :
    (∑ x, f (decimalHybridFirstReducedResidueEquiv hq hd hdvd hq10 x)) =
      ∑ y, f y := by
  exact (decimalHybridFirstReducedResidueEquiv hq hd hdvd hq10).sum_comp f

theorem decimalHybridFirstTwoSourceResidue_unitAddCircle_eq
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10)
    (a : ReducedResidue q)
    (b : HybridMixedRadixReducedPair
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))) :
    (((decimalHybridFirstTwoSourceResidueEquiv hq hd hdvd hq10 (a, b)).val.val : Real) /
        ((q *
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) : Nat) : Real) :
      UnitAddCircle) =
      ((((10 ^ k * a.val.val : Nat) : Real) / (q : Real)) +
        (((10 ^ k /
          hybridDenominatorThirdFactor d (10 ^ k)) *
            (hybridMixedRadixReducedPairEquiv
              (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
              (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) b).val.val : Nat) : Real) /
          ((hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) : Nat) : Real) :
        UnitAddCircle) := by
  have hphase := weightedCRTResidue_unitAddCircle_eq
    (q := q)
    (d := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
      hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
    (u := 10 ^ k)
    (v := 10 ^ k / hybridDenominatorThirdFactor d (10 ^ k))
    hq
    (Nat.mul_pos (hybridDenominatorFirstFactor_pos hd)
      (hybridDenominatorSecondFactor_pos hd))
    (decimalHybridScale_mul_firstSecond_coprime hdvd hq10)
    (decimalHybridScaleDivThird_mul_coprime hd hdvd hq10)
    a.val
    (hybridMixedRadixReducedPairEquiv
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) b).val
  have hsource :
      (decimalHybridFirstTwoSourceResidueEquiv hq hd hdvd hq10 (a, b)).val.val =
        (decimalHybridFirstTwoReducedResidueEquiv hq hd hdvd hq10
          (a, (hybridMixedRadixReducedPairEquiv
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) b))).val.val := by
    rfl
  have hred :
      (decimalHybridFirstTwoReducedResidueEquiv hq hd hdvd hq10
          (a, (hybridMixedRadixReducedPairEquiv
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) b))).val.val =
        (weightedCRTResidue
          (q := q)
          (d := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
          (u := 10 ^ k)
          (v := 10 ^ k / hybridDenominatorThirdFactor d (10 ^ k))
          hq
          (Nat.mul_pos (hybridDenominatorFirstFactor_pos hd)
            (hybridDenominatorSecondFactor_pos hd))
          (decimalHybridScale_mul_firstSecond_coprime hdvd hq10)
          (decimalHybridScaleDivThird_mul_coprime hd hdvd hq10)
          a.val
          (hybridMixedRadixReducedPairEquiv
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) b).val).val := by
    rfl
  rw [hsource, hred]
  simpa [hybridMixedRadixReducedPairEquiv_val] using hphase

theorem decimalHybridFirstResidue_unitAddCircle_eq
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10)
    (a : ReducedResidue q)
    (b : ReducedResidue (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))) :
    (((decimalHybridFirstReducedResidueEquiv hq hd hdvd hq10 (a, b)).val.val : Real) /
        ((q * hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) : Nat) : Real) :
      UnitAddCircle) =
      (((((10 ^ k * 10 ^ v * a.val.val : Nat) : Real) / (q : Real)) +
        (((((10 ^ k * 10 ^ v) /
          (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorThirdFactor d (10 ^ k))) * b.val.val : Nat) : Real) /
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) : Real)) : UnitAddCircle)) := by
  have hphase := weightedCRTResidue_unitAddCircle_eq
    (q := q)
    (d := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
    (u := 10 ^ k * 10 ^ v)
    (v := (10 ^ k * 10 ^ v) /
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
        hybridDenominatorThirdFactor d (10 ^ k)))
    hq (hybridDenominatorFirstFactor_pos hd)
    (decimalHybridEnlargedScale_mul_first_coprime hdvd hq10)
    (decimalHybridEnlargedQuotient_mul_coprime hd hdvd hq10)
    a.val b.val
  have hsource :
      (decimalHybridFirstReducedResidueEquiv hq hd hdvd hq10 (a, b)).val.val =
        (weightedCRTResidue
          (q := q)
          (d := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
          (u := 10 ^ k * 10 ^ v)
          (v := (10 ^ k * 10 ^ v) /
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
              hybridDenominatorThirdFactor d (10 ^ k)))
          hq (hybridDenominatorFirstFactor_pos hd)
          (decimalHybridEnlargedScale_mul_first_coprime hdvd hq10)
          (decimalHybridEnlargedQuotient_mul_coprime hd hdvd hq10)
          a.val b.val).val := by
    rfl
  rw [hsource]
  exact hphase

end
end PrimesRestrictedDigits
