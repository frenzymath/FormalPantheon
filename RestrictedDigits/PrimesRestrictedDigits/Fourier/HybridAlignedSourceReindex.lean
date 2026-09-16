import PrimesRestrictedDigits.Fourier.HybridLatticeCarrier
import PrimesRestrictedDigits.Fourier.HybridResidualPrefix
import PrimesRestrictedDigits.Fourier.HybridSourcePhases

/-!
# Original aligned-source reindex for the alternative hybrid bound

This file formalizes the exact reduced-residue reindex in equation (10.11) of
`MAYNARD-PRD-PUBLISHED`, pp. 181--182. The full three-coordinate coprimality condition is
retained. The source phase is identified only modulo one, while the aligned integer carrier
stays centered at its canonical representative.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- Three low-first mixed-radix coordinates subject to the source's single
coprimality condition on their combined value. -/
def HybridMixedRadixReducedTriple (d₁ d₂ d₃ : Nat) :=
  {b : (Fin d₁ × Fin d₂) × Fin d₃ //
    (mixedRadixTripleEquiv d₁ d₂ d₃ b).val.Coprime (d₁ * d₂ * d₃)}

instance instFintypeHybridMixedRadixReducedTriple (d₁ d₂ d₃ : Nat) :
    Fintype (HybridMixedRadixReducedTriple d₁ d₂ d₃) := by
  dsimp [HybridMixedRadixReducedTriple]
  infer_instance

/-- Restrict the full mixed-radix bijection to the combined reduced-residue
predicate. This remains total when one or more radices are zero. -/
noncomputable def hybridMixedRadixReducedTripleEquiv (d₁ d₂ d₃ : Nat) :
    HybridMixedRadixReducedTriple d₁ d₂ d₃ ≃ ReducedResidue (d₁ * d₂ * d₃) :=
  (mixedRadixTripleEquiv d₁ d₂ d₃).subtypeEquiv (fun _ => Iff.rfl)

theorem hybridMixedRadixReducedTripleEquiv_val (d₁ d₂ d₃ : Nat)
    (b : HybridMixedRadixReducedTriple d₁ d₂ d₃) :
    (hybridMixedRadixReducedTripleEquiv d₁ d₂ d₃ b).val.val =
      b.val.1.1.val + d₁ * b.val.1.2.val + d₁ * d₂ * b.val.2.val := by
  exact mixedRadixTripleEquiv_val d₁ d₂ d₃
    b.val.1.1 b.val.1.2 b.val.2

private def reducedResidueCongr {m n : Nat} (h : m = n) :
    ReducedResidue m ≃ ReducedResidue n :=
  Equiv.cast (congrArg ReducedResidue h)

@[simp]
private theorem reducedResidueCongr_val {m n : Nat} (h : m = n)
    (a : ReducedResidue m) :
    (reducedResidueCongr h a).val.val = a.val.val := by
  subst n
  rfl

private noncomputable def decimalHybridMixedRadixReducedTripleEquiv
    (d k v : Nat) :
    HybridMixedRadixReducedTriple
        (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
        (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
        (hybridDenominatorThirdFactor d (10 ^ k)) ≃
      ReducedResidue d :=
  (hybridMixedRadixReducedTripleEquiv
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorThirdFactor d (10 ^ k))).trans
    (reducedResidueCongr
      (hybridDenominatorFirstSecondThird_eq d (10 ^ k) (10 ^ v)))

@[simp]
private theorem decimalHybridMixedRadixReducedTripleEquiv_val
    (d k v : Nat)
    (b : HybridMixedRadixReducedTriple
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorThirdFactor d (10 ^ k))) :
    (decimalHybridMixedRadixReducedTripleEquiv d k v b).val.val =
      b.val.1.1.val +
        hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) * b.val.1.2.val +
        hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
          hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) * b.val.2.val := by
  simp only [decimalHybridMixedRadixReducedTripleEquiv, Equiv.trans_apply,
    reducedResidueCongr_val, hybridMixedRadixReducedTripleEquiv_val]

private theorem decimalHybridMixedRadixReducedTripleEquiv_div_eq
    {d k v : Nat} (hd : 0 < d)
    (b : HybridMixedRadixReducedTriple
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorThirdFactor d (10 ^ k))) :
    ((decimalHybridMixedRadixReducedTripleEquiv d k v b).val.val : Real) /
        (d : Real) =
      (b.val.1.1.val : Real) /
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorThirdFactor d (10 ^ k) : Nat) +
        (b.val.1.2.val : Real) /
          (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorThirdFactor d (10 ^ k) : Nat) +
        (b.val.2.val : Real) /
          (hybridDenominatorThirdFactor d (10 ^ k) : Real) := by
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  have hd₁ : 0 < d₁ := hybridDenominatorFirstFactor_pos hd
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hproduct : d₁ * d₂ * d₃ = d :=
    hybridDenominatorFirstSecondThird_eq d (10 ^ k) (10 ^ v)
  have hproductReal : (d : Real) = ((d₁ * d₂ * d₃ : Nat) : Real) := by
    exact_mod_cast hproduct.symm
  change ((decimalHybridMixedRadixReducedTripleEquiv d k v b).val.val : Real) /
      (d : Real) =
    (b.val.1.1.val : Real) / (d₁ * d₂ * d₃ : Nat) +
      (b.val.1.2.val : Real) / (d₂ * d₃ : Nat) +
      (b.val.2.val : Real) / (d₃ : Real)
  rw [decimalHybridMixedRadixReducedTripleEquiv_val, hproductReal]
  push_cast
  field_simp [show (d₁ : Real) ≠ 0 by exact_mod_cast hd₁.ne',
    show (d₂ : Real) ≠ 0 by exact_mod_cast hd₂.ne',
    show (d₃ : Real) ≠ 0 by exact_mod_cast hd₃.ne']
  ring

/-- The weight-one CRT equivalence that reindexes the complete reduced
residue in equation (10.11) by `a'` and the full decimal triple. -/
noncomputable def decimalHybridFullSourceResidueEquiv
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10) :
    ReducedResidue q ×
        HybridMixedRadixReducedTriple
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorThirdFactor d (10 ^ k)) ≃
      ReducedResidue (q * d) :=
  ((Equiv.refl (ReducedResidue q)).prodCongr
      (decimalHybridMixedRadixReducedTripleEquiv d k v)).trans
    (weightedReducedResidueEquiv (u := 1) (v := 1) hq hd
      (by simpa using (coprime_dvd_pow_ten hq10 hdvd).symm)
      (by simpa using coprime_dvd_pow_ten hq10 hdvd))

theorem sum_decimalHybridFullSourceResidueEquiv
    {M : Type*} [AddCommMonoid M]
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10)
    (f : ReducedResidue (q * d) → M) :
    (∑ x, f (decimalHybridFullSourceResidueEquiv
      (q := q) (d := d) (k := k) (v := v) (u := u)
      hq hd hdvd hq10 x)) =
      ∑ c, f c := by
  exact (decimalHybridFullSourceResidueEquiv
    (q := q) (d := d) (k := k) (v := v) (u := u)
    hq hd hdvd hq10).sum_comp f

/-- The canonical output fraction represents the four-fraction source phase
on the unit additive circle. Real representatives are intentionally not
identified because the source phase can exceed one. -/
theorem decimalHybridFullSourceResidue_unitAddCircle_eq
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10)
    (a : ReducedResidue q)
    (b : HybridMixedRadixReducedTriple
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorThirdFactor d (10 ^ k))) :
    (((decimalHybridFullSourceResidueEquiv
        (q := q) (d := d) (k := k) (v := v) (u := u)
        hq hd hdvd hq10 (a, b)).val.val : Real) /
        ((q * d : Nat) : Real) : UnitAddCircle) =
      ((hybridSourceBetaTwo q
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorThirdFactor d (10 ^ k)) a b.val.1 +
        (b.val.2.val : Real) /
          (hybridDenominatorThirdFactor d (10 ^ k) : Real) : Real) :
        UnitAddCircle) := by
  let triple := decimalHybridMixedRadixReducedTripleEquiv d k v b
  have hcop := coprime_dvd_pow_ten hq10 hdvd
  have hphase := weightedCRTResidue_unitAddCircle_eq
    (q := q) (d := d) (u := 1) (v := 1) hq hd
    (by simpa using hcop.symm) (by simpa using hcop) a.val triple.val
  have hsource :
      (decimalHybridFullSourceResidueEquiv
        (q := q) (d := d) (k := k) (v := v) (u := u)
        hq hd hdvd hq10 (a, b)).val.val =
        (weightedCRTResidue
          (q := q) (d := d) (u := 1) (v := 1) hq hd
          (by simpa using hcop.symm) (by simpa using hcop) a.val triple.val).val := by
    rfl
  rw [hsource]
  calc
    (((weightedCRTResidue
          (q := q) (d := d) (u := 1) (v := 1) hq hd
          (by simpa using hcop.symm) (by simpa using hcop) a.val triple.val).val : Real) /
        ((q * d : Nat) : Real) : UnitAddCircle) =
        ((a.val.val : Real) / (q : Real) +
          (triple.val.val : Real) / (d : Real) : UnitAddCircle) := by
      simpa using hphase
    _ = ((hybridSourceBetaTwo q
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorThirdFactor d (10 ^ k)) a b.val.1 +
        (b.val.2.val : Real) /
          (hybridDenominatorThirdFactor d (10 ^ k) : Real) : Real) :
        UnitAddCircle) := by
      congr 1
      rw [decimalHybridMixedRadixReducedTripleEquiv_div_eq hd b,
        hybridSourceBetaTwo_eq
          (hybridDenominatorFirstFactor_pos hd)
          (hybridDenominatorSecondFactor_pos hd)
          (hybridDenominatorThirdFactor_pos hd)]
      ring

/-- The literal aligned source sum in Lemma 10.7, before block factorization.
The inner center is the canonical reduced fraction in `[0,1)`. -/
noncomputable def decimalHybridAlignedSourceBandSum
    (digit : Fin 10) (length q₁ d Q₂ E : Nat) : Real :=
  ∑ q₂ ∈ hybridResidualSourceDenominators Q₂,
    ∑ c : ReducedResidue ((q₁ * q₂) * d),
      alignedGridSum digit length (E : Real)
        ((c.val.val : Real) / (((q₁ * q₂) * d : Nat) : Real))

private theorem hybridResidualSourceDenominator_pos
    {Q₂ : Nat} (q₂ : {q₂ // q₂ ∈ hybridResidualSourceDenominators Q₂}) :
    0 < q₂.val := by
  exact (mem_hybridResidualSourceDenominators_iff.mp q₂.property).1

private theorem hybridResidualSourceDenominator_coprime_ten
    {Q₂ : Nat} (q₂ : {q₂ // q₂ ∈ hybridResidualSourceDenominators Q₂}) :
    q₂.val.Coprime 10 := by
  exact (mem_hybridResidualSourceDenominators_iff.mp q₂.property).2.2.2

/-- Exact finite reindex of the original source sum by `a'` and the complete
three-coordinate reduced carrier. The aligned center remains canonical; use
`decimalHybridFullSourceResidue_unitAddCircle_eq` for its source phase. -/
theorem decimalHybridAlignedSourceBandSum_eq_reindexed
    (digit : Fin 10) (length q₁ d k v u Q₂ E : Nat)
    (hq₁ : 0 < q₁) (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq₁10 : q₁.Coprime 10) :
    decimalHybridAlignedSourceBandSum digit length q₁ d Q₂ E =
      ∑ q₂ : {q₂ // q₂ ∈ hybridResidualSourceDenominators Q₂},
        ∑ a : ReducedResidue (q₁ * q₂.val),
          ∑ b : HybridMixedRadixReducedTriple
            (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
            (hybridDenominatorThirdFactor d (10 ^ k)),
            alignedGridSum digit length (E : Real)
              (((decimalHybridFullSourceResidueEquiv
                (q := q₁ * q₂.val) (d := d) (k := k) (v := v) (u := u)
                (Nat.mul_pos hq₁ (hybridResidualSourceDenominator_pos q₂))
                hd hdvd
                (hq₁10.mul_left
                  (hybridResidualSourceDenominator_coprime_ten q₂))
                (a, b)).val.val : Real) /
                ((((q₁ * q₂.val) * d : Nat) : Real))) := by
  classical
  rw [decimalHybridAlignedSourceBandSum]
  rw [Finset.sum_subtype (hybridResidualSourceDenominators Q₂)
    (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro q₂ _
  have hq : 0 < q₁ * q₂.val :=
    Nat.mul_pos hq₁ (hybridResidualSourceDenominator_pos q₂)
  have hq10 : (q₁ * q₂.val).Coprime 10 :=
    hq₁10.mul_left (hybridResidualSourceDenominator_coprime_ten q₂)
  have hsum := sum_decimalHybridFullSourceResidueEquiv
    (q := q₁ * q₂.val) (d := d) (k := k) (v := v) (u := u)
    hq hd hdvd hq10
    (fun c => alignedGridSum digit length (E : Real)
      ((c.val.val : Real) / ((((q₁ * q₂.val) * d : Nat) : Real))))
  simpa only [Fintype.sum_prod_type] using hsum.symm

end

end PrimesRestrictedDigits
