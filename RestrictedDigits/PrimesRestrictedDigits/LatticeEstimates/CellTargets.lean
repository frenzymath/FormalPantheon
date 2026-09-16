import PrimesRestrictedDigits.LatticeEstimates.FinalSOne
import PrimesRestrictedDigits.LatticeEstimates.HybridTerm

/-!
# Weighted target carriers for fixed Lemma 14.3 cells

The standard carrier expands one diagonal `q'` contribution to `S1*S2`. The exceptional
carrier expands one contribution to `S1*S3`. Their explicit hybrid terms are the targets of
the injective selected-pair maps.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- One explicit summand of `S1At` at a fixed `q'`. -/
abbrev LatticeSOneCellTerm
    (length d Q G E : Nat)
    (q : {q // q ∈ hybridResidualSourceDenominators Q}) :=
  Σ g : {g // g ∈ hybridResidualSourceDenominators G},
    LatticeHybridTerm length E ((q.val * d) * g.val)

def latticeSOneCellTermWeight
    (digit : Fin 10) (length d Q G E : Nat)
    (q : {q // q ∈ hybridResidualSourceDenominators Q})
    (term : LatticeSOneCellTerm length d Q G E q) : Real :=
  latticeHybridTermWeight digit length E ((q.val * d) * term.1.val) term.2

private theorem sum_latticeSOneCellTermWeight
    (digit : Fin 10) (length d Q G E : Nat)
    (q : {q // q ∈ hybridResidualSourceDenominators Q}) :
    (∑ term : LatticeSOneCellTerm length d Q G E q,
      latticeSOneCellTermWeight digit length d Q G E q term) =
        latticeSOneAt digit length d q.val G E := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ g : {g // g ∈ hybridResidualSourceDenominators G},
      ∑ term : LatticeHybridTerm length E ((q.val * d) * g.val),
        latticeHybridTermWeight digit length E ((q.val * d) * g.val) term) =
        ∑ g : {g // g ∈ hybridResidualSourceDenominators G},
          latticeHybridDenominatorWeight digit length E ((q.val * d) * g.val) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [sum_latticeHybridTermWeight]
    _ = latticeSOneAt digit length d q.val G E := by
      unfold latticeSOneAt
      exact (Finset.sum_subtype (M := Real)
        (hybridResidualSourceDenominators G) (fun _ => Iff.rfl)
        (fun g : Nat => latticeHybridDenominatorWeight digit length E
          ((q.val * d) * g))).symm

/-- One explicit summand of the `S2` sum at a fixed `q'`. -/
abbrev LatticeSTwoCellTerm
    (length d Q G E : Nat)
    (q : {q // q ∈ hybridResidualSourceDenominators Q}) :=
  Σ g : {g // g ∈ latticeFactorTenBand G},
    LatticeHybridTerm length E (d * (q.val * g.val))

def latticeSTwoCellTermWeight
    (digit : Fin 10) (length d Q G E : Nat)
    (q : {q // q ∈ hybridResidualSourceDenominators Q})
    (term : LatticeSTwoCellTerm length d Q G E q) : Real :=
  latticeHybridTermWeight digit length E (d * (q.val * term.1.val)) term.2

private theorem sum_latticeSTwoCellTermWeight
    (digit : Fin 10) (length d Q G E : Nat)
    (q : {q // q ∈ hybridResidualSourceDenominators Q}) :
    (∑ term : LatticeSTwoCellTerm length d Q G E q,
      latticeSTwoCellTermWeight digit length d Q G E q term) =
      ∑ g : {g // g ∈ latticeFactorTenBand G},
        latticeHybridDenominatorWeight digit length E (d * (q.val * g.val)) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g hg
  change (∑ term : LatticeHybridTerm length E (d * (q.val * g.val)),
      latticeHybridTermWeight digit length E (d * (q.val * g.val)) term) = _
  rw [sum_latticeHybridTermWeight]

private theorem sum_latticeSTwoCellTermWeight_all
    (digit : Fin 10) (length d Q G E : Nat) :
    (∑ q : {q // q ∈ hybridResidualSourceDenominators Q},
      ∑ term : LatticeSTwoCellTerm length d Q G E q,
        latticeSTwoCellTermWeight digit length d Q G E q term) =
        latticeSTwo digit length d Q G E := by
  classical
  calc
    (∑ q : {q // q ∈ hybridResidualSourceDenominators Q},
      ∑ term : LatticeSTwoCellTerm length d Q G E q,
        latticeSTwoCellTermWeight digit length d Q G E q term) =
        ∑ q : {q // q ∈ hybridResidualSourceDenominators Q},
          ∑ g : {g // g ∈ latticeFactorTenBand G},
            latticeHybridDenominatorWeight digit length E
              (d * (q.val * g.val)) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_latticeSTwoCellTermWeight]
    _ = ∑ q ∈ hybridResidualSourceDenominators Q,
        ∑ g ∈ latticeFactorTenBand G,
          latticeHybridDenominatorWeight digit length E (d * (q * g)) := by
      calc
        (∑ q : {q // q ∈ hybridResidualSourceDenominators Q},
          ∑ g : {g // g ∈ latticeFactorTenBand G},
            latticeHybridDenominatorWeight digit length E
              (d * (q.val * g.val))) =
            ∑ q ∈ hybridResidualSourceDenominators Q,
              ∑ g : {g // g ∈ latticeFactorTenBand G},
                latticeHybridDenominatorWeight digit length E
                  (d * (q * g.val)) := by
          exact (Finset.sum_subtype (M := Real)
            (hybridResidualSourceDenominators Q) (fun _ => Iff.rfl)
            (fun q : Nat =>
              ∑ g : {g // g ∈ latticeFactorTenBand G},
                latticeHybridDenominatorWeight digit length E
                  (d * (q * g.val)))).symm
        _ = ∑ q ∈ hybridResidualSourceDenominators Q,
            ∑ g ∈ latticeFactorTenBand G,
              latticeHybridDenominatorWeight digit length E (d * (q * g)) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact (Finset.sum_subtype (M := Real) (latticeFactorTenBand G)
            (fun _ => Iff.rfl)
            (fun g : Nat => latticeHybridDenominatorWeight digit length E
              (d * (q * g)))).symm
    _ = latticeSTwo digit length d Q G E := by
      unfold latticeSTwo
      exact (Finset.sum_product (hybridResidualSourceDenominators Q)
        (latticeFactorTenBand G)
        (fun x : Nat × Nat =>
          latticeHybridDenominatorWeight digit length E
            (d * (x.1 * x.2)))).symm

/-- The weighted target for the fixed-cell standard reindexing. -/
abbrev LatticeStandardCellTarget
    (length d0 d1 Q1 G1 G2 E : Nat) :=
  Σ q : {q // q ∈ hybridResidualSourceDenominators Q1},
    LatticeSOneCellTerm length (d0 * d1) Q1 G1 E q ×
      LatticeSTwoCellTerm length d0 Q1 G2 E q

def latticeStandardCellTargetWeight
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat)
    (target : LatticeStandardCellTarget length d0 d1 Q1 G1 G2 E) : Real :=
  latticeSOneCellTermWeight digit length (d0 * d1) Q1 G1 E
      target.1 target.2.1 *
    latticeSTwoCellTermWeight digit length d0 Q1 G2 E target.1 target.2.2

theorem latticeStandardCellTargetWeight_nonneg
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat)
    (target : LatticeStandardCellTarget length d0 d1 Q1 G1 G2 E) :
    0 <= latticeStandardCellTargetWeight digit length d0 d1 Q1 G1 G2 E
      target := by
  unfold latticeStandardCellTargetWeight latticeSOneCellTermWeight
    latticeSTwoCellTermWeight
  exact mul_nonneg
    (latticeHybridTermWeight_nonneg digit length E _ target.2.1.2)
    (latticeHybridTermWeight_nonneg digit length E _ target.2.2.2)

/-- The first aligned grid integer stored in a standard target. -/
def LatticeStandardCellTarget.firstGrid
    {length d0 d1 Q1 G1 G2 E : Nat}
    (target : LatticeStandardCellTarget length d0 d1 Q1 G1 G2 E) : Int :=
  target.2.2.2.2.val

/-- The second aligned grid integer stored in a standard target. -/
def LatticeStandardCellTarget.secondGrid
    {length d0 d1 Q1 G1 G2 E : Nat}
    (target : LatticeStandardCellTarget length d0 d1 Q1 G1 G2 E) : Int :=
  target.2.1.2.2.val

private theorem sum_standardTarget_at
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat)
    (q : {q // q ∈ hybridResidualSourceDenominators Q1}) :
    (∑ target :
        LatticeSOneCellTerm length (d0 * d1) Q1 G1 E q ×
          LatticeSTwoCellTerm length d0 Q1 G2 E q,
      latticeStandardCellTargetWeight digit length d0 d1 Q1 G1 G2 E
        ⟨q, target⟩) =
      latticeSOneAt digit length (d0 * d1) q.val G1 E *
        (∑ term : LatticeSTwoCellTerm length d0 Q1 G2 E q,
          latticeSTwoCellTermWeight digit length d0 Q1 G2 E q term) := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ first : LatticeSOneCellTerm length (d0 * d1) Q1 G1 E q,
      ∑ second : LatticeSTwoCellTerm length d0 Q1 G2 E q,
        latticeSOneCellTermWeight digit length (d0 * d1) Q1 G1 E q first *
          latticeSTwoCellTermWeight digit length d0 Q1 G2 E q second) =
        ∑ first : LatticeSOneCellTerm length (d0 * d1) Q1 G1 E q,
          latticeSOneCellTermWeight digit length (d0 * d1) Q1 G1 E q first *
            (∑ second : LatticeSTwoCellTerm length d0 Q1 G2 E q,
              latticeSTwoCellTermWeight digit length d0 Q1 G2 E q second) := by
      apply Finset.sum_congr rfl
      intro first hfirst
      rw [Finset.mul_sum]
    _ = (∑ first : LatticeSOneCellTerm length (d0 * d1) Q1 G1 E q,
          latticeSOneCellTermWeight digit length (d0 * d1) Q1 G1 E q first) *
        (∑ second : LatticeSTwoCellTerm length d0 Q1 G2 E q,
          latticeSTwoCellTermWeight digit length d0 Q1 G2 E q second) := by
      rw [Finset.sum_mul]
    _ = latticeSOneAt digit length (d0 * d1) q.val G1 E *
        (∑ second : LatticeSTwoCellTerm length d0 Q1 G2 E q,
          latticeSTwoCellTermWeight digit length d0 Q1 G2 E q second) := by
      rw [sum_latticeSOneCellTermWeight]

/-- The full standard target is bounded by the corrected standard product. -/
theorem sum_latticeStandardCellTargetWeight_le
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat) :
    (∑ target : LatticeStandardCellTarget length d0 d1 Q1 G1 G2 E,
      latticeStandardCellTargetWeight digit length d0 d1 Q1 G1 G2 E target) <=
        latticeSOne digit length (d0 * d1) Q1 G1 E *
          latticeSTwo digit length d0 Q1 G2 E := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ q : {q // q ∈ hybridResidualSourceDenominators Q1},
      ∑ target :
          LatticeSOneCellTerm length (d0 * d1) Q1 G1 E q ×
            LatticeSTwoCellTerm length d0 Q1 G2 E q,
        latticeStandardCellTargetWeight digit length d0 d1 Q1 G1 G2 E
          ⟨q, target⟩) =
        ∑ q : {q // q ∈ hybridResidualSourceDenominators Q1},
          latticeSOneAt digit length (d0 * d1) q.val G1 E *
            (∑ term : LatticeSTwoCellTerm length d0 Q1 G2 E q,
              latticeSTwoCellTermWeight digit length d0 Q1 G2 E q term) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_standardTarget_at]
    _ <= ∑ q : {q // q ∈ hybridResidualSourceDenominators Q1},
        latticeSOne digit length (d0 * d1) Q1 G1 E *
          (∑ term : LatticeSTwoCellTerm length d0 Q1 G2 E q,
            latticeSTwoCellTermWeight digit length d0 Q1 G2 E q term) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right
      · exact latticeSOneAt_le_latticeSOne digit length (d0 * d1) Q1 G1 E
          q.val q.property
      · exact Finset.sum_nonneg fun term _ =>
          latticeHybridTermWeight_nonneg digit length E _ term.2
    _ = latticeSOne digit length (d0 * d1) Q1 G1 E *
        (∑ q : {q // q ∈ hybridResidualSourceDenominators Q1},
          ∑ term : LatticeSTwoCellTerm length d0 Q1 G2 E q,
            latticeSTwoCellTermWeight digit length d0 Q1 G2 E q term) := by
      rw [Finset.mul_sum]
    _ = latticeSOne digit length (d0 * d1) Q1 G1 E *
        latticeSTwo digit length d0 Q1 G2 E := by
      rw [sum_latticeSTwoCellTermWeight_all]

/-- Denominators which occur in the approximation count and also satisfy the
coprime-to-ten restriction required by `S1At`. -/
abbrev LatticeExceptionalCellDenominator
    (length : Nat) (a : Fin (10 ^ length)) (d Q G E : Nat) :=
  {q : {q // q ∈ latticeApproximationDenominators length a d Q G E} //
    q.val ∈ hybridResidualSourceDenominators Q}

/-- The weighted target for the fixed-cell exceptional reindexing. -/
abbrev LatticeExceptionalCellTarget
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat) :=
  Σ a : {a // a ∈ genericExceptionalFrequencies digit length},
    Σ q : LatticeExceptionalCellDenominator length a.val d0 Q1 G2 E,
      LatticeSOneCellTerm length (d0 * d1) Q1 G1 E
        ⟨q.val.val, q.property⟩

def latticeExceptionalCellTargetWeight
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat)
    (target : LatticeExceptionalCellTarget digit length d0 d1 Q1 G1 G2 E) : Real :=
  normalizedPaddedDigitFourierMagnitudeAt digit length
    ((target.1.val.val : Real) / ((10 ^ length : Nat) : Real)) *
    latticeSOneCellTermWeight digit length (d0 * d1) Q1 G1 E
      ⟨target.2.1.val.val, target.2.1.property⟩
      target.2.2

theorem latticeExceptionalCellTargetWeight_nonneg
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat)
    (target : LatticeExceptionalCellTarget digit length d0 d1 Q1 G1 G2 E) :
    0 <= latticeExceptionalCellTargetWeight digit length d0 d1 Q1 G1 G2 E
      target := by
  unfold latticeExceptionalCellTargetWeight latticeSOneCellTermWeight
  exact mul_nonneg
    (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)
    (latticeHybridTermWeight_nonneg digit length E _ target.2.2.2)

def LatticeExceptionalCellTarget.secondGrid
    {digit : Fin 10} {length d0 d1 Q1 G1 G2 E : Nat}
    (target : LatticeExceptionalCellTarget digit length d0 d1 Q1 G1 G2 E) : Int :=
  target.2.2.2.2.val

private theorem sum_exceptionalTarget_at
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat)
    (a : {a // a ∈ genericExceptionalFrequencies digit length}) :
    (∑ target :
        Σ q : LatticeExceptionalCellDenominator length a.val d0 Q1 G2 E,
          LatticeSOneCellTerm length (d0 * d1) Q1 G1 E
            ⟨q.val.val, q.property⟩,
      latticeExceptionalCellTargetWeight digit length d0 d1 Q1 G1 G2 E
        ⟨a, target⟩) <=
      normalizedPaddedDigitFourierMagnitudeAt digit length
          ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
        ((latticeApproximationCount length a.val d0 Q1 G2 E : Real) *
          latticeSOne digit length (d0 * d1) Q1 G1 E) := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ q : LatticeExceptionalCellDenominator length a.val d0 Q1 G2 E,
      ∑ term : LatticeSOneCellTerm length (d0 * d1) Q1 G1 E
          ⟨q.val.val, q.property⟩,
        normalizedPaddedDigitFourierMagnitudeAt digit length
            ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
          latticeSOneCellTermWeight digit length (d0 * d1) Q1 G1 E
            ⟨q.val.val, q.property⟩
            term) =
        ∑ q : LatticeExceptionalCellDenominator length a.val d0 Q1 G2 E,
          normalizedPaddedDigitFourierMagnitudeAt digit length
              ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
            latticeSOneAt digit length (d0 * d1) q.val.val G1 E := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.mul_sum, sum_latticeSOneCellTermWeight]
    _ <= ∑ _q : LatticeExceptionalCellDenominator length a.val d0 Q1 G2 E,
        normalizedPaddedDigitFourierMagnitudeAt digit length
            ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
          latticeSOne digit length (d0 * d1) Q1 G1 E := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (latticeSOneAt_le_latticeSOne digit length (d0 * d1) Q1 G1 E
          q.val.val q.property)
        (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)
    _ <= (Fintype.card
          (LatticeExceptionalCellDenominator length a.val d0 Q1 G2 E) : Real) *
        (normalizedPaddedDigitFourierMagnitudeAt digit length
            ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
          latticeSOne digit length (d0 * d1) Q1 G1 E) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ <= (Fintype.card
          {q // q ∈ latticeApproximationDenominators length a.val d0 Q1 G2 E} :
            Real) *
        (normalizedPaddedDigitFourierMagnitudeAt digit length
            ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
          latticeSOne digit length (d0 * d1) Q1 G1 E) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Fintype.card_subtype_le
          (fun q : {q // q ∈
            latticeApproximationDenominators length a.val d0 Q1 G2 E} =>
              q.val ∈ hybridResidualSourceDenominators Q1)
      · exact mul_nonneg
          (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)
          (latticeSOne_nonneg digit length (d0 * d1) Q1 G1 E)
    _ = normalizedPaddedDigitFourierMagnitudeAt digit length
          ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
        ((latticeApproximationCount length a.val d0 Q1 G2 E : Real) *
          latticeSOne digit length (d0 * d1) Q1 G1 E) := by
      simp only [Fintype.card_coe, latticeApproximationCount]
      ring

/-- The full exceptional target is bounded by the corrected exceptional
product. -/
theorem sum_latticeExceptionalCellTargetWeight_le
    (digit : Fin 10) (length d0 d1 Q1 G1 G2 E : Nat) :
    (∑ target : LatticeExceptionalCellTarget digit length d0 d1 Q1 G1 G2 E,
      latticeExceptionalCellTargetWeight digit length d0 d1 Q1 G1 G2 E target) <=
        latticeSOne digit length (d0 * d1) Q1 G1 E *
          latticeSThree digit length d0 Q1 G2 E := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ a : {a // a ∈ genericExceptionalFrequencies digit length},
      ∑ target :
          Σ q : LatticeExceptionalCellDenominator length a.val d0 Q1 G2 E,
            LatticeSOneCellTerm length (d0 * d1) Q1 G1 E
              ⟨q.val.val, q.property⟩,
        latticeExceptionalCellTargetWeight digit length d0 d1 Q1 G1 G2 E
          ⟨a, target⟩) <=
        ∑ a : {a // a ∈ genericExceptionalFrequencies digit length},
          normalizedPaddedDigitFourierMagnitudeAt digit length
              ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
            ((latticeApproximationCount length a.val d0 Q1 G2 E : Real) *
              latticeSOne digit length (d0 * d1) Q1 G1 E) := by
      exact Finset.sum_le_sum fun a _ =>
        sum_exceptionalTarget_at digit length d0 d1 Q1 G1 G2 E a
    _ = latticeSOne digit length (d0 * d1) Q1 G1 E *
        (∑ a : {a // a ∈ genericExceptionalFrequencies digit length},
          normalizedPaddedDigitFourierMagnitudeAt digit length
              ((a.val.val : Real) / ((10 ^ length : Nat) : Real)) *
            (latticeApproximationCount length a.val d0 Q1 G2 E : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = latticeSOne digit length (d0 * d1) Q1 G1 E *
        latticeSThree digit length d0 Q1 G2 E := by
      unfold latticeSThree
      rw [Finset.sum_subtype (genericExceptionalFrequencies digit length)
        (fun _ => Iff.rfl)]

end

end PrimesRestrictedDigits
