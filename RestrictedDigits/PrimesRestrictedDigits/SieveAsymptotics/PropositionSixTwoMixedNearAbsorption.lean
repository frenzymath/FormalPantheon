import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoNearSignedWeakPieces
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoHalfspaceNearAbsorption

/-!
# Proposition 6.2 mixed near-candidate absorption

This sums the halfspace near-candidate estimate over the exact signed weak pieces of a mixed
affine presentation.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_list_common_threshold
    {alpha : Type*} (items : List alpha) (P : alpha -> Nat -> Prop)
    (hP : forall item, exists threshold : Nat, 1 <= threshold ∧
      forall length : Nat, threshold <= length -> P item length) :
    exists threshold : Nat, 1 <= threshold ∧
      forall item, item ∈ items -> forall length : Nat,
        threshold <= length -> P item length := by
  induction items with
  | nil => exact ⟨1, le_rfl, by simp⟩
  | cons item items ih =>
      obtain ⟨itemThreshold, hitemThreshold, hitem⟩ := hP item
      obtain ⟨itemsThreshold, hitemsThreshold, hitems⟩ := ih
      refine ⟨max itemThreshold itemsThreshold,
        hitemThreshold.trans (le_max_left _ _), ?_⟩
      intro current hcurrent length hlength
      rcases List.mem_cons.mp hcurrent with hEq | hmem
      · subst current
        exact hitem length ((le_max_left _ _).trans hlength)
      · exact hitems current hmem length
          ((le_max_right _ _).trans hlength)

set_option maxHeartbeats 2400000 in
/-- For one direct band, the mixed-region Proposition 6.2 near discrepancy is
eventually absorbed into any positive logarithmic budget. -/
theorem exists_propositionSixTwoMixedNearCandidateDiscrepancy_band_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget)
    {ell : Nat} (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real))
    (presentation : TypeIIAffineMixedPresentation region)
    (band : SectionSixDirectBand) :
    exists length0 : Nat, 1 <= length0 ∧
      forall length, length0 <= length -> forall digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := XNat
        let rho := majorArcM2LogLogDelta XNat
        let A := paddedRestrictedNumbers digit length
        let B := maynardAmbientCarrier X
        let lambda :=
          (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
        abs (((propositionSixTwoNearCandidates epsilon ell I j region length
          band rho A).card : Real) - lambda *
          ((propositionSixTwoNearCandidates epsilon ell I j region length band
            rho B).card : Real)) <=
          budget * (A.card : Real) / Real.log X := by
  let pieces := presentation.signedWeakPieces
  let pieceBudget : Real :=
    budget / (((pieces.length + 1 : Nat) : Real))
  have hpieceBudget : 0 < pieceBudget := by
    dsimp only [pieceBudget]
    positivity
  let PieceBound : TypeIIAffineSignedWeakPiece presentation -> Nat -> Prop :=
    fun piece length =>
      forall digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := XNat
        let rho := majorArcM2LogLogDelta XNat
        let A := paddedRestrictedNumbers digit length
        let B := maynardAmbientCarrier X
        let lambda :=
          (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
        abs (((propositionSixTwoNearCandidates epsilon ell I j piece.region
          length band rho A).card : Real) - lambda *
          ((propositionSixTwoNearCandidates epsilon ell I j piece.region length
            band rho B).card : Real)) <=
          pieceBudget * (A.card : Real) / Real.log X
  have hPieceThreshold : forall piece,
      exists threshold : Nat, 1 <= threshold ∧
        forall length : Nat, threshold <= length -> PieceBound piece length := by
    intro piece
    obtain ⟨threshold, hthreshold, hAt⟩ :=
      exists_propositionSixTwoHalfspaceNearCandidateDiscrepancy_budget_upper
        epsilon hepsilon hepsilonSmall pieceBudget hpieceBudget I j piece.region
          piece.weakPresentation band
    refine ⟨threshold, hthreshold, ?_⟩
    intro length hlength
    simpa only [PieceBound] using hAt length hlength
  obtain ⟨length0, hlength0, hAllPieces⟩ :=
    exists_list_common_threshold pieces PieceBound hPieceThreshold
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A := paddedRestrictedNumbers digit length
  let B := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let mass : Real := (A.card : Real) / Real.log X
  let nearDiscrepancy : Set (Fin ell -> Real) -> Real := fun sourceRegion =>
    ((propositionSixTwoNearCandidates epsilon ell I j sourceRegion length band
      rho A).card : Real) - lambda *
      ((propositionSixTwoNearCandidates epsilon ell I j sourceRegion length
        band rho B).card : Real)
  have hPieceBound (piece : TypeIIAffineSignedWeakPiece presentation)
      (hpiece : piece ∈ pieces) :
      abs (nearDiscrepancy piece.region) <= pieceBudget * mass := by
    have hAt := hAllPieces piece hpiece length hlength
    dsimp only [PieceBound] at hAt
    have hBound := hAt digit
    have hBound' :
        abs (nearDiscrepancy piece.region) <=
          pieceBudget * (A.card : Real) / Real.log X := by
      simpa only [XNat, X, rho, A, B, lambda, nearDiscrepancy] using hBound
    calc
      abs (nearDiscrepancy piece.region) <=
          pieceBudget * (A.card : Real) / Real.log X := hBound'
      _ = pieceBudget * mass := by
        dsimp only [mass]
        ring
  have htriangle :
      abs ((pieces.map fun piece =>
          (piece.coefficient : Real) *
            nearDiscrepancy piece.region).sum) <=
        (pieces.map fun piece =>
          abs (nearDiscrepancy piece.region)).sum := by
    induction pieces with
    | nil => simp
    | cons piece remaining ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          abs ((piece.coefficient : Real) * nearDiscrepancy piece.region +
              (remaining.map fun current =>
                (current.coefficient : Real) *
                  nearDiscrepancy current.region).sum) <=
              abs ((piece.coefficient : Real) *
                nearDiscrepancy piece.region) +
                abs ((remaining.map fun current =>
                  (current.coefficient : Real) *
                    nearDiscrepancy current.region).sum) := abs_add_le _ _
          _ <= abs ((piece.coefficient : Real) *
                nearDiscrepancy piece.region) +
              (remaining.map fun current =>
                abs (nearDiscrepancy current.region)).sum := by gcongr
          _ = abs (nearDiscrepancy piece.region) +
              (remaining.map fun current =>
                abs (nearDiscrepancy current.region)).sum := by
            rw [abs_mul]
            simp [TypeIIAffineSignedWeakPiece.coefficient]
  have hsum :
      (pieces.map fun piece =>
          abs (nearDiscrepancy piece.region)).sum <=
        (pieces.map fun _ => pieceBudget * mass).sum :=
    List.sum_le_sum hPieceBound
  have hfactor :
      (pieces.map fun _ => pieceBudget * mass).sum =
        (pieces.length : Real) * pieceBudget * mass := by
    induction pieces with
    | nil => simp
    | cons piece remaining ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          Nat.cast_add, Nat.cast_one]
        rw [ih]
        ring
  have hdenominator :
      0 < (((pieces.length + 1 : Nat) : Real)) := by positivity
  have hscalar : (pieces.length : Real) * pieceBudget <= budget := by
    dsimp only [pieceBudget]
    rw [show (pieces.length : Real) *
        (budget / ((pieces.length + 1 : Nat) : Real)) =
          ((pieces.length : Real) * budget) /
            ((pieces.length + 1 : Nat) : Real) by ring]
    apply (div_le_iff₀ hdenominator).2
    have hcount : (pieces.length : Real) <=
        ((pieces.length + 1 : Nat) : Real) := by
      exact_mod_cast Nat.le_succ pieces.length
    calc
      (pieces.length : Real) * budget <=
          ((pieces.length + 1 : Nat) : Real) * budget :=
        mul_le_mul_of_nonneg_right hcount hbudget.le
      _ = budget * ((pieces.length + 1 : Nat) : Real) := by ring
  have hlengthOne : 1 <= length := hlength0.trans hlength
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hmass : 0 <= mass := by
    dsimp only [mass]
    positivity
  have hsigned :
      nearDiscrepancy region =
        (pieces.map fun piece =>
          (piece.coefficient : Real) *
            nearDiscrepancy piece.region).sum := by
    simpa only [XNat, X, A, B, lambda, nearDiscrepancy, pieces] using
      (propositionSixTwoNearCandidateDiscrepancy_eq_signedWeakPieces
        presentation digit epsilon rho I j length band)
  calc
    abs (nearDiscrepancy region) =
        abs ((pieces.map fun piece =>
          (piece.coefficient : Real) *
            nearDiscrepancy piece.region).sum) := congrArg abs hsigned
    _ <= (pieces.map fun piece =>
        abs (nearDiscrepancy piece.region)).sum := htriangle
    _ <= (pieces.map fun _ => pieceBudget * mass).sum := hsum
    _ = (pieces.length : Real) * pieceBudget * mass := hfactor
    _ <= budget * mass := mul_le_mul_of_nonneg_right hscalar hmass
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

end

end PrimesRestrictedDigits
