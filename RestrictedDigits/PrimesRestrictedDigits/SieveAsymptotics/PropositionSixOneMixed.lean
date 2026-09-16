import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneSignedWeakPieces
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOne

/-!
# Mixed-strict Proposition 6.1

This sums the proved weak-halfspace Proposition 6.1 estimate over the exact signed weak pieces
of a mixed affine presentation. See `MAYNARD-PRD-PUBLISHED`, pp. 137--138.
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

/-- Proposition 6.1 for a finite mixture of weak and strict affine walls. -/
theorem propositionSixOneMixed
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region) :
    propositionSixOneAsymptotic epsilon ell region := by
  intro rho hrho
  let pieces := presentation.signedWeakPieces
  let pieceBudget : Real :=
    rho / (((pieces.length + 1 : Nat) : Real))
  have hpieceBudget : 0 < pieceBudget := by
    dsimp only [pieceBudget]
    positivity
  let PieceBound : TypeIIAffineSignedWeakPiece presentation -> Nat -> Prop :=
    fun piece length => forall digit : Fin 10,
      abs (propositionSixOneSum epsilon ell piece.region digit length) <=
        pieceBudget *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real)
  have hPieceThreshold : forall piece,
      exists threshold : Nat, 1 <= threshold ∧
        forall length : Nat, threshold <= length -> PieceBound piece length := by
    intro piece
    obtain ⟨threshold, hthreshold, hAt⟩ :=
      propositionSixOne epsilon hepsilon hepsilonSmall hepsilonRosser
        piece.weakPresentation pieceBudget hpieceBudget
    refine ⟨threshold, hthreshold, ?_⟩
    intro length hlength
    simpa only [PieceBound] using hAt length hlength
  obtain ⟨length0, hlength0, hAllPieces⟩ :=
    exists_list_common_threshold pieces PieceBound hPieceThreshold
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A := paddedRestrictedNumbers digit length
  let mass : Real := (A.card : Real) / Real.log X
  have hPieceBound (piece : TypeIIAffineSignedWeakPiece presentation)
      (hpiece : piece ∈ pieces) :
      abs (propositionSixOneSum epsilon ell piece.region digit length) <=
        pieceBudget * mass := by
    have hAt := hAllPieces piece hpiece length hlength
    dsimp only [PieceBound] at hAt
    have hBound := hAt digit
    have hBound' :
        abs (propositionSixOneSum epsilon ell piece.region digit length) <=
          pieceBudget * (A.card : Real) / Real.log X := by
      simpa only [A, X, XNat] using hBound
    calc
      abs (propositionSixOneSum epsilon ell piece.region digit length) <=
          pieceBudget * (A.card : Real) / Real.log X := hBound'
      _ = pieceBudget * mass := by
        dsimp only [mass]
        ring
  have htriangle :
      abs ((pieces.map fun piece =>
          (piece.coefficient : Real) *
            propositionSixOneSum epsilon ell piece.region digit length).sum) <=
        (pieces.map fun piece =>
          abs (propositionSixOneSum epsilon ell piece.region digit length)).sum := by
    induction pieces with
    | nil => simp
    | cons piece remaining ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          abs ((piece.coefficient : Real) *
                propositionSixOneSum epsilon ell piece.region digit length +
              (remaining.map fun current =>
                (current.coefficient : Real) *
                  propositionSixOneSum epsilon ell current.region digit
                    length).sum) <=
              abs ((piece.coefficient : Real) *
                propositionSixOneSum epsilon ell piece.region digit length) +
                abs ((remaining.map fun current =>
                  (current.coefficient : Real) *
                    propositionSixOneSum epsilon ell current.region digit
                      length).sum) := abs_add_le _ _
          _ <= abs ((piece.coefficient : Real) *
                propositionSixOneSum epsilon ell piece.region digit length) +
              (remaining.map fun current =>
                abs (propositionSixOneSum epsilon ell current.region digit
                  length)).sum := by gcongr
          _ = abs (propositionSixOneSum epsilon ell piece.region digit length) +
              (remaining.map fun current =>
                abs (propositionSixOneSum epsilon ell current.region digit
                  length)).sum := by
            rw [abs_mul]
            simp [TypeIIAffineSignedWeakPiece.coefficient]
  have hsum :
      (pieces.map fun piece =>
          abs (propositionSixOneSum epsilon ell piece.region digit length)).sum <=
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
  have hscalar : (pieces.length : Real) * pieceBudget <= rho := by
    dsimp only [pieceBudget]
    rw [show (pieces.length : Real) *
        (rho / ((pieces.length + 1 : Nat) : Real)) =
          ((pieces.length : Real) * rho) /
            ((pieces.length + 1 : Nat) : Real) by ring]
    apply (div_le_iff₀ hdenominator).2
    have hcount : (pieces.length : Real) <=
        ((pieces.length + 1 : Nat) : Real) := by
      exact_mod_cast Nat.le_succ pieces.length
    calc
      (pieces.length : Real) * rho <=
          ((pieces.length + 1 : Nat) : Real) * rho :=
        mul_le_mul_of_nonneg_right hcount hrho.le
      _ = rho * ((pieces.length + 1 : Nat) : Real) := by ring
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
      propositionSixOneSum epsilon ell region digit length =
        (pieces.map fun piece =>
          (piece.coefficient : Real) *
            propositionSixOneSum epsilon ell piece.region digit length).sum := by
    simpa only [pieces] using
      propositionSixOneSum_eq_signedWeakPieces presentation epsilon digit
        length
  calc
    abs (propositionSixOneSum epsilon ell region digit length) =
        abs ((pieces.map fun piece =>
          (piece.coefficient : Real) *
            propositionSixOneSum epsilon ell piece.region digit length).sum) :=
      congrArg abs hsigned
    _ <= (pieces.map fun piece =>
        abs (propositionSixOneSum epsilon ell piece.region digit length)).sum :=
      htriangle
    _ <= (pieces.map fun _ => pieceBudget * mass).sum := hsum
    _ = (pieces.length : Real) * pieceBudget * mass := hfactor
    _ <= rho * mass := mul_le_mul_of_nonneg_right hscalar hmass
    _ = rho * ((paddedRestrictedNumbers digit length).card : Real) /
        Real.log ((10 ^ length : Nat) : Real) := by
      dsimp only [mass, A, X, XNat]
      ring

end

end PrimesRestrictedDigits
