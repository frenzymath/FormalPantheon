import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetOccurrenceAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectFormalSignedTargetError

/-!
# Signed weak-piece target-occurrence absorption

The fixed weak-piece target estimate is summed over the compiler's multiplicity-preserving
signed List and then over both direct bands.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_list_common_threshold_at
    {alpha : Type*} (items : List alpha) (P : alpha -> Nat -> Prop)
    (hP : ∀ item, ∃ threshold : Nat, 1 <= threshold ∧
      ∀ length : Nat, threshold <= length -> P item length) :
    ∃ threshold : Nat, 1 <= threshold ∧
      ∀ item, item ∈ items -> ∀ length : Nat,
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
/-- For one direct band, the complete formal signed weak-piece target
occurrence discrepancy is eventually absorbed into any positive budget. -/
theorem
    exists_sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell : Nat) (region : Set (Fin ell -> Real))
    (presentation : TypeIIAffineMixedPresentation region)
    (band : SectionSixDirectBand) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let M : Nat := Nat.ceil (2 / delta)
        epsilon <= 1 / 64 ->
        delta < sectionSixThetaGap epsilon ->
        rho ^ 2 < delta ->
        2 * rho <= delta / 2 ->
        rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
        abs (sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
          presentation digit epsilon delta rho length band) <=
            budget * (A.card : Real) / Real.log X := by
  let M : Nat := Nat.ceil (2 / delta)
  let pieces := presentation.signedWeakPieces
  let pieceBudget : Real :=
    budget / (((pieces.length + 1 : Nat) : Real))
  have hpieceBudget : 0 < pieceBudget := by
    dsimp only [pieceBudget]
    positivity
  let PieceBound : TypeIIAffineSignedWeakPiece presentation -> Nat -> Prop :=
    fun piece length =>
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let B : Finset Nat := maynardAmbientCarrier X
        let lambda : Real :=
          (restrictedDigitDensity digit : Real) * (A.card : Real) / X
        let targetOccurrenceCount : Finset Nat -> Real := fun C =>
          ∑ pattern : SectionSixDirectStablePattern ell M,
            (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho
              ell piece.region length band C M pattern).filter fun candidate =>
                candidate.value ∈ typeIIOriginalRegionSupport XNat
                  (sectionSixDirectStableTargetRegion epsilon delta piece.region
                    band pattern)).card : Real)
        epsilon <= 1 / 64 ->
        delta < sectionSixThetaGap epsilon ->
        rho ^ 2 < delta ->
        2 * rho <= delta / 2 ->
        rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
        abs (targetOccurrenceCount A - lambda * targetOccurrenceCount B) <=
          pieceBudget * (A.card : Real) / Real.log X
  have hPieceThreshold : ∀ piece,
      ∃ threshold : Nat, 1 <= threshold ∧
        ∀ length : Nat, threshold <= length -> PieceBound piece length := by
    intro piece
    obtain ⟨threshold, hthreshold, hAt⟩ :=
      exists_sectionSixDirectStableTargetOccurrenceDiscrepancy_budget_upper
        delta pieceBudget hdelta hpieceBudget epsilon hepsilon ell M piece.region
          piece.weakPresentation band
    refine ⟨threshold, hthreshold, ?_⟩
    intro length hlength
    simpa only [PieceBound] using hAt length hlength
  obtain ⟨length0, hlength0, hAllPieces⟩ :=
    exists_list_common_threshold_at pieces PieceBound hPieceThreshold
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let mass : Real := (A.card : Real) / Real.log X
  let targetOccurrenceDiscrepancy :
      TypeIIAffineSignedWeakPiece presentation -> Real := fun piece =>
    let targetOccurrenceCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          piece.region length band C M pattern).filter fun candidate =>
            candidate.value ∈ typeIIOriginalRegionSupport XNat
              (sectionSixDirectStableTargetRegion epsilon delta piece.region band
                pattern)).card : Real)
    targetOccurrenceCount A - lambda * targetOccurrenceCount B
  have hPieceBound (piece : TypeIIAffineSignedWeakPiece presentation)
      (hpiece : piece ∈ pieces) :
      abs (targetOccurrenceDiscrepancy piece) <= pieceBudget * mass := by
    have hAt := hAllPieces piece hpiece length hlength
    dsimp only [PieceBound] at hAt
    have hBound := hAt digit hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth
      hglobalWidth
    have hBound' :
        abs (targetOccurrenceDiscrepancy piece) <=
          pieceBudget * (A.card : Real) / Real.log X := by
      simpa only [XNat, X, rho, A, B, M, lambda,
        targetOccurrenceDiscrepancy] using hBound
    calc
      abs (targetOccurrenceDiscrepancy piece) <=
          pieceBudget * (A.card : Real) / Real.log X := hBound'
      _ = pieceBudget * mass := by
        dsimp only [mass]
        ring
  have htriangle :
      abs ((pieces.map fun piece =>
          (piece.coefficient : Real) *
            targetOccurrenceDiscrepancy piece).sum) <=
        (pieces.map fun piece =>
          abs (targetOccurrenceDiscrepancy piece)).sum := by
    induction pieces with
    | nil => simp
    | cons piece remaining ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          abs ((piece.coefficient : Real) *
                targetOccurrenceDiscrepancy piece +
              (remaining.map fun current =>
                (current.coefficient : Real) *
                  targetOccurrenceDiscrepancy current).sum) <=
              abs ((piece.coefficient : Real) *
                targetOccurrenceDiscrepancy piece) +
                abs ((remaining.map fun current =>
                  (current.coefficient : Real) *
                    targetOccurrenceDiscrepancy current).sum) := abs_add_le _ _
          _ <= abs ((piece.coefficient : Real) *
                targetOccurrenceDiscrepancy piece) +
              (remaining.map fun current =>
                abs (targetOccurrenceDiscrepancy current)).sum := by gcongr
          _ = abs (targetOccurrenceDiscrepancy piece) +
              (remaining.map fun current =>
                abs (targetOccurrenceDiscrepancy current)).sum := by
            rw [abs_mul]
            simp [TypeIIAffineSignedWeakPiece.coefficient]
  have hsum :
      (pieces.map fun piece =>
          abs (targetOccurrenceDiscrepancy piece)).sum <=
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
  have hformal :
      sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
          presentation digit epsilon delta rho length band =
        (pieces.map fun piece =>
          (piece.coefficient : Real) *
            targetOccurrenceDiscrepancy piece).sum := by
    unfold sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
    rfl
  calc
    abs (sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
        presentation digit epsilon delta rho length band) =
        abs ((pieces.map fun piece =>
          (piece.coefficient : Real) *
            targetOccurrenceDiscrepancy piece).sum) := congrArg abs hformal
    _ <= (pieces.map fun piece =>
        abs (targetOccurrenceDiscrepancy piece)).sum := htriangle
    _ <= (pieces.map fun _ => pieceBudget * mass).sum := hsum
    _ = (pieces.length : Real) * pieceBudget * mass := hfactor
    _ <= budget * mass := mul_le_mul_of_nonneg_right hscalar hmass
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

set_option maxHeartbeats 2400000 in
/-- The sum of the two direct-band formal target discrepancies is eventually
absorbed into any positive budget. -/
theorem
    exists_sectionSixDirectTwoBandFormalSignedWeakPieceTargetOccurrenceDiscrepancy_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell : Nat) (region : Set (Fin ell -> Real))
    (presentation : TypeIIAffineMixedPresentation region) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let M : Nat := Nat.ceil (2 / delta)
        let formalTargetDiscrepancy : SectionSixDirectBand -> Real :=
          fun band =>
            sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
              presentation digit epsilon delta rho length band
        epsilon <= 1 / 64 ->
        delta < sectionSixThetaGap epsilon ->
        rho ^ 2 < delta ->
        2 * rho <= delta / 2 ->
        rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
        abs (formalTargetDiscrepancy .first +
          formalTargetDiscrepancy .second) <=
            budget * (A.card : Real) / Real.log X := by
  obtain ⟨lengthFirst, hlengthFirst, hFirst⟩ :=
    exists_sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy_budget_upper
      delta (budget / 2) hdelta (by positivity) epsilon hepsilon ell region
        presentation .first
  obtain ⟨lengthSecond, hlengthSecond, hSecond⟩ :=
    exists_sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy_budget_upper
      delta (budget / 2) hdelta (by positivity) epsilon hepsilon ell region
        presentation .second
  let length0 : Nat := max lengthFirst lengthSecond
  have hlength0 : 1 <= length0 :=
    hlengthFirst.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hlengthFirstAt : lengthFirst <= length := by
    have : lengthFirst <= length0 := by dsimp only [length0]; omega
    exact this.trans hlength
  have hlengthSecondAt : lengthSecond <= length := by
    have : lengthSecond <= length0 := by dsimp only [length0]; omega
    exact this.trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let formalTargetDiscrepancy : SectionSixDirectBand -> Real := fun band =>
    sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
      presentation digit epsilon delta rho length band
  have hFirstAt := hFirst length hlengthFirstAt digit hepsilonSmall
    hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hSecondAt := hSecond length hlengthSecondAt digit hepsilonSmall
    hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hFirstBound : abs (formalTargetDiscrepancy .first) <=
      budget / 2 * (A.card : Real) / Real.log X := by
    simpa only [formalTargetDiscrepancy, XNat, X, rho, A] using hFirstAt
  have hSecondBound : abs (formalTargetDiscrepancy .second) <=
      budget / 2 * (A.card : Real) / Real.log X := by
    simpa only [formalTargetDiscrepancy, XNat, X, rho, A] using hSecondAt
  calc
    abs (formalTargetDiscrepancy .first +
        formalTargetDiscrepancy .second) <=
        abs (formalTargetDiscrepancy .first) +
          abs (formalTargetDiscrepancy .second) := abs_add_le _ _
    _ <= budget / 2 * (A.card : Real) / Real.log X +
        budget / 2 * (A.card : Real) / Real.log X :=
      add_le_add hFirstBound hSecondBound
    _ = budget * (A.card : Real) / Real.log X := by ring

end

end PrimesRestrictedDigits
