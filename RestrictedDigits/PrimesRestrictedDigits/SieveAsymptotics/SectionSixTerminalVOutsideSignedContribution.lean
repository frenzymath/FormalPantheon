import PrimesRestrictedDigits.SieveAsymptotics.SectionSixStrictOutsideNearAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVSignedContribution
import Mathlib.Tactic.Ring

/-!
# Terminal-V outside signed contribution

The canonical terminal-V Sigma sum is rewritten as a state-labelled signed represented-tail
discrepancy. The existing positive outside-near incidence bound then absorbs both state bands
without forgetting occurrence labels.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sum_sectionSixTerminalVCofactorOutside_weight_eq
    {A B near : Finset Nat} {y lambda : Real}
    (hAB : A ⊆ B)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell)
    (hV : state.2.kind = .V) :
    (∑ m ∈ (sectionSixTerminalCofactorCarrier B y state).filter
        (fun m => m * state.1 ∉ near),
      sectionSixWeight A B lambda (m * state.1)) =
      ((sectionSixTerminalRepresentedCarrier A y state \ near).card : Real) -
        lambda *
          ((sectionSixTerminalRepresentedCarrier B y state \ near).card : Real) := by
  classical
  let outsideB := (sectionSixTerminalCofactorCarrier B y state).filter
    (fun m => m * state.1 ∉ near)
  let outsideA := (sectionSixTerminalCofactorCarrier A y state).filter
    (fun m => m * state.1 ∉ near)
  have hmemB (m : Nat) (hm : m ∈ outsideB) : m * state.1 ∈ B := by
    have hmCof : m ∈ sectionSixTerminalCofactorCarrier B y state :=
      (Finset.mem_filter.mp hm).1
    simp only [sectionSixTerminalCofactorCarrier, hV] at hmCof
    exact mem_sieveDilation.mp (mem_strictSiftedCarrier.mp hmCof).1
  have houtsideA : outsideA = outsideB.filter (fun m => m * state.1 ∈ A) := by
    dsimp only [outsideA, outsideB]
    rw [sectionSixTerminalCofactorCarrier_eq_filter_of_subset_of_kind_eq_V
      hAB y state hV]
    ext m
    simp only [Finset.mem_filter]
    tauto
  have hcardOutside (C : Finset Nat) :
      (((sectionSixTerminalCofactorCarrier C y state).filter
        (fun m => m * state.1 ∉ near)).card : Real) =
        ((sectionSixTerminalRepresentedCarrier C y state \ near).card : Real) := by
    have hmap : sectionSixTerminalRepresentedCarrier C y state \ near =
        ((sectionSixTerminalCofactorCarrier C y state).filter
          (fun m => m * state.1 ∉ near)).map
            (sectionSixTerminalRepresentedEmbedding state) := by
      simp only [sectionSixTerminalRepresentedCarrier]
      rw [Finset.sdiff_eq_filter, Finset.filter_map]
      rfl
    rw [hmap, Finset.card_map]
  change (∑ m ∈ outsideB,
      sectionSixWeight A B lambda (m * state.1)) = _
  calc
    (∑ m ∈ outsideB,
        sectionSixWeight A B lambda (m * state.1)) =
        ∑ m ∈ outsideB,
          ((if m * state.1 ∈ A then 1 else 0) - lambda) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact sectionSixWeight_of_mem_ambient A B lambda (hmemB m hm)
    _ = (∑ m ∈ outsideB, (if m * state.1 ∈ A then 1 else 0 : Real)) -
        ∑ _m ∈ outsideB, lambda := by
      rw [Finset.sum_sub_distrib]
    _ = ((outsideB.filter (fun m => m * state.1 ∈ A)).card : Real) -
        lambda * (outsideB.card : Real) := by
      rw [Finset.sum_boole]
      simp
      ring
    _ = (outsideA.card : Real) - lambda * (outsideB.card : Real) := by
      rw [houtsideA]
    _ = ((sectionSixTerminalRepresentedCarrier A y state \ near).card : Real) -
        lambda *
          ((sectionSixTerminalRepresentedCarrier B y state \ near).card : Real) := by
      rw [hcardOutside A, hcardOutside B]

/-- The outside candidate sum is the exact signed discrepancy of the
state-labelled represented tails. Non-V states remain explicit zero terms. -/
theorem sectionSixSourceBandTerminalVOutsideSignedCandidateSum_eq_stateTail
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (near : Finset Nat) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real := (restrictedDigitDensity digit : Real) *
      ((A.card : Real) / X)
    let states := sectionSixSourceBandTerminalStateFinset region hepsilon
      hepsilonSmall hlength hdeltaGap band
    sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
        hepsilon hepsilonSmall hlength hdeltaGap band y near =
      ∑ state ∈ states,
        if sectionSixTerminalVPredicate state then
          sectionSixTerminalVStateSign state *
            (((sectionSixTerminalVRepresentedCarrier A y state \ near).card : Real) -
              lambda *
                ((sectionSixTerminalVRepresentedCarrier B y state \ near).card : Real))
        else 0 := by
  classical
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  have hAB : A ⊆ B := by
    simpa only [A, B, X] using
      paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length
  change (∑ candidate ∈
      sectionSixSourceBandTerminalVOutsideCandidates region hepsilon
        hepsilonSmall hlength hdeltaGap band B y near,
      candidate.signedWeight A B lambda) = _
  rw [sectionSixSourceBandTerminalVOutsideCandidates,
    sectionSixSourceBandTerminalVFullCandidates,
    Finset.filter_sigma, Finset.sum_sigma]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro state hstate
  by_cases hV : sectionSixTerminalVPredicate state = true
  · rw [if_pos hV]
    have hkind : state.2.kind = .V := by
      simpa [sectionSixTerminalVPredicate] using hV
    change (∑ m ∈ (sectionSixTerminalCofactorCarrier B y state).filter
        (fun m => m * state.1 ∉ near),
      sectionSixTerminalVStateSign state *
        sectionSixWeight A B lambda (m * state.1)) = _
    rw [← Finset.mul_sum]
    rw [sum_sectionSixTerminalVCofactorOutside_weight_eq hAB state hkind]
    simp only [sectionSixTerminalVRepresentedCarrier, hV, if_true, A, B, X,
      lambda]
  · simp [hV]

/-- The signed outside sum is bounded by its positive restricted-plus-ambient
represented-tail charge, without cancellation across states. -/
theorem abs_sectionSixSourceBandTerminalVOutsideSignedCandidateSum_le_tailCharge
    (digit : Fin 10)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (near : Finset Nat) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real := (restrictedDigitDensity digit : Real) *
      ((A.card : Real) / X)
    abs (sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
        hepsilon hepsilonSmall hlength hdeltaGap band y near) <=
      (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlength hdeltaGap band,
        ((sectionSixTerminalVRepresentedCarrier A y state \ near).card : Real)) +
      lambda *
        (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
            hepsilonSmall hlength hdeltaGap band,
          ((sectionSixTerminalVRepresentedCarrier B y state \ near).card : Real)) := by
  classical
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let states := sectionSixSourceBandTerminalStateFinset region hepsilon
    hepsilonSmall hlength hdeltaGap band
  let a : SectionSixAnyState band ell -> Real := fun state =>
    ((sectionSixTerminalVRepresentedCarrier A y state \ near).card : Real)
  let b : SectionSixAnyState band ell -> Real := fun state =>
    ((sectionSixTerminalVRepresentedCarrier B y state \ near).card : Real)
  have hXPos : 0 < X := by
    dsimp only [X]
    positivity
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact mul_nonneg (restrictedDigitDensity_nonneg digit)
      (div_nonneg (by positivity) hXPos.le)
  have hidentity :=
    sectionSixSourceBandTerminalVOutsideSignedCandidateSum_eq_stateTail
      digit region hepsilon hepsilonSmall hlength hdeltaGap band y near
  change abs (sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
      hepsilon hepsilonSmall hlength hdeltaGap band y near) <=
    (∑ state ∈ states, a state) + lambda * ∑ state ∈ states, b state
  have hidentity' :
      sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGap band y near =
        ∑ state ∈ states,
          sectionSixTerminalVStateSign state * (a state - lambda * b state) := by
    rw [hidentity]
    apply Finset.sum_congr rfl
    intro state hstate
    by_cases hV : sectionSixTerminalVPredicate state = true
    · simp only [hV, if_true, X, A, B, lambda, a, b]
    · have hfalse : sectionSixTerminalVPredicate state = false :=
        Bool.eq_false_of_not_eq_true hV
      simp [hfalse, a, b, sectionSixTerminalVRepresentedCarrier]
  rw [hidentity']
  calc
    abs (∑ state ∈ states,
        sectionSixTerminalVStateSign state * (a state - lambda * b state)) <=
      ∑ state ∈ states,
        abs (sectionSixTerminalVStateSign state *
          (a state - lambda * b state)) := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ state ∈ states, abs (a state - lambda * b state) := by
      apply Finset.sum_congr rfl
      intro state hstate
      rw [abs_mul]
      simp [sectionSixTerminalVStateSign]
    _ <= ∑ state ∈ states, (a state + lambda * b state) := by
      apply Finset.sum_le_sum
      intro state hstate
      have ha : 0 <= a state := by dsimp only [a]; positivity
      have hb : 0 <= b state := by dsimp only [b]; positivity
      calc
        abs (a state - lambda * b state) <=
            abs (a state) + abs (lambda * b state) := abs_sub _ _
        _ = a state + lambda * b state := by
          rw [abs_of_nonneg ha, abs_mul, abs_of_nonneg hlambda,
            abs_of_nonneg hb]
    _ = (∑ state ∈ states, a state) +
        lambda * ∑ state ∈ states, b state := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Both terminal-V outside bands are eventually absorbed into an arbitrary
positive logarithmic budget. -/
theorem exists_sectionSixTerminalVTwoBandOutsideSignedContribution_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (ell : Nat) (rho : Real) (hrho : 0 < rho)
    (delta : Real) (hdelta : 0 < delta)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon) :
    ∃ (length0 : Nat) (hlength0 : 1 <= length0),
      ∀ region : Set (Fin ell -> Real),
      ∀ (length : Nat) (hlength : length0 <= length),
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let y : Real := X ^ delta
        let near : Finset Nat :=
          typeIINearXCarrier XNat (majorArcM2LogLogDelta XNat)
        let hlengthOne : 1 <= length := hlength0.trans hlength
        let outsideLow : Real :=
          sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
            hepsilon hepsilonSmall hlengthOne hdeltaGap .low y near
        let outsideHigh : Real :=
          sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
            hepsilon hepsilonSmall hlengthOne hdeltaGap .high y near
        abs (outsideLow + outsideHigh) <=
          rho * (A.card : Real) / Real.log X := by
  obtain ⟨length0, hlength0, hOutside⟩ :=
    exists_sectionSixTerminalVOutsideNearAbsorptionThreshold epsilon hepsilon
      hepsilonSmall ell (rho / 2) (by positivity) delta hdelta hdeltaGap
  refine ⟨length0, hlength0, ?_⟩
  intro region length hlength digit
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let y : Real := X ^ delta
  let near : Finset Nat :=
    typeIINearXCarrier XNat (majorArcM2LogLogDelta XNat)
  let hlengthOne : 1 <= length := hlength0.trans hlength
  let outside : SectionSixStateBand -> Real := fun band =>
    sectionSixSourceBandTerminalVOutsideSignedCandidateSum digit region
      hepsilon hepsilonSmall hlengthOne hdeltaGap band y near
  let charge : SectionSixStateBand -> Real := fun band =>
    let states := sectionSixSourceBandTerminalStateFinset region hepsilon
      hepsilonSmall hlengthOne hdeltaGap band
    (∑ state ∈ states,
      ((sectionSixTerminalVRepresentedCarrier A y state \ near).card : Real)) +
      lambda * (∑ state ∈ states,
        ((sectionSixTerminalVRepresentedCarrier B y state \ near).card : Real))
  have hLowAbs : abs (outside .low) <= charge .low := by
    have h :=
      abs_sectionSixSourceBandTerminalVOutsideSignedCandidateSum_le_tailCharge
        digit region hepsilon hepsilonSmall hlengthOne hdeltaGap .low y near
    simpa only [outside, charge, X, A, B, lambda] using h
  have hHighAbs : abs (outside .high) <= charge .high := by
    have h :=
      abs_sectionSixSourceBandTerminalVOutsideSignedCandidateSum_le_tailCharge
        digit region hepsilon hepsilonSmall hlengthOne hdeltaGap .high y near
    simpa only [outside, charge, X, A, B, lambda] using h
  have hLowCharge : charge .low <=
      rho / 2 * (A.card : Real) / Real.log X := by
    have h := hOutside length hlength digit region .low
    convert h using 1
    all_goals
      simp only [charge, XNat, X, A, B, lambda, y, near]
      ring
  have hHighCharge : charge .high <=
      rho / 2 * (A.card : Real) / Real.log X := by
    have h := hOutside length hlength digit region .high
    convert h using 1
    all_goals
      simp only [charge, XNat, X, A, B, lambda, y, near]
      ring
  calc
    abs (outside .low + outside .high) <=
        abs (outside .low) + abs (outside .high) := abs_add_le _ _
    _ <= charge .low + charge .high := add_le_add hLowAbs hHighAbs
    _ <= rho / 2 * (A.card : Real) / Real.log X +
        rho / 2 * (A.card : Real) / Real.log X :=
      add_le_add hLowCharge hHighCharge
    _ = rho * (A.card : Real) / Real.log X := by ring

end

end PrimesRestrictedDigits
