import PrimesRestrictedDigits.SieveAsymptotics.TypeIICubeFamily

/-!
# The unweighted interior-cube family error

This file applies the tuple count to a finite family of natural grid anchors. It covers only
the `tilde 1` interior-family term in Maynard's Eqs. (9.10)--(9.11).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 1200000 in
theorem exists_majorArcCubeInternalError_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ C : Real, 0 < C ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          ∀ digit : Fin 10, ∀ k : Nat,
            ∀ delta : Real, 0 <= delta ->
              (((k + 1 : Nat) : Real) <= 2 / eta) ->
                ∀ anchors : Finset (Fin k -> Nat),
                  (∀ anchor ∈ anchors, ∀ i,
                    eta / 2 <= scaledNaturalCubeAnchor delta anchor i) ->
                  let XNat : Nat := 10 ^ length
                  let X : Real := (XNat : Real)
                  let A : Finset Nat :=
                    paddedRestrictedNumbers digit length
                  let B : Finset Nat := maynardAmbientCarrier X
                  let tupleFamily : (Fin k -> Nat) ->
                      Finset (Fin (k + 1) -> Nat) := fun anchor =>
                    majorArcPrimeTuples XNat
                      (scaledNaturalCubeAnchor delta anchor) delta eta
                  delta *
                    ((∑ anchor ∈ anchors,
                        (((primeTupleProductSupport
                          (tupleFamily anchor)).filter
                            (fun n => n ∈ A)).card : Real)) +
                      (restrictedDigitDensity digit : Real) *
                          (A.card : Real) / X *
                        (∑ anchor ∈ anchors,
                          (((primeTupleProductSupport
                            (tupleFamily anchor)).filter
                              (fun n => n ∈ B)).card : Real))) <=
                    delta * (C * (A.card : Real) / Real.log X) := by
  obtain ⟨C, hC, length0, hlength0, hbound⟩ :=
    exists_primeTupleInternalCount_eta_upper eta heta
  refine ⟨C, hC, length0, hlength0, ?_⟩
  intro length hlength digit k delta hdelta hell anchors hmargin
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let tupleFamily : (Fin k -> Nat) ->
      Finset (Fin (k + 1) -> Nat) := fun anchor =>
    majorArcPrimeTuples XNat
      (scaledNaturalCubeAnchor delta anchor) delta eta
  change delta *
      ((∑ anchor ∈ anchors,
          (((primeTupleProductSupport
            (tupleFamily anchor)).filter
              (fun n => n ∈ A)).card : Real)) +
        (restrictedDigitDensity digit : Real) *
            (A.card : Real) / X *
          (∑ anchor ∈ anchors,
            (((primeTupleProductSupport
              (tupleFamily anchor)).filter
                (fun n => n ∈ B)).card : Real))) <=
    delta * (C * (A.card : Real) / Real.log X)
  rcases lt_or_eq_of_le hdelta with hdeltaPos | rfl
  · let tuples : Finset (Fin (k + 1) -> Nat) :=
      anchors.biUnion tupleFamily
    have hlengthOne : 1 <= length := hlength0.trans hlength
    have hXNat : 1 < XNat := by
      dsimp [XNat]
      exact Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast hXNat
    have hXpos : 0 < X := by linarith
    have hpairwise :
        (anchors : Set (Fin k -> Nat)).PairwiseDisjoint tupleFamily := by
      intro u hu v hv huv
      have hglobal :=
        pairwiseDisjoint_majorArcPrimeTuples_scaledNaturalCubeAnchor
          XNat k delta eta hdeltaPos
      simpa [tupleFamily] using
        hglobal (Set.mem_univ u) (Set.mem_univ v) huv
    have hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime := by
      intro p hp i
      change p ∈ anchors.biUnion tupleFamily at hp
      obtain ⟨anchor, hanchor, hpTuple⟩ := Finset.mem_biUnion.mp hp
      exact Nat.prime_of_mem_primesLE
        ((mem_majorArcPrimeTuples_iff.mp hpTuple).1 i)
    have hrough : ∀ p ∈ tuples,
        strictRoughPredicate (X ^ (eta / 8))
          (primeTupleProduct p) := by
      intro p hp
      change p ∈ anchors.biUnion tupleFamily at hp
      obtain ⟨anchor, hanchor, hpTuple⟩ := Finset.mem_biUnion.mp hp
      have hroughNat :=
        majorArcPrimeTuple_strictRough_etaEighth hXNat heta
          (hmargin anchor hanchor) hpTuple
      simpa [X] using hroughNat
    have htupleBound :
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ A).card : Real) +
            (restrictedDigitDensity digit : Real) *
              (A.card : Real) / X *
              ((tuples.filter fun p =>
                primeTupleProduct p ∈ B).card : Real) <=
          C * (A.card : Real) / Real.log X := by
      simpa only [XNat, X, A, B] using
        hbound length hlength digit (k + 1) hell tuples hprime hrough
    have hsupportA :=
      sum_card_primeTupleProductSupport_filter_le_biUnion
        anchors tupleFamily A hpairwise
    have hsupportB :=
      sum_card_primeTupleProductSupport_filter_le_biUnion
        anchors tupleFamily B hpairwise
    have hsupportAReal :
        (∑ anchor ∈ anchors,
          (((primeTupleProductSupport
            (tupleFamily anchor)).filter
              (fun n => n ∈ A)).card : Real)) <=
        ((tuples.filter fun p =>
          primeTupleProduct p ∈ A).card : Real) := by
      dsimp [tuples]
      exact_mod_cast hsupportA
    have hsupportBReal :
        (∑ anchor ∈ anchors,
          (((primeTupleProductSupport
            (tupleFamily anchor)).filter
              (fun n => n ∈ B)).card : Real)) <=
        ((tuples.filter fun p =>
          primeTupleProduct p ∈ B).card : Real) := by
      dsimp [tuples]
      exact_mod_cast hsupportB
    let rho : Real := restrictedDigitDensity digit
    let lambda : Real := rho * (A.card : Real) / X
    have hrho : 0 <= rho := by
      dsimp [rho]
      rw [restrictedDigitDensity_eq]
      split_ifs <;> norm_num
    have hlambda : 0 <= lambda := by
      dsimp [lambda]
      positivity
    have hsupportCombined :
        (∑ anchor ∈ anchors,
            (((primeTupleProductSupport
              (tupleFamily anchor)).filter
                (fun n => n ∈ A)).card : Real)) +
          lambda *
            (∑ anchor ∈ anchors,
              (((primeTupleProductSupport
                (tupleFamily anchor)).filter
                  (fun n => n ∈ B)).card : Real)) <=
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ A).card : Real) +
          lambda *
            ((tuples.filter fun p =>
              primeTupleProduct p ∈ B).card : Real) := by
      exact add_le_add hsupportAReal
        (mul_le_mul_of_nonneg_left hsupportBReal hlambda)
    have hunscaled :
        (∑ anchor ∈ anchors,
            (((primeTupleProductSupport
              (tupleFamily anchor)).filter
                (fun n => n ∈ A)).card : Real)) +
          lambda *
            (∑ anchor ∈ anchors,
              (((primeTupleProductSupport
                (tupleFamily anchor)).filter
                  (fun n => n ∈ B)).card : Real)) <=
        C * (A.card : Real) / Real.log X := by
      apply hsupportCombined.trans
      simpa only [lambda, rho] using htupleBound
    apply mul_le_mul_of_nonneg_left _ hdeltaPos.le
    simpa only [lambda, rho] using hunscaled
  · simp

end

end PrimesRestrictedDigits
