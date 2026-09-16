import PrimesRestrictedDigits.SieveAsymptotics.TypeIIPrimeTupleMultiplicity

/-!
# Multiplicity-aware Type II internal count

This packages the restricted plus ambient unweighted tuple count used on the short path
through Maynard's Eq. (9.11). It pays factorial product multiplicity and uses the strict
cutoff `X^(eta/8)`.
-/

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 1200000 in
theorem exists_primeTupleInternalCount_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ C : Real, 0 < C ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          ∀ digit : Fin 10,
            let X : Real := ((10 ^ length : Nat) : Real)
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            ∀ ell : Nat, (ell : Real) <= 2 / eta ->
              ∀ tuples : Finset (Fin ell -> Nat),
                (∀ p ∈ tuples, ∀ i, (p i).Prime) ->
                (∀ p ∈ tuples,
                  strictRoughPredicate (X ^ (eta / 8))
                    (primeTupleProduct p)) ->
                ((tuples.filter fun p =>
                    primeTupleProduct p ∈ A).card : Real) +
                    (restrictedDigitDensity digit : Real) *
                      (A.card : Real) / X *
                      ((tuples.filter fun p =>
                        primeTupleProduct p ∈ B).card : Real) <=
                  C * (A.card : Real) / Real.log X := by
  have htheta : 0 < eta / 2 := by linarith
  obtain ⟨CA, hCA, lengthA, hlengthA, hA⟩ :=
    exists_paddedRestrictedSiftedCount_eta_upper (eta / 2) htheta
  obtain ⟨CB, hCB, lengthB, hlengthB, hB⟩ :=
    exists_maynardAmbientSiftedCount_eta_upper (eta / 2) htheta
  let arityFactor : Real :=
    (Nat.factorial (Nat.ceil (2 / eta)) : Real)
  let C : Real := arityFactor * (CA + (10 / 9 : Real) * CB)
  have harityFactor : 0 < arityFactor := by
    dsimp [arityFactor]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let length0 : Nat := max lengthA lengthB
  refine ⟨C, hC, length0, ?_, ?_⟩
  · dsimp [length0]
    omega
  · intro length hlength digit
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    change ∀ ell : Nat, (ell : Real) <= 2 / eta ->
      ∀ tuples : Finset (Fin ell -> Nat),
        (∀ p ∈ tuples, ∀ i, (p i).Prime) ->
        (∀ p ∈ tuples,
          strictRoughPredicate (X ^ (eta / 8))
            (primeTupleProduct p)) ->
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ A).card : Real) +
            (restrictedDigitDensity digit : Real) *
              (A.card : Real) / X *
              ((tuples.filter fun p =>
                primeTupleProduct p ∈ B).card : Real) <=
          C * (A.card : Real) / Real.log X
    intro ell hell tuples hprime hrough
    have hlengthA' : lengthA <= length := by
      exact (Nat.le_max_left lengthA lengthB).trans hlength
    have hlengthB' : lengthB <= length := by
      exact (Nat.le_max_right lengthA lengthB).trans hlength
    have hlengthOne : 1 <= length := hlengthA.trans hlengthA'
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hXpos : 0 < X := by linarith
    have hlogPos : 0 < Real.log X := Real.log_pos hX
    have hthetaQuarter : (eta / 2) / 4 = eta / 8 := by ring
    have hrestricted :
        ((strictSiftedCarrier A (X ^ (eta / 8))).card : Real) <=
          CA * (A.card : Real) / Real.log X := by
      simpa only [X, A, hthetaQuarter] using
        hA length hlengthA' digit
    have hambient :
        ((strictSiftedCarrier B (X ^ (eta / 8))).card : Real) <=
          CB * X / Real.log X := by
      simpa only [X, B, hthetaQuarter] using hB length hlengthB'
    have hcountA :=
      card_primeTuples_product_mem_le_factorial_mul_sifted
        A (X ^ (eta / 8)) tuples hprime hrough
    have hcountB :=
      card_primeTuples_product_mem_le_factorial_mul_sifted
        B (X ^ (eta / 8)) tuples hprime hrough
    have hcountAReal :
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ A).card : Real) <=
          (Nat.factorial ell : Real) *
            ((strictSiftedCarrier A
              (X ^ (eta / 8))).card : Real) := by
      exact_mod_cast hcountA
    have hcountBReal :
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ B).card : Real) <=
          (Nat.factorial ell : Real) *
            ((strictSiftedCarrier B
              (X ^ (eta / 8))).card : Real) := by
      exact_mod_cast hcountB
    have hfactorialNat :
        Nat.factorial ell <= Nat.factorial (Nat.ceil (2 / eta)) :=
      factorial_le_arityCeil hell
    have hfactorial : (Nat.factorial ell : Real) <= arityFactor := by
      dsimp [arityFactor]
      exact_mod_cast hfactorialNat
    have htupleA :
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ A).card : Real) <=
          arityFactor * CA * (A.card : Real) / Real.log X := by
      calc
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ A).card : Real) <=
            (Nat.factorial ell : Real) *
              ((strictSiftedCarrier A
                (X ^ (eta / 8))).card : Real) := hcountAReal
        _ <= arityFactor *
              ((strictSiftedCarrier A
                (X ^ (eta / 8))).card : Real) := by
          exact mul_le_mul_of_nonneg_right hfactorial (by positivity)
        _ <= arityFactor *
              (CA * (A.card : Real) / Real.log X) := by
          exact mul_le_mul_of_nonneg_left hrestricted
            harityFactor.le
        _ = arityFactor * CA * (A.card : Real) / Real.log X := by
          ring
    have htupleB :
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ B).card : Real) <=
          arityFactor * CB * X / Real.log X := by
      calc
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ B).card : Real) <=
            (Nat.factorial ell : Real) *
              ((strictSiftedCarrier B
                (X ^ (eta / 8))).card : Real) := hcountBReal
        _ <= arityFactor *
              ((strictSiftedCarrier B
                (X ^ (eta / 8))).card : Real) := by
          exact mul_le_mul_of_nonneg_right hfactorial (by positivity)
        _ <= arityFactor * (CB * X / Real.log X) := by
          exact mul_le_mul_of_nonneg_left hambient
            harityFactor.le
        _ = arityFactor * CB * X / Real.log X := by ring
    let rho : Real := restrictedDigitDensity digit
    have hrhoNonneg : 0 <= rho := by
      dsimp [rho]
      rw [restrictedDigitDensity_eq]
      split_ifs <;> norm_num
    have hrhoUpper : rho <= (10 / 9 : Real) := by
      dsimp [rho]
      rw [restrictedDigitDensity_eq]
      split_ifs <;> norm_num
    let lambda : Real := rho * (A.card : Real) / X
    have hlambda : 0 <= lambda := by
      dsimp [lambda]
      positivity
    have hweighted :
        lambda *
              ((tuples.filter fun p =>
                primeTupleProduct p ∈ B).card : Real) <=
          (10 / 9 : Real) * arityFactor * CB *
            (A.card : Real) / Real.log X := by
      calc
        lambda *
              ((tuples.filter fun p =>
                primeTupleProduct p ∈ B).card : Real) <=
            lambda *
              (arityFactor * CB * X / Real.log X) :=
          mul_le_mul_of_nonneg_left htupleB hlambda
        _ = rho * arityFactor * CB *
              (A.card : Real) / Real.log X := by
          dsimp [lambda]
          field_simp [hXpos.ne', hlogPos.ne']
        _ <= (10 / 9 : Real) * arityFactor * CB *
              (A.card : Real) / Real.log X := by
          rw [show rho * arityFactor * CB *
                (A.card : Real) / Real.log X =
              rho * (arityFactor * CB *
                (A.card : Real) / Real.log X) by ring]
          rw [show (10 / 9 : Real) * arityFactor * CB *
                (A.card : Real) / Real.log X =
              (10 / 9 : Real) * (arityFactor * CB *
                (A.card : Real) / Real.log X) by ring]
          exact mul_le_mul_of_nonneg_right hrhoUpper (by positivity)
    have hfinal :
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ A).card : Real) +
            lambda *
              ((tuples.filter fun p =>
                primeTupleProduct p ∈ B).card : Real) <=
          C * (A.card : Real) / Real.log X := by
      calc
        ((tuples.filter fun p =>
            primeTupleProduct p ∈ A).card : Real) +
              lambda *
                ((tuples.filter fun p =>
                  primeTupleProduct p ∈ B).card : Real) <=
            arityFactor * CA * (A.card : Real) / Real.log X +
              (10 / 9 : Real) * arityFactor * CB *
                (A.card : Real) / Real.log X :=
          add_le_add htupleA hweighted
        _ = C * (A.card : Real) / Real.log X := by
          dsimp [C]
          ring
    simpa only [lambda, rho] using hfinal

end

end PrimesRestrictedDigits
