import PrimesRestrictedDigits.SieveAsymptotics.SourceFundamentalSieveAggregate
import PrimesRestrictedDigits.SieveAsymptotics.AmbientFundamentalSieveAggregate
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalCoprimeRemoval
import PrimesRestrictedDigits.SieveAsymptotics.DecimalAmbientBoundingSieve
import PrimesRestrictedDigits.SieveAsymptotics.SourceFundamentalSieveAggregateBridges
import PrimesRestrictedDigits.TypeI.PropositionSevenOne
import PrimesRestrictedDigits.Digits.LocalDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Common small-delta fundamental-sieve split

This assembles the source and ambient corrected splits after removing the coprimality filters.
The common product main term is cancelled exactly using the decimal power-of-ten cardinality
and local-density identities.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private lemma abs_sub_mul_le (u v a b scale : Real) (hscale : 0 <= scale)
    (hmain : a = scale * b) :
    |u - scale * v| <= |u - a| + scale * |v - b| := by
  calc
    |u - scale * v| <= |u - a| + |a - scale * v| := abs_sub_le _ _ _
    _ = |u - a| + |scale * (b - v)| := by
      have hdiff : a - scale * v = scale * (b - v) := by
        rw [hmain]
        ring
      rw [hdiff]
    _ = |u - a| + scale * |v - b| := by
      rw [abs_mul, abs_of_nonneg hscale]
      have habs : |b - v| = |v - b| := abs_sub_comm b v
      rw [habs]

theorem exists_correctedFundamentalSmallDeltaSplit :
    ∃ C : Real, 1 <= C ∧
      ∀ epsilon : Real, 0 < epsilon -> epsilon <= 1 / 64 ->
        2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1 ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
            ∀ (digit : Fin 10) (delta : Real),
              0 < delta -> delta <= epsilon ^ (4 : Nat) ->
              let X : Real := ((10 ^ length : Nat) : Real)
              5 <= X ^ delta ->
              (∑ d ∈ maynardStrictRoughCarrier
                  (X ^ (50 / 77 - epsilon)) (X ^ delta),
                |((strictSiftedCarrier
                    (sieveDilation
                      (paddedRestrictedNumbers digit length) d.toPNat')
                    (X ^ delta)).card : Real) -
                  (restrictedDigitDensity digit : Real) *
                    ((paddedRestrictedNumbers digit length).card : Real) /
                      X *
                    ((strictSiftedCarrier
                      (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                      (X ^ delta)).card : Real)|) <=
                C * ((paddedRestrictedNumbers digit length).card : Real) *
                    Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
                      Real.log X +
                  C * ((paddedRestrictedNumbers digit length).card : Real) /
                    Real.log X ^ (100 : Nat) := by
  obtain ⟨CSource, hCSource, hSource⟩ :=
    exists_correctedSourceFundamentalSplit
  obtain ⟨CAmbient, hCAmbient, hAmbient⟩ :=
    exists_correctedAmbientFundamentalSplit
  let C : Real := CSource + CAmbient
  have hC : 1 <= C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon hepsilonSmall hepsilonRosser
  obtain ⟨lengthSource, hlengthSourceOne, hlengthSource⟩ :=
    hSource epsilon hepsilon hepsilonSmall hepsilonRosser
  obtain ⟨lengthAmbient, hlengthAmbientOne, hlengthAmbient⟩ :=
    hAmbient epsilon hepsilon hepsilonSmall hepsilonRosser
  let length0 : Nat := max 1 (max lengthSource lengthAmbient)
  refine ⟨length0, ?_, ?_⟩
  · dsimp [length0]
    omega
  · intro length hlength digit delta hdelta hdeltaEpsilon
    dsimp
    intro hcutoff
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let D : Finset Nat := maynardStrictRoughCarrier
      (X ^ (50 / 77 - epsilon)) (X ^ delta)
    let V : Real := decimalExcludedPrimeProduct (X ^ delta)
    let kappa : Real := typeIProgressionDensity digit
    let kappaA : Real := restrictedDigitDensity digit
    let scale : Real := kappaA * (A.card : Real) / X
    let R : Real := Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X
    let E : Real := 1 / Real.log X ^ (100 : Nat)
    have hlengthOne : 1 <= length := by
      have h0 : 1 <= length0 := by
        dsimp [length0]
        omega
      exact h0.trans hlength
    have hlengthPos : 0 < length := Nat.zero_lt_of_lt hlengthOne
    have hlengthSource' : lengthSource <= length := by
      have hm : lengthSource <= max lengthSource lengthAmbient :=
        Nat.le_max_left _ _
      exact hm.trans ((Nat.le_max_right 1 _).trans hlength)
    have hlengthAmbient' : lengthAmbient <= length := by
      have hm : lengthAmbient <= max lengthSource lengthAmbient :=
        Nat.le_max_right _ _
      exact hm.trans ((Nat.le_max_right 1 _).trans hlength)
    have hXgt : 1 < X := by
      dsimp [X]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hXpos : 0 < X := lt_trans (by norm_num) hXgt
    have hXne : X ≠ 0 := ne_of_gt hXpos
    have hcutoffX : 5 <= X ^ delta := by simpa [X] using hcutoff
    have hsourceRaw := hlengthSource length hlengthSource' digit delta
      hdelta hdeltaEpsilon
    dsimp at hsourceRaw
    have hsourceRaw := hsourceRaw hcutoffX
    have hambientRaw := hlengthAmbient length hlengthAmbient' delta
      hdelta hdeltaEpsilon
    dsimp at hambientRaw
    have hambientRaw := hambientRaw hcutoffX
    have hsourceBound :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation (A.filter (fun n => n.Coprime 10)) d.toPNat')
              (X ^ delta)).card : Real) -
            kappa * (A.card : Real) / (d : Real) * V|) <=
          CSource * (A.card : Real) * R +
            CSource * (A.card : Real) * E := by
      simpa [D, A, V, R, E, X, kappa, div_eq_mul_inv, mul_assoc,
        mul_comm, mul_left_comm] using hsourceRaw
    have hambientBound :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation
                (maynardCoprimeAmbientCarrier X) d.toPNat')
              (X ^ delta)).card : Real) -
            ((maynardCoprimeAmbientCarrier X).card : Real) /
              (d : Real) * V|) <=
          CAmbient * ((maynardCoprimeAmbientCarrier X).card : Real) * R +
            CAmbient * ((maynardCoprimeAmbientCarrier X).card : Real) * E := by
      simpa [D, V, R, E, X, div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm] using hambientRaw
    have hBcard : ((maynardAmbientCarrier X).card : Real) = X := by
      dsimp [X]
      rw [card_maynardAmbientCarrier_natCast]
    have hBprime :
        ((maynardCoprimeAmbientCarrier X).card : Real) =
          (2 / 5 : Real) * X := by
      have hratio := card_maynardCoprimeAmbientCarrier_powerTen_real_ratio
        (length := length) hlengthPos
      have hratioX :
          ((maynardCoprimeAmbientCarrier X).card : Real) =
            (Nat.totient 10 : Real) / 10 *
              ((maynardAmbientCarrier X).card : Real) := by
        simpa [X] using hratio
      rw [hBcard] at hratioX
      have htotient : Nat.totient 10 = 4 := by decide
      rw [htotient] at hratioX
      norm_num at hratioX ⊢
      exact hratioX
    have hRel :
        (5 / 2 : Real) * kappa = kappaA := by
      have hRat := five_halves_mul_typeIProgressionDensity digit
      have hCast := congrArg (fun r : Rat => (r : Real)) hRat
      simpa [kappa, kappaA] using hCast
    have hkappa : 0 <= kappa ∧ kappa <= 1 := by
      simpa [kappa] using sourceFundamental_typeIProgressionDensity_bounds digit
    have hkappaAnonneg : 0 <= kappaA := by
      dsimp [kappaA]
      rw [restrictedDigitDensity_eq]
      split_ifs <;> norm_num
    have hscaleNonneg : 0 <= scale := by
      dsimp [scale]
      exact div_nonneg (mul_nonneg hkappaAnonneg (by positivity)) hXpos.le
    have hscaleBprime :
        scale * ((maynardCoprimeAmbientCarrier X).card : Real) =
          kappa * (A.card : Real) := by
      dsimp [scale]
      rw [hBprime, ← hRel]
      field_simp [hXne]
    have hpointwise :
        ∀ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation A d.toPNat') (X ^ delta)).card : Real) -
              scale *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real)| <=
            |((strictSiftedCarrier
                (sieveDilation (A.filter (fun n => n.Coprime 10)) d.toPNat')
                (X ^ delta)).card : Real) -
              kappa * (A.card : Real) / (d : Real) * V| +
              scale *
                |((strictSiftedCarrier
                  (sieveDilation
                    (maynardCoprimeAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real) -
                  ((maynardCoprimeAmbientCarrier X).card : Real) /
                    (d : Real) * V| := by
      intro d hd
      have hdData : d ∈ maynardStrictRoughCarrier
          (X ^ (50 / 77 - epsilon)) (X ^ delta) := by
        simpa [D] using hd
      have hdTen : d.Coprime 10 :=
        maynardStrictRoughCarrier_mem_coprime_ten hcutoffX hdData
      have hdCoercion := sourceFundamental_toPNat'_coe_of_mem hdData
      have hdPNatTen : ((d.toPNat' : PNat) : Nat).Coprime 10 := by
        simpa [hdCoercion] using hdTen
      have hAeq :=
        strictSiftedCarrier_sieveDilation_filter_coprime_ten_eq
          A d.toPNat' hcutoffX hdPNatTen
      have hBeq :=
        strictSiftedCarrier_sieveDilation_filter_coprime_ten_eq
          B d.toPNat' hcutoffX hdPNatTen
      have hAeqCard := congrArg (fun S : Finset Nat => (S.card : Real)) hAeq
      have hBeqCard :
          ((strictSiftedCarrier
              (sieveDilation (maynardCoprimeAmbientCarrier X) d.toPNat')
              (X ^ delta)).card : Real) =
            ((strictSiftedCarrier
              (sieveDilation (maynardAmbientCarrier X) d.toPNat')
              (X ^ delta)).card : Real) := by
        simpa [B, maynardCoprimeAmbientCarrier] using
          congrArg (fun S : Finset Nat => (S.card : Real)) hBeq
      have hdPos : 0 < d := by
        exact lt_of_lt_of_le Nat.zero_lt_one
          (mem_maynardStrictRoughCarrier.mp hdData).1
      have hdNe : (d : Real) ≠ 0 := by positivity
      have hmain :
          kappa * (A.card : Real) / (d : Real) * V =
            scale * (((maynardCoprimeAmbientCarrier X).card : Real) /
              (d : Real) * V) := by
        calc
          kappa * (A.card : Real) / (d : Real) * V =
              (kappa * (A.card : Real)) /
                (d : Real) * V := by ring
          _ = (scale * ((maynardCoprimeAmbientCarrier X).card : Real)) /
                (d : Real) * V := by rw [hscaleBprime]
          _ = scale * (((maynardCoprimeAmbientCarrier X).card : Real) /
                (d : Real) * V) := by ring
      have htri := abs_sub_mul_le
        (((strictSiftedCarrier
            (sieveDilation (A.filter (fun n => n.Coprime 10)) d.toPNat')
            (X ^ delta)).card : Real))
        (((strictSiftedCarrier
            (sieveDilation
              (maynardCoprimeAmbientCarrier X) d.toPNat')
            (X ^ delta)).card : Real))
        (kappa * (A.card : Real) / (d : Real) * V)
        (((maynardCoprimeAmbientCarrier X).card : Real) /
          (d : Real) * V) scale hscaleNonneg hmain
      calc
        |((strictSiftedCarrier (sieveDilation A d.toPNat')
            (X ^ delta)).card : Real) -
              scale *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real)| =
            |((strictSiftedCarrier
                (sieveDilation (A.filter (fun n => n.Coprime 10)) d.toPNat')
                (X ^ delta)).card : Real) -
              scale *
                ((strictSiftedCarrier
                  (sieveDilation (maynardCoprimeAmbientCarrier X)
                    d.toPNat') (X ^ delta)).card : Real)| := by
              rw [hAeqCard, hBeqCard]
        _ <= _ := htri
    have hsumPointwise :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation A d.toPNat') (X ^ delta)).card : Real) -
              scale *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real)|) <=
          (∑ d ∈ D,
            |((strictSiftedCarrier
                (sieveDilation (A.filter (fun n => n.Coprime 10)) d.toPNat')
                (X ^ delta)).card : Real) -
              kappa * (A.card : Real) / (d : Real) * V|) +
            scale *
              (∑ d ∈ D,
                |((strictSiftedCarrier
                    (sieveDilation
                      (maynardCoprimeAmbientCarrier X) d.toPNat')
                    (X ^ delta)).card : Real) -
                  ((maynardCoprimeAmbientCarrier X).card : Real) /
                    (d : Real) * V|) := by
      calc
        _ <= ∑ d ∈ D,
            (|((strictSiftedCarrier
                (sieveDilation (A.filter (fun n => n.Coprime 10)) d.toPNat')
                (X ^ delta)).card : Real) -
              kappa * (A.card : Real) / (d : Real) * V| +
              scale *
                |((strictSiftedCarrier
                    (sieveDilation
                      (maynardCoprimeAmbientCarrier X) d.toPNat')
                    (X ^ delta)).card : Real) -
                  ((maynardCoprimeAmbientCarrier X).card : Real) /
                    (d : Real) * V|) := by
          apply Finset.sum_le_sum
          intro d hd
          exact hpointwise d hd
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hlog : 0 < Real.log X := Real.log_pos hXgt
    have hR : 0 <= R := by
      dsimp [R]
      positivity
    have hE : 0 <= E := by
      dsimp [E]
      positivity
    have hscaledAmbient :
        scale *
            (CAmbient * ((maynardCoprimeAmbientCarrier X).card : Real) * R +
              CAmbient * ((maynardCoprimeAmbientCarrier X).card : Real) * E) <=
          CAmbient * (A.card : Real) * R +
            CAmbient * (A.card : Real) * E := by
      have hnonneg :
          0 <= CAmbient * (A.card : Real) * R +
            CAmbient * (A.card : Real) * E := by
        positivity
      calc
        _ = (scale * ((maynardCoprimeAmbientCarrier X).card : Real)) *
              (CAmbient * R) +
            (scale * ((maynardCoprimeAmbientCarrier X).card : Real)) *
              (CAmbient * E) := by ring
        _ = (kappa * (A.card : Real)) * (CAmbient * R) +
              (kappa * (A.card : Real)) * (CAmbient * E) := by
          rw [hscaleBprime]
        _ = kappa *
              (CAmbient * (A.card : Real) * R +
                CAmbient * (A.card : Real) * E) := by ring
        _ <= 1 *
              (CAmbient * (A.card : Real) * R +
                CAmbient * (A.card : Real) * E) := by
          exact mul_le_mul_of_nonneg_right hkappa.2 hnonneg
        _ = _ := by ring
    have hsumBound := hsumPointwise.trans
      (add_le_add hsourceBound
        (mul_le_mul_of_nonneg_left hambientBound hscaleNonneg))
    have hlocal :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation A d.toPNat') (X ^ delta)).card : Real) -
              scale *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real)|) <=
          C * (A.card : Real) * R + C * (A.card : Real) * E := by
      calc
        _ <= (CSource * (A.card : Real) * R +
              CSource * (A.card : Real) * E) +
            scale *
              (CAmbient *
                    ((maynardCoprimeAmbientCarrier X).card : Real) * R +
                CAmbient *
                    ((maynardCoprimeAmbientCarrier X).card : Real) * E) :=
          hsumBound
        _ <= (CSource * (A.card : Real) * R +
              CSource * (A.card : Real) * E) +
            (CAmbient * (A.card : Real) * R +
              CAmbient * (A.card : Real) * E) := by
          exact add_le_add_right hscaledAmbient _
        _ = C * (A.card : Real) * R + C * (A.card : Real) * E := by
          dsimp [C]
          ring
    simpa [D, A, X, scale, kappaA, R, E, div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm] using hlocal

end

end PrimesRestrictedDigits
