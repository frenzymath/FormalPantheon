import PrimesRestrictedDigits.SieveAsymptotics.FundamentalRemainderBridge
import PrimesRestrictedDigits.SieveDecomposition.SectionSixPrimeRecurrence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Repeated weak states charged at the repeated prime square

This file supplies the finite carrier bridge needed after the corrected Proposition 6.1
recurrence. A weak twice-dilated state is controlled at the repeated prime square `q^2`; the
full state modulus is deliberately not used. The quantitative multiplicity and Type-I
summation theorem remain downstream.
-/

namespace PrimesRestrictedDigits

noncomputable section

open scoped BigOperators

/-- A weakly `q`-rough natural is coprime to ten once the threshold is above
five.  The strict rough lemma is reused after lowering the threshold to five.
-/
theorem weakRoughPredicate_coprime_ten_of_five_lt
    {z : Real} (hz : 5 < z) {n : Nat}
    (hn : weakRoughPredicate z n) : n.Coprime 10 := by
  apply strictRoughPredicate_coprime_ten (z := 5) (by norm_num)
  intro p hp hpd
  exact lt_of_lt_of_le hz (hn p hp hpd)

private theorem prime_coprime_ten_of_five_lt
    {q : Nat} (hq : q.Prime) (hqFive : 5 < (q : Real)) :
    q.Coprime 10 := by
  apply strictRoughPredicate_coprime_ten (z := 5) (by norm_num)
  intro p hp hpd
  rcases (Nat.dvd_prime hq).mp hpd with hpOne | hpEq
  · exact (hp.ne_one hpOne).elim
  · subst p
    exact hqFive

private theorem repeatedSquare_modulus_coe
    (d : PNat) {q : Nat} (hq : q.Prime) :
    (((d * Nat.toPNat' q) * Nat.toPNat' q : PNat) : Nat) =
      (d : Nat) * q * q := by
  rw [PNat.mul_coe, PNat.mul_coe, Nat.toPNat'_coe, if_pos hq.pos]

/-! The restricted image of a repeated state lies in the square progression
carrier.  This is an inclusion, not an equality: roughness and the outer
modulus impose additional conditions.
-/
theorem card_sectionSixRepeatedRestricted_le_squareProgression
    (A : Finset Nat) (d : PNat) {q : Nat} (hq : q.Prime)
    {z : Real} (hz : 5 < z) (hqz : z < (q : Real))
    (hd : (d : Nat).Coprime 10) :
    (weakSiftedCarrier
        (sieveDilation A ((d * Nat.toPNat' q) * Nat.toPNat' q))
        (q : Real)).card ≤
      (A.filter (fun n => q * q ∣ n ∧ n.Coprime 10)).card := by
  classical
  let D : PNat := (d * Nat.toPNat' q) * Nat.toPNat' q
  let f : Nat ↪ Nat :=
    ⟨fun m => m * (D : Nat),
      mul_left_injective₀ (PNat.ne_zero D)⟩
  have hD : (D : Nat) = (d : Nat) * q * q := by
    dsimp only [D]
    exact repeatedSquare_modulus_coe d hq
  have hqFive : (5 : Real) < (q : Real) := hz.trans hqz
  have hqTen : q.Coprime 10 := prime_coprime_ten_of_five_lt hq hqFive
  have hsubset :
      (weakSiftedCarrier (sieveDilation A D) (q : Real)).map f ⊆
        A.filter (fun n => q * q ∣ n ∧ n.Coprime 10) := by
    intro n hn
    rcases Finset.mem_map.mp hn with ⟨m, hm, rfl⟩
    have hmData := mem_weakSiftedCarrier.mp hm
    have hmA : m * (D : Nat) ∈ A := mem_sieveDilation.mp hmData.1
    have hmTen : m.Coprime 10 :=
      weakRoughPredicate_coprime_ten_of_five_lt hqFive hmData.2
    have hqSqTen : (q * q).Coprime 10 := by
      simpa only [pow_two] using hqTen.pow_left 2
    have hmdTen : (m * (d : Nat)).Coprime 10 := hmTen.mul_left hd
    have htotalTen :
        (m * (d : Nat) * (q * q)).Coprime 10 :=
      hmdTen.mul_left hqSqTen
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · change m * (D : Nat) ∈ A
      exact hmA
    · refine ⟨m * (d : Nat), ?_⟩
      change m * (D : Nat) = q * q * (m * (d : Nat))
      rw [hD]
      ring
    · change (m * (D : Nat)).Coprime 10
      rw [hD]
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using htotalTen
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_map] at hcard
  exact hcard

/-- The ambient repeated state has at most `X/q^2` elements.  Positivity of
the weakly rough cofactor removes the zero multiple, so the strict ambient
endpoint is represented exactly by `(X-1)/q^2`. -/
theorem card_sectionSixRepeatedAmbient_le_squareQuotient
    (length : Nat) (d : PNat) {q : Nat} (hq : q.Prime)
    {z : Real} (hz : 5 < z) (hqz : z < (q : Real)) :
    ((weakSiftedCarrier
        (sieveDilation (maynardAmbientCarrier
          ((10 ^ length : Nat) : Real))
          ((d * Nat.toPNat' q) * Nat.toPNat' q))
        (q : Real)).card : Real) ≤
      ((10 ^ length : Nat) : Real) / (q * q : Nat) := by
  classical
  let XNat : Nat := 10 ^ length
  let D : PNat := (d * Nat.toPNat' q) * Nat.toPNat' q
  let upper : Nat := (XNat - 1) / (q * q)
  let f : Nat ↪ Nat :=
    ⟨fun m => m * (d : Nat),
      mul_left_injective₀ (PNat.ne_zero d)⟩
  have hD : (D : Nat) = (d : Nat) * q * q := by
    dsimp only [D]
    exact repeatedSquare_modulus_coe d hq
  have hqFive : (5 : Real) < (q : Real) := hz.trans hqz
  have hqSqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hsubset :
      (weakSiftedCarrier
        (sieveDilation (maynardAmbientCarrier (XNat : Real)) D)
          (q : Real)).map f ⊆ Finset.Icc 1 upper := by
    intro k hk
    rcases Finset.mem_map.mp hk with ⟨m, hm, rfl⟩
    have hmData := mem_weakSiftedCarrier.mp hm
    have hmAmbient := mem_sieveDilation.mp hmData.1
    have hm0 : m ≠ 0 := by
      intro hmZero
      subst m
      have hzero := weakRoughPredicate_zero.mp hmData.2
      linarith
    have hmdPos : 0 < m * (d : Nat) :=
      Nat.mul_pos (Nat.pos_of_ne_zero hm0) d.pos
    have htotalReal :
        ((m * (D : Nat) : Nat) : Real) < (XNat : Real) :=
      mem_maynardAmbientCarrier.mp hmAmbient
    have htotal : m * (D : Nat) < XNat := by
      exact_mod_cast htotalReal
    have hproduct : (m * (d : Nat)) * (q * q) < XNat := by
      rw [hD] at htotal
      simpa [Nat.mul_assoc] using htotal
    have hlePred : (m * (d : Nat)) * (q * q) ≤ XNat - 1 :=
      Nat.le_sub_one_of_lt hproduct
    have hupper : m * (d : Nat) ≤ upper := by
      dsimp only [upper]
      exact (Nat.le_div_iff_mul_le hqSqPos).2 hlePred
    exact Finset.mem_Icc.mpr ⟨hmdPos, hupper⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_map, Nat.card_Icc] at hcard
  have hcardUpper :
      (weakSiftedCarrier
        (sieveDilation (maynardAmbientCarrier (XNat : Real)) D)
          (q : Real)).card ≤ upper := by
    simpa only [Nat.add_sub_cancel] using hcard
  have hupperDiv : upper ≤ XNat / (q * q) := by
    dsimp only [upper]
    exact Nat.div_le_div_right (Nat.sub_le XNat 1)
  have hcardDiv :
      (weakSiftedCarrier
        (sieveDilation (maynardAmbientCarrier (XNat : Real)) D)
          (q : Real)).card ≤ XNat / (q * q) :=
    hcardUpper.trans hupperDiv
  have hcardCast :
      ((weakSiftedCarrier
        (sieveDilation (maynardAmbientCarrier (XNat : Real)) D)
          (q : Real)).card : Real) ≤ ((XNat / (q * q) : Nat) : Real) := by
    exact_mod_cast hcardDiv
  exact hcardCast.trans Nat.cast_div_le

/-! A generic finite charge inequality.  The caller supplies the ambient
positive-multiple cardinality bound and the progression error; this keeps the
analytic Type-I input explicit and prevents an abstract hypothesis from
reaching the final theorem unnoticed.
-/
theorem abs_sectionSixWeakSiftedSum_le_of_squareProgression
    (digit : Fin 10) (length : Nat) (d : PNat) {q : Nat}
    (hq : q.Prime) {z : Real} (hz : 5 < z) (hqz : z < (q : Real))
    (hd : (d : Nat).Coprime 10)
    (hambient :
      ((weakSiftedCarrier
          (sieveDilation (maynardAmbientCarrier
            ((10 ^ length : Nat) : Real))
            ((d * Nat.toPNat' q) * Nat.toPNat' q))
          (q : Real)).card : Real) ≤
        ((10 ^ length : Nat) : Real) / (q * q : Nat)) :
    |sectionSixWeakSiftedSum digit length
        ((d * Nat.toPNat' q) * Nat.toPNat' q) (q : Real)| ≤
      |realTypeIProgressionError digit length (q * q)| +
      ((typeIProgressionDensity digit : Real) +
        (restrictedDigitDensity digit : Real)) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            (q * q : Real) := by
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let X : Real := ((10 ^ length : Nat) : Real)
  let D : PNat := (d * Nat.toPNat' q) * Nat.toPNat' q
  have hrestricted := card_sectionSixRepeatedRestricted_le_squareProgression
    A d hq hz hqz hd
  have hrestrictedReal :
      ((weakSiftedCarrier (sieveDilation A D) (q : Real)).card : Real) ≤
        (((A.filter (fun n => q * q ∣ n ∧ n.Coprime 10)).card : Nat) : Real) := by
    exact_mod_cast hrestricted
  have hcountEq := sectionSixWeakSiftedSum_eq_card_sub_density_mul_card
    digit length D (q : Real)
  let kappaProg : Real := typeIProgressionDensity digit
  let kappaA : Real := restrictedDigitDensity digit
  have herror :
      (((A.filter (fun n => q * q ∣ n ∧ n.Coprime 10)).card : Nat) : Real) =
        kappaProg * (A.card : Real) / (q * q : Real) +
          realTypeIProgressionError digit length (q * q) := by
    rw [realTypeIProgressionError]
    dsimp only [A, kappaProg]
    push_cast
    ring
  have hkappaProg : 0 ≤ kappaProg := by
    dsimp only [kappaProg]
    rw [typeIProgressionDensity_eq]
    split_ifs <;> norm_num
  have hkappaA : 0 ≤ kappaA := by
    dsimp only [kappaA]
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  have hmainNonneg : 0 ≤ kappaProg * (A.card : Real) / (q * q : Real) := by
    positivity
  have hrestrictedBound :
      ((weakSiftedCarrier (sieveDilation A D) (q : Real)).card : Real) ≤
        kappaProg * (A.card : Real) / (q * q : Real) +
          |realTypeIProgressionError digit length (q * q)| := by
    calc
      _ ≤ (((A.filter (fun n => q * q ∣ n ∧ n.Coprime 10)).card : Nat) : Real) :=
        hrestrictedReal
      _ = kappaProg * (A.card : Real) / (q * q : Real) +
          realTypeIProgressionError digit length (q * q) := herror
      _ ≤ kappaProg * (A.card : Real) / (q * q : Real) +
          |realTypeIProgressionError digit length (q * q)| := by
        gcongr
        exact le_abs_self _
  have hambient' :
      ((weakSiftedCarrier (sieveDilation
          (maynardAmbientCarrier X) D) (q : Real)).card : Real) ≤
        X / (q * q : Nat) := by
    simpa only [X, D] using hambient
  have hsumEq :
      sectionSixWeakSiftedSum digit length D (q : Real) =
        ((weakSiftedCarrier (sieveDilation A D) (q : Real)).card : Real) -
          kappaA * ((A.card : Real) / X) *
            ((weakSiftedCarrier (sieveDilation
              (maynardAmbientCarrier X) D) (q : Real)).card : Real) := by
    simpa only [A, X, D, kappaA] using hcountEq
  rw [hsumEq]
  have hlambdaNonneg : 0 ≤ kappaA * ((A.card : Real) / X) := by positivity
  have hambientTerm :
      kappaA * ((A.card : Real) / X) *
          ((weakSiftedCarrier (sieveDilation
            (maynardAmbientCarrier X) D) (q : Real)).card : Real) ≤
        kappaA * (A.card : Real) / (q * q : Real) := by
    calc
      _ ≤ kappaA * ((A.card : Real) / X) * (X / (q * q : Nat)) := by
        gcongr
      _ = kappaA * (A.card : Real) / (q * q : Real) := by
        have hX : X ≠ 0 := by positivity
        push_cast
        field_simp
  have hrestrictedNonneg :
      0 ≤ ((weakSiftedCarrier (sieveDilation A D) (q : Real)).card : Real) := by
    positivity
  have hambientNonneg :
      0 ≤ kappaA * ((A.card : Real) / X) *
        ((weakSiftedCarrier (sieveDilation
          (maynardAmbientCarrier X) D) (q : Real)).card : Real) := by
    positivity
  calc
    |(weakSiftedCarrier (sieveDilation A D) (q : Real)).card -
        kappaA * ((A.card : Real) / X) *
          (weakSiftedCarrier (sieveDilation (maynardAmbientCarrier X) D)
            (q : Real)).card| ≤
        ((weakSiftedCarrier (sieveDilation A D) (q : Real)).card : Real) +
          kappaA * ((A.card : Real) / X) *
            ((weakSiftedCarrier (sieveDilation (maynardAmbientCarrier X) D)
              (q : Real)).card : Real) := by
      calc
        _ ≤ |((weakSiftedCarrier (sieveDilation A D)
            (q : Real)).card : Real)| +
            |kappaA * ((A.card : Real) / X) *
              ((weakSiftedCarrier (sieveDilation
                (maynardAmbientCarrier X) D) (q : Real)).card : Real)| :=
          abs_sub _ _
        _ = _ := by
          rw [abs_of_nonneg hrestrictedNonneg,
            abs_of_nonneg hambientNonneg]
    _ ≤ (kappaProg * (A.card : Real) / (q * q : Real) +
          |realTypeIProgressionError digit length (q * q)|) +
          kappaA * (A.card : Real) / (q * q : Real) := by
      exact add_le_add hrestrictedBound hambientTerm
    _ = |realTypeIProgressionError digit length (q * q)| +
        (kappaProg + kappaA) * (A.card : Real) / (q * q : Real) := by ring

/-- The unconditional finite repeated-state charge at the repeated square.
The remaining summation over states is a separate multiplicity problem. -/
theorem abs_sectionSixWeakSiftedSum_le_repeatedSquare
    (digit : Fin 10) (length : Nat) (d : PNat) {q : Nat}
    (hq : q.Prime) {z : Real} (hz : 5 < z) (hqz : z < (q : Real))
    (hd : (d : Nat).Coprime 10) :
    |sectionSixWeakSiftedSum digit length
        ((d * Nat.toPNat' q) * Nat.toPNat' q) (q : Real)| ≤
      |realTypeIProgressionError digit length (q * q)| +
      ((typeIProgressionDensity digit : Real) +
        (restrictedDigitDensity digit : Real)) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            (q * q : Real) := by
  exact abs_sectionSixWeakSiftedSum_le_of_squareProgression
    digit length d hq hz hqz hd
      (card_sectionSixRepeatedAmbient_le_squareQuotient
        length d hq hz hqz)

/-- An injective family of prime squares is a subfamily of the Type I modulus
carrier once every square lies below its strict real cutoff. -/
theorem sum_abs_realTypeIProgressionError_primeSquares_le
    (digit : Fin 10) (length : Nat) (P : Finset Nat) (Q : Real)
    (hcoprime : ∀ q, q ∈ P → q.Coprime 10)
    (hcutoff : ∀ q, q ∈ P → ((q * q : Nat) : Real) < Q) :
    (∑ q ∈ P, |realTypeIProgressionError digit length (q * q)|) ≤
      ∑ r ∈ typeIModuliBelow Q,
        |realTypeIProgressionError digit length r| := by
  classical
  let square : Nat → Nat := fun q => q * q
  let squares : Finset Nat := P.image square
  have hsquareInj : Function.Injective square := by
    intro q r hqr
    apply Nat.pow_left_injective (n := 2) (by norm_num)
    simpa only [square, pow_two] using hqr
  have hsubset : squares ⊆ typeIModuliBelow Q := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨q, hqP, rfl⟩
    change q * q ∈ typeIModuliBelow Q
    rw [typeIModuliBelow, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · rw [Nat.lt_ceil]
      exact hcutoff q hqP
    · have hqSqTen := (hcoprime q hqP).pow_left 2
      simpa only [pow_two] using hqSqTen
  have hsumImage :
      (∑ r ∈ squares,
          |realTypeIProgressionError digit length r|) =
        ∑ q ∈ P,
          |realTypeIProgressionError digit length (q * q)| := by
    dsimp only [squares]
    exact Finset.sum_image hsquareInj.injOn
  calc
    (∑ q ∈ P, |realTypeIProgressionError digit length (q * q)|) =
        ∑ r ∈ squares,
          |realTypeIProgressionError digit length r| := hsumImage.symm
    _ ≤ ∑ r ∈ typeIModuliBelow Q,
        |realTypeIProgressionError digit length r| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r hr _ => abs_nonneg _)

/-- Prime squares from one source interval satisfy the preceding reindex once
the cutoff inequality is supplied.  The strict lower endpoint above five
proves decimal coprimality. -/
theorem sum_abs_realTypeIProgressionError_sievePrimeSquares_le
    (digit : Fin 10) (length : Nat) {z1 z2 Q : Real}
    (hz1 : 5 < z1)
    (hcutoff : ∀ q, q ∈ sievePrimeInterval z1 z2 →
      ((q * q : Nat) : Real) < Q) :
    (∑ q ∈ sievePrimeInterval z1 z2,
        |realTypeIProgressionError digit length (q * q)|) ≤
      ∑ r ∈ typeIModuliBelow Q,
        |realTypeIProgressionError digit length r| := by
  apply sum_abs_realTypeIProgressionError_primeSquares_le
  · intro q hq
    have hqData := mem_sievePrimeInterval.mp hq
    exact prime_coprime_ten_of_five_lt hqData.1
      (hz1.trans hqData.2.1)
  · exact hcutoff

end

end PrimesRestrictedDigits
