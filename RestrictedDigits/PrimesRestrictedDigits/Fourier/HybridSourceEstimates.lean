import PrimesRestrictedDigits.Fourier.GridCircleSpacing
import PrimesRestrictedDigits.Fourier.HybridEstimate

/-!
# Source-facing hybrid estimates

These are the two conclusions of `MAYNARD-PRD-PUBLISHED`, Lemma 10.6, specialized from the
generic separated-family estimate. The literal source carriers retain their periodic numerator
endpoints.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The fixed-denominator hybrid estimate, including both source endpoints
`a = 0` and `a = q`. -/
theorem fixedDenominator_hybridEstimate
    (digit : Fin 10) (length q : Nat) (hq : 0 < q)
    {E : Real} (hE : 1 <= E) :
    (∑ a ∈ Finset.range (q + 1),
      alignedGridSum digit length E ((a : Real) / q)) <=
      hybridConstant *
        (((q : Real) * E) ^ largeSieveAlpha +
          (q : Real) * E *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
  classical
  let value (a : Nat) :=
    alignedGridSum digit length E ((a : Real) / q)
  let canonicalValue (a : Fin q) := value a.val
  let target : Real :=
    ((q : Real) * E) ^ largeSieveAlpha +
      (q : Real) * E *
        (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))
  have hqReal : (1 : Real) <= q := by
    exact_mod_cast hq
  have htarget : 0 <= target := by
    dsimp [target]
    positivity
  have hcanonical :
      (∑ a : Fin q, canonicalValue a) <=
        hybridSamplingConstant * target := by
    have hsample := sum_alignedGridSum_hybridEstimate
      (Finset.univ : Finset (Fin q)) digit length
      (fun a : Fin q => (a.val : Real) / q) hqReal hE
      (by
        intro a ha
        rw [Set.mem_Icc]
        constructor
        · positivity
        · apply (div_le_one (by positivity : (0 : Real) < q)).mpr
          exact_mod_cast a.isLt.le)
      (by
        intro a ha b hb hab
        exact one_div_natCast_le_dist_fin_div hq hab)
    simpa only [canonicalValue, value, target] using hsample
  have hendpoint :
      alignedGridSum digit length E 1 <=
        hybridSamplingConstant * target := by
    have hsample := sum_alignedGridSum_hybridEstimate
      (Finset.univ : Finset (Fin 1)) digit length
      (fun _ : Fin 1 => (1 : Real)) hqReal hE
      (by simp)
      (by
        intro a ha b hb hab
        exact (hab (Subsingleton.elim a b)).elim)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_one, one_nsmul, one_mul, target] using hsample
  have hendpointValue : value q = alignedGridSum digit length E 1 := by
    have hqNe : (q : Real) ≠ 0 := by
      exact_mod_cast hq.ne'
    simp only [value, div_self hqNe]
  have hsourceIdentity :
      (∑ a ∈ Finset.range (q + 1), value a) =
        (∑ a : Fin q, canonicalValue a) +
          alignedGridSum digit length E 1 := by
    rw [Finset.sum_range_succ, hendpointValue]
    congr 1
    simpa only [canonicalValue] using
      (Fin.sum_univ_eq_sum_range value q).symm
  change (∑ a ∈ Finset.range (q + 1), value a) <=
    hybridConstant * target
  rw [hsourceIdentity]
  unfold hybridSamplingConstant at hcanonical hendpoint
  unfold hybridConstant
  nlinarith

/-- The strict divisible-denominator hybrid estimate on the literal source
carrier. The two exceptional coprime endpoints at denominator one are
retained and bounded separately. -/
theorem divisibleDenominators_hybridEstimate
    (digit : Fin 10) (length d : Nat) (hd : 0 < d)
    {Q : Real} (hQ : 1 <= Q) {E : Real} (hE : 1 <= E) :
    (∑ pair ∈ strictDivisibleReducedFractionSourceCarrier Q d,
      alignedGridSum digit length E
        ((pair.2 : Real) / (pair.1 : Real))) <=
      hybridConstant *
        ((((Q ^ 2 / d) * E) ^ largeSieveAlpha) +
          (Q ^ 2 / d) * E *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
  classical
  let source := strictDivisibleReducedFractionSourceCarrier Q d
  let carrier := strictDivisibleReducedFractionCarrier Q d
  let endpoints : Finset (Nat × Nat) := {(1, 0), (1, 1)}
  let value (pair : Nat × Nat) :=
    alignedGridSum digit length E
      ((pair.2 : Real) / (pair.1 : Real))
  let L : Real := Q ^ 2 / d
  let target : Real :=
    (L * E) ^ largeSieveAlpha +
      L * E * (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hdReal : 0 < (d : Real) := by
    exact_mod_cast hd
  have hL0 : 0 < L := by
    dsimp [L]
    positivity
  have htarget : 0 <= target := by
    dsimp [target]
    positivity
  change (∑ pair ∈ source, value pair) <= hybridConstant * target
  rcases source.eq_empty_or_nonempty with hempty | hnonempty
  · rw [hempty]
    simp only [Finset.sum_empty]
    exact mul_nonneg (by unfold hybridConstant; norm_num) htarget
  · obtain ⟨witness, hwitness⟩ := hnonempty
    rcases mem_strictDivisibleReducedFractionSourceCarrier_iff.mp hwitness with
      ⟨hqOne, hqFloor, hqStrict, hdvd, haLe, hcoprime⟩
    have hqPos : 0 < witness.1 :=
      lt_of_lt_of_le Nat.zero_lt_one hqOne
    have hdq : d <= witness.1 := Nat.le_of_dvd hqPos hdvd
    have hdQ : (d : Real) <= Q :=
      (by exact_mod_cast hdq : (d : Real) <= witness.1).trans hqStrict.le
    have hL : 1 <= L := by
      dsimp [L]
      apply (le_div_iff₀ hdReal).mpr
      calc
        (1 : Real) * d = (d : Real) := by ring
        _ <= Q := hdQ
        _ <= Q * Q := by nlinarith
        _ = Q ^ 2 := by ring
    have hcanonical :
        (∑ pair ∈ carrier, value pair) <=
          hybridSamplingConstant * target := by
      have hsample := sum_alignedGridSum_hybridEstimate
        carrier digit length reducedFractionValue hL hE
        (by
          intro pair hpair
          have hred :=
            (mem_strictDivisibleReducedFractionCarrier_iff.mp hpair).1
          have hmem := mem_reducedFractionCarrier_iff.mp hred
          rw [Set.mem_Icc]
          dsimp [reducedFractionValue]
          constructor
          · positivity
          · apply (div_le_one (by
                exact_mod_cast
                  (lt_of_lt_of_le Nat.zero_lt_one hmem.1) :
                    (0 : Real) < pair.1)).mpr
            exact_mod_cast hmem.2.2.2.1.le)
        (by
          intro left hleft right hright hne
          have hleftData :=
            mem_strictDivisibleReducedFractionCarrier_iff.mp hleft
          have hrightData :=
            mem_strictDivisibleReducedFractionCarrier_iff.mp hright
          have hspacing :=
            natCast_div_sq_le_dist_divisibleReducedFractionValue
              hd hQ0
              (mem_divisibleReducedFractionCarrier_iff.mpr
                ⟨hleftData.1, hleftData.2.1⟩)
              (mem_divisibleReducedFractionCarrier_iff.mpr
                ⟨hrightData.1, hrightData.2.1⟩)
              (Nat.floor_le hQ0.le) hne
          have hreciprocal : 1 / L = (d : Real) / Q ^ 2 := by
            dsimp [L]
            field_simp
          rw [hreciprocal]
          exact hspacing)
      simpa only [carrier, value, reducedFractionValue, target] using hsample
    have hsingleton (x : Real) (hx : x ∈ Set.Icc (0 : Real) 1) :
        alignedGridSum digit length E x <=
          hybridSamplingConstant * target := by
      have hsample := sum_alignedGridSum_hybridEstimate
        (Finset.univ : Finset (Fin 1)) digit length
        (fun _ : Fin 1 => x) hL hE
        (by
          intro a ha
          exact hx)
        (by
          intro a ha b hb hab
          exact (hab (Subsingleton.elim a b)).elim)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_one, one_nsmul, one_mul, target] using hsample
    have hzero : value (1, 0) <= hybridSamplingConstant * target := by
      simpa only [value, Nat.cast_zero, Nat.cast_one, zero_div] using
        hsingleton 0 (by norm_num)
    have hone : value (1, 1) <= hybridSamplingConstant * target := by
      simpa only [value, Nat.cast_one, div_one] using
        hsingleton 1 (by norm_num)
    have hsourceSubset : source ⊆ carrier ∪ endpoints := by
      intro pair hpair
      rcases mem_strictDivisibleReducedFractionSourceCarrier_iff.mp hpair with
        ⟨hqOne', hqFloor', hqStrict', hdvd', haLe', hcoprime'⟩
      by_cases haZero : pair.2 = 0
      · have hqEq : pair.1 = 1 := by
          have hcoprimeZero : Nat.Coprime 0 pair.1 := by
            simpa only [haZero] using hcoprime'
          exact (Nat.coprime_zero_left pair.1).mp hcoprimeZero
        have hpairEq : pair = (1, 0) := by
          apply Prod.ext
          · exact hqEq
          · exact haZero
        apply Finset.mem_union.mpr
        exact Or.inr (by simp [endpoints, hpairEq])
      · by_cases haStrict : pair.2 < pair.1
        · apply Finset.mem_union.mpr
          apply Or.inl
          apply mem_strictDivisibleReducedFractionCarrier_iff.mpr
          exact ⟨mem_reducedFractionCarrier_iff.mpr
            ⟨hqOne', hqFloor', Nat.pos_of_ne_zero haZero,
              haStrict, hcoprime'⟩, hdvd', hqStrict'⟩
        · have haEq : pair.2 = pair.1 :=
            Nat.le_antisymm haLe' (Nat.le_of_not_gt haStrict)
          have hqEq : pair.1 = 1 := by
            have hcoprimeSelf : pair.1.Coprime pair.1 := by
              simpa only [haEq] using hcoprime'
            simpa only [Nat.coprime_self] using hcoprimeSelf
          have hpairEq : pair = (1, 1) := by
            apply Prod.ext
            · exact hqEq
            · exact haEq.trans hqEq
          apply Finset.mem_union.mpr
          exact Or.inr (by simp [endpoints, hpairEq])
    have hsourceSum :
        (∑ pair ∈ source, value pair) <=
          ∑ pair ∈ carrier ∪ endpoints, value pair := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsourceSubset
      intro pair hpair hnotSource
      dsimp [value]
      exact alignedGridSum_nonneg digit length E _
    have hunionSum :
        (∑ pair ∈ carrier ∪ endpoints, value pair) <=
          (∑ pair ∈ carrier, value pair) +
            value (1, 0) + value (1, 1) := by
      calc
        (∑ pair ∈ carrier ∪ endpoints, value pair) =
            (∑ pair ∈ carrier, value pair) +
              ∑ pair ∈ endpoints \ carrier, value pair := by
          rw [← Finset.union_sdiff_self_eq_union (s := carrier) (t := endpoints),
            Finset.sum_union Finset.disjoint_sdiff]
        _ <= (∑ pair ∈ carrier, value pair) +
            ∑ pair ∈ endpoints, value pair := by
          have hdifference :
              (∑ pair ∈ endpoints \ carrier, value pair) <=
                ∑ pair ∈ endpoints, value pair := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (s := endpoints \ carrier) (t := endpoints) (f := value)
              Finset.sdiff_subset
            intro pair hpair hnotDifference
            dsimp [value]
            exact alignedGridSum_nonneg digit length E _
          exact add_le_add le_rfl hdifference
        _ = (∑ pair ∈ carrier, value pair) +
            value (1, 0) + value (1, 1) := by
          rw [show endpoints = {(1, 0), (1, 1)} by rfl,
            Finset.sum_pair (by decide)]
          ring
    calc
      (∑ pair ∈ source, value pair) <=
          ∑ pair ∈ carrier ∪ endpoints, value pair := hsourceSum
      _ <= (∑ pair ∈ carrier, value pair) +
          value (1, 0) + value (1, 1) := hunionSum
      _ <= hybridConstant * target := by
        unfold hybridSamplingConstant at hcanonical hzero hone
        unfold hybridConstant
        nlinarith

end

end PrimesRestrictedDigits
