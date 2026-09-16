import PrimesRestrictedDigits.TypeI.ProgressionError
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Harmonic aggregation for the Type I error

This implements the exact `q = q' * q''` reindex in the proof of published Proposition 7.1 and
then bounds the relaxed `q''` sum harmonically.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Positive natural moduli below the strict real cutoff and coprime to ten.
The positivity follows from the coprimality filter. -/
noncomputable def typeIModuliBelow (Q : Real) : Finset Nat :=
  (Finset.range (Nat.ceil Q)).filter (fun q => Nat.Coprime q 10)

/-- The reduced-numerator Fourier mass at fixed decimal and nondecimal
denominator parts. -/
noncomputable def typeIReducedFrequencyMass
    (digit : Fin 10) (length d q : Nat) : Real :=
  ∑ b ∈ (Finset.range (d * q)).filter
      (fun b => Nat.Coprime b (d * q)),
    normalizedPaddedDigitFourierMagnitudeAt digit length
      ((b : Real) / ((d * q : Nat) : Real))

private def typeIDivisorPairCarrier (Q : Nat) : Finset (Nat × Nat) :=
  ((Finset.range Q).product (Finset.range Q)).filter fun pair =>
    pair.1.Coprime 10 ∧ 1 < pair.2 ∧ pair.2 ∣ pair.1

private def typeIProductPairCarrier (Q : Nat) : Finset (Nat × Nat) :=
  ((Finset.range Q).product (Finset.range Q)).filter fun pair =>
    1 < pair.1 ∧ 0 < pair.2 ∧ pair.1 * pair.2 < Q ∧
      pair.1.Coprime 10 ∧ pair.2.Coprime 10

private theorem typeIDivisorPairCarrier_mem {Q : Nat} {q q' : Nat}
    (h : (q, q') ∈ typeIDivisorPairCarrier Q) :
    q < Q ∧ q' < Q ∧ q.Coprime 10 ∧ 1 < q' ∧ q' ∣ q := by
  rcases Finset.mem_filter.mp h with ⟨hproduct, hconditions⟩
  rcases Finset.mem_product.mp hproduct with ⟨hqQ, hq'Q⟩
  exact ⟨Finset.mem_range.mp hqQ, Finset.mem_range.mp hq'Q,
    hconditions.1, hconditions.2.1, hconditions.2.2⟩

private theorem typeIProductPairCarrier_mem {Q : Nat} {q' q'' : Nat}
    (h : (q', q'') ∈ typeIProductPairCarrier Q) :
    q' < Q ∧ q'' < Q ∧ 1 < q' ∧ 0 < q'' ∧ q' * q'' < Q ∧
      q'.Coprime 10 ∧ q''.Coprime 10 := by
  rcases Finset.mem_filter.mp h with ⟨hproduct, hconditions⟩
  rcases Finset.mem_product.mp hproduct with ⟨hq'Q, hq''Q⟩
  exact ⟨Finset.mem_range.mp hq'Q, Finset.mem_range.mp hq''Q,
    hconditions.1, hconditions.2.1, hconditions.2.2.1,
    hconditions.2.2.2.1, hconditions.2.2.2.2⟩

private theorem sum_typeIDivisorPairCarrier_eq_productPairCarrier
    (Q : Nat) (f : Nat → Real) :
    (∑ pair ∈ typeIDivisorPairCarrier Q,
      (1 / (pair.1 : Real)) * f pair.2) =
    ∑ pair ∈ typeIProductPairCarrier Q,
      (1 / (pair.1 : Real)) * (1 / (pair.2 : Real)) * f pair.1 := by
  classical
  refine Finset.sum_bij'
    (i := fun pair _ => (pair.2, pair.1 / pair.2))
    (j := fun pair _ => (pair.1 * pair.2, pair.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, q'⟩ h
    rcases typeIDivisorPairCarrier_mem h with
      ⟨hqQ, hq'Q, hq10, hq', hdiv⟩
    have hq'Pos : 0 < q' := by omega
    have hq0 : q ≠ 0 := by
      intro hqZero
      subst q
      norm_num [Nat.Coprime] at hq10
    have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
    have hquotPos : 0 < q / q' :=
      Nat.div_pos (Nat.le_of_dvd hqPos hdiv) hq'Pos
    have hmul : q' * (q / q') = q := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
    have hcop := Nat.coprime_mul_iff_left.mp (hmul.symm ▸ hq10)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hq'Q,
      Finset.mem_range.mpr ((Nat.div_le_self q q').trans_lt hqQ)⟩,
      hq', hquotPos, ?_, hcop.1, hcop.2⟩
    simpa [hmul] using hqQ
  · rintro ⟨q', q''⟩ h
    rcases typeIProductPairCarrier_mem h with
      ⟨hq'Q, hq''Q, hq', hq''Pos, hprodQ, hq'10, hq''10⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hprodQ,
      Finset.mem_range.mpr hq'Q⟩, ?_, hq', dvd_mul_right q' q''⟩
    exact Nat.coprime_mul_iff_left.mpr ⟨hq'10, hq''10⟩
  · rintro ⟨q, q'⟩ h
    rcases typeIDivisorPairCarrier_mem h with ⟨_, _, _, hq', hdiv⟩
    have hq'Pos : 0 < q' := by omega
    simp only [Prod.mk.injEq, and_true]
    rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
  · rintro ⟨q', q''⟩ h
    rcases typeIProductPairCarrier_mem h with ⟨_, _, hq', _, _, _, _⟩
    have hq'Pos : 0 < q' := by omega
    simp only [Prod.mk.injEq, true_and]
    exact Nat.mul_div_cancel_left q'' hq'Pos
  · rintro ⟨q, q'⟩ h
    rcases typeIDivisorPairCarrier_mem h with ⟨_, _, hq10, hq', hdiv⟩
    have hq'Pos : 0 < q' := by omega
    have hq0 : q ≠ 0 := by
      intro hqZero
      subst q
      norm_num [Nat.Coprime] at hq10
    have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
    have hquotPos : 0 < q / q' :=
      Nat.div_pos (Nat.le_of_dvd hqPos hdiv) hq'Pos
    have hmul : q' * (q / q') = q := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
    have hmulReal : (q : Real) = (q' : Real) * (q / q' : Nat) := by
      exact_mod_cast hmul.symm
    rw [hmulReal]
    field_simp

private theorem sum_typeIDivisorPairCarrier_eq_nested
    (Q : Nat) (f : Nat → Real) :
    (∑ pair ∈ typeIDivisorPairCarrier Q,
      (1 / (pair.1 : Real)) * f pair.2) =
    ∑ q ∈ (Finset.range Q).filter (fun q => q.Coprime 10),
      (1 / (q : Real)) *
        ∑ q' ∈ q.divisors.filter (fun q' => 1 < q'), f q' := by
  classical
  rw [typeIDivisorPairCarrier, Finset.sum_filter]
  refine (Finset.sum_product (Finset.range Q) (Finset.range Q)
    (fun pair : Nat × Nat =>
      if pair.1.Coprime 10 ∧ 1 < pair.2 ∧ pair.2 ∣ pair.1 then
        (1 / (pair.1 : Real)) * f pair.2 else 0)).trans ?_
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hqQ
  by_cases hq10 : q.Coprime 10
  · have hcondition (x : Nat) :
        (q.Coprime 10 ∧ 1 < x ∧ x ∣ q) ↔ (1 < x ∧ x ∣ q) :=
      ⟨fun h => h.2, fun h => ⟨hq10, h⟩⟩
    simp_rw [hcondition]
    rw [if_pos hq10, Finset.mul_sum]
    change (∑ x ∈ Finset.range Q,
      if 1 < x ∧ x ∣ q then (1 / (q : Real)) * f x else 0) =
      ∑ i ∈ q.divisors.filter (fun i => 1 < i),
        (1 / (q : Real)) * f i
    rw [← Finset.sum_filter (fun q' => 1 < q' ∧ q' ∣ q)
      (fun q' => (1 / (q : Real)) * f q')]
    apply Finset.sum_congr
    · ext q'
      simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
      have hq0 : q ≠ 0 := by
        intro hqZero
        subst q
        norm_num [Nat.Coprime] at hq10
      constructor
      · rintro ⟨hq'Q, hq', hdiv⟩
        exact ⟨⟨hdiv, hq0⟩, hq'⟩
      · rintro ⟨⟨hdiv, hq0⟩, hq'⟩
        exact ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdiv).trans_lt
          (Finset.mem_range.mp hqQ), hq', hdiv⟩
    · intro q' hq'
      simp
  · simp [hq10]

private theorem typeISourceHarmonicSum_eq_productSum
    (Q : Nat) (f : Nat → Real) :
    (∑ q ∈ (Finset.range Q).filter (fun q => q.Coprime 10),
      (1 / (q : Real)) *
        ∑ q' ∈ q.divisors.filter (fun q' => 1 < q'), f q') =
    ∑ pair ∈ typeIProductPairCarrier Q,
      (1 / (pair.1 : Real)) * (1 / (pair.2 : Real)) * f pair.1 := by
  rw [← sum_typeIDivisorPairCarrier_eq_nested,
    sum_typeIDivisorPairCarrier_eq_productPairCarrier]

private theorem positive_reciprocal_sum_le_harmonic (Q : Nat) :
    (∑ n ∈ (Finset.range Q).filter (fun n => 0 < n),
      1 / (n : Real)) ≤ (harmonic (Q - 1) : Real) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnQ, hnPos⟩
    exact Finset.mem_Icc.mpr ⟨hnPos, by
      have hnLt := Finset.mem_range.mp hnQ
      omega⟩
  · intro n hn _
    positivity

private theorem typeIProductSum_le_harmonic
    (Q : Nat) (f : Nat → Real) (hf : ∀ n, 0 ≤ f n) :
    (∑ pair ∈ typeIProductPairCarrier Q,
      (1 / (pair.1 : Real)) * (1 / (pair.2 : Real)) * f pair.1) ≤
    (harmonic (Q - 1) : Real) *
      ∑ q' ∈ (Finset.range Q).filter
          (fun q' => 1 < q' ∧ q'.Coprime 10),
        (1 / (q' : Real)) * f q' := by
  classical
  let outer := (Finset.range Q).filter
    (fun q' => 1 < q' ∧ q'.Coprime 10)
  let positive := (Finset.range Q).filter (fun q'' => 0 < q'')
  have hsubset : typeIProductPairCarrier Q ⊆ outer.product positive := by
    intro pair hpair
    rcases pair with ⟨q', q''⟩
    rcases typeIProductPairCarrier_mem hpair with
      ⟨hq'Q, hq''Q, hq', hq''Pos, _, hq'10, _⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq'Q, hq', hq'10⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq''Q, hq''Pos⟩⟩
  calc
    (∑ pair ∈ typeIProductPairCarrier Q,
        (1 / (pair.1 : Real)) * (1 / (pair.2 : Real)) * f pair.1) ≤
        ∑ pair ∈ outer.product positive,
          (1 / (pair.1 : Real)) * (1 / (pair.2 : Real)) * f pair.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro pair _ _
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (hf pair.1)
    _ = ∑ q' ∈ outer,
        ((1 / (q' : Real)) * f q') *
          ∑ q'' ∈ positive, 1 / (q'' : Real) := by
      refine (Finset.sum_product outer positive
        (fun pair : Nat × Nat =>
          (1 / (pair.1 : Real)) * (1 / (pair.2 : Real)) * f pair.1)).trans ?_
      apply Finset.sum_congr rfl
      intro q' hq'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q'' hq''
      ring
    _ ≤ ∑ q' ∈ outer,
        ((1 / (q' : Real)) * f q') * (harmonic (Q - 1) : Real) := by
      apply Finset.sum_le_sum
      intro q' hq'
      apply mul_le_mul_of_nonneg_left
        (positive_reciprocal_sum_le_harmonic Q)
      exact mul_nonneg (by positivity) (hf q')
    _ = (harmonic (Q - 1) : Real) *
        ∑ q' ∈ (Finset.range Q).filter
            (fun q' => 1 < q' ∧ q'.Coprime 10),
          (1 / (q' : Real)) * f q' := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q' hq'
      ring

private theorem typeISourceHarmonicSum_le
    (Q : Nat) (f : Nat → Real) (hf : ∀ n, 0 ≤ f n) :
    (∑ q ∈ (Finset.range Q).filter (fun q => q.Coprime 10),
      (1 / (q : Real)) *
        ∑ q' ∈ q.divisors.filter (fun q' => 1 < q'), f q') ≤
    (harmonic (Q - 1) : Real) *
      ∑ q' ∈ (Finset.range Q).filter
          (fun q' => 1 < q' ∧ q'.Coprime 10),
        (1 / (q' : Real)) * f q' := by
  rw [typeISourceHarmonicSum_eq_productSum]
  exact typeIProductSum_le_harmonic Q f hf

private theorem typeIReducedFrequencyMass_nonneg
    (digit : Fin 10) (length d q : Nat) :
    0 ≤ typeIReducedFrequencyMass digit length d q := by
  apply Finset.sum_nonneg
  intro b hb
  exact normalizedPaddedDigitFourierMagnitudeAt_nonneg _ _ _

/-- The source's exact modulus-factor reindex followed by its valid harmonic
relaxation. The factor `q''` is positive before its reciprocal is formed. -/
theorem sum_typeIReducedErrorFourierSum_div_le_harmonic
    (digit : Fin 10) (length : Nat) (Q : Real) :
    (∑ q ∈ typeIModuliBelow Q,
      typeIReducedErrorFourierSum digit length q / (q : Real)) ≤
      (harmonic (Nat.ceil Q - 1) : Real) *
        ∑ d ∈ Nat.divisors 10,
          ∑ q' ∈ (Finset.range (Nat.ceil Q)).filter
              (fun q' => 1 < q' ∧ Nat.Coprime q' 10),
            typeIReducedFrequencyMass digit length d q' / (q' : Real) := by
  let N := Nat.ceil Q
  let H : Real := harmonic (N - 1)
  have hgeneric (d : Nat) :
      (∑ q ∈ (Finset.range N).filter (fun q => q.Coprime 10),
        (1 / (q : Real)) *
          ∑ q' ∈ q.divisors.filter (fun q' => 1 < q'),
            typeIReducedFrequencyMass digit length d q') ≤
      H * ∑ q' ∈ (Finset.range N).filter
          (fun q' => 1 < q' ∧ q'.Coprime 10),
        (1 / (q' : Real)) *
          typeIReducedFrequencyMass digit length d q' := by
    exact typeISourceHarmonicSum_le N
      (typeIReducedFrequencyMass digit length d)
      (typeIReducedFrequencyMass_nonneg digit length d)
  change (∑ q ∈ (Finset.range N).filter (fun q => q.Coprime 10),
      typeIReducedErrorFourierSum digit length q / (q : Real)) ≤ _
  calc
    (∑ q ∈ (Finset.range N).filter (fun q => q.Coprime 10),
        typeIReducedErrorFourierSum digit length q / (q : Real)) =
        ∑ q ∈ (Finset.range N).filter (fun q => q.Coprime 10),
          ∑ d ∈ Nat.divisors 10,
            (∑ q' ∈ q.divisors.filter (fun q' => 1 < q'),
              typeIReducedFrequencyMass digit length d q') / (q : Real) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [typeIReducedErrorFourierSum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      rfl
    _ = ∑ d ∈ Nat.divisors 10,
          ∑ q ∈ (Finset.range N).filter (fun q => q.Coprime 10),
            (∑ q' ∈ q.divisors.filter (fun q' => 1 < q'),
              typeIReducedFrequencyMass digit length d q') / (q : Real) := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Nat.divisors 10,
          ∑ q ∈ (Finset.range N).filter (fun q => q.Coprime 10),
            (1 / (q : Real)) *
              ∑ q' ∈ q.divisors.filter (fun q' => 1 < q'),
                typeIReducedFrequencyMass digit length d q' := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ ∑ d ∈ Nat.divisors 10,
        H * ∑ q' ∈ (Finset.range N).filter
          (fun q' => 1 < q' ∧ q'.Coprime 10),
            (1 / (q' : Real)) *
              typeIReducedFrequencyMass digit length d q' := by
      apply Finset.sum_le_sum
      intro d hd
      exact hgeneric d
    _ = H * ∑ d ∈ Nat.divisors 10,
        ∑ q' ∈ (Finset.range N).filter
            (fun q' => 1 < q' ∧ Nat.Coprime q' 10),
          typeIReducedFrequencyMass digit length d q' / (q' : Real) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      apply Finset.sum_congr rfl
      intro q' hq'
      ring

end PrimesRestrictedDigits
