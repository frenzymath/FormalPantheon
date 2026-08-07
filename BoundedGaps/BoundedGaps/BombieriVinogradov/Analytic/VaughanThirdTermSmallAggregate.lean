import BoundedGaps.BombieriVinogradov.Analytic.VaughanFirstTermBound
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdTermSmall

/-!
# Vaughan's small third-term aggregate bound

This file combines the level-one and primitive pointwise estimates to prove
the natural-cutoff specialization of Akbary--Hambrook2013v2, equation (6.12).
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

private noncomputable def primitiveCharacterOne : primitiveCharacters 1 :=
  ⟨(1 : DirichletCharacter ℂ 1),
    DirichletCharacter.isPrimitive_one_level_one⟩

private noncomputable local instance primitiveCharactersOneUnique :
    Unique (primitiveCharacters 1) where
  default := primitiveCharacterOne
  uniq χ := by
    apply Subtype.ext
    exact DirichletCharacter.level_one χ.1

/-- Maximum small third Vaughan term over positive natural endpoints through
`x`, totalized to zero when the interval is empty. -/
noncomputable def vaughanTwistedSumThreeSmallEndpointMaximum
    (U V : ℝ) (x q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  if hx : 1 ≤ x then
    (Finset.Icc 1 x).sup'
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩
      (fun y ↦ ‖vaughanTwistedSumThreeSmall U V y q χ‖)
  else 0

/-- The level-one endpoint maximum satisfies the strict small-term bound. -/
theorem vaughanTwistedSumThreeSmallEndpointMaximum_level_one_lt_endpoint_mul_log_sq
    {U V : ℝ} {x : ℕ} (hx : 4 ≤ x) (hU : 1 ≤ U)
    (χ : DirichletCharacter ℂ 1) :
    vaughanTwistedSumThreeSmallEndpointMaximum U V x 1 χ <
      (x : ℝ) * (Real.log ((x : ℝ) * U)) ^ 2 := by
  unfold vaughanTwistedSumThreeSmallEndpointMaximum
  rw [dif_pos (by omega)]
  rw [Finset.sup'_lt_iff]
  intro y hy
  exact norm_vaughanTwistedSumThreeSmall_level_one_lt_endpoint_mul_log_sq
    hx hU (Finset.mem_Icc.mp hy).2 χ

/-- The primitive Polya--Vinogradov estimate, maximized over natural
endpoints. -/
theorem vaughanTwistedSumThreeSmallEndpointMaximum_lt_sqrt_mul_cutoff_mul_log_sq
    {Q U V : ℝ} {x q : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U)
    (hq : 1 < q) (hqQ : (q : ℝ) ≤ Q)
    (hQsqrt : Q ≤ Real.sqrt (x : ℝ))
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ <
      Real.sqrt (q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
  unfold vaughanTwistedSumThreeSmallEndpointMaximum
  rw [dif_pos (by omega)]
  rw [Finset.sup'_lt_iff]
  intro y _hy
  exact norm_vaughanTwistedSumThreeSmall_lt_sqrt_mul_cutoff_mul_log_sq
    hx hU hq hqQ hQsqrt χ hχ

private theorem weightedPrimitiveVaughanTwistedSumThreeSmallEndpointMaximum_le
    {U V : ℝ} {x Q q : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U)
    (hq : 1 < q) (hqQ : q ≤ Q)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : primitiveCharacters q,
          vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1 ≤
      (q : ℝ) * Real.sqrt (q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hphi : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  have hboundNonneg :
      0 ≤ Real.sqrt (q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
    positivity
  have hmass :
      (∑ χ : primitiveCharacters q,
          vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1) ≤
        (q.totient : ℝ) *
          (Real.sqrt (q : ℝ) * U *
            (Real.log ((x : ℝ) * U)) ^ 2) := by
    calc
      (∑ χ : primitiveCharacters q,
          vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1) ≤
          ∑ _χ : primitiveCharacters q,
            Real.sqrt (q : ℝ) * U *
              (Real.log ((x : ℝ) * U)) ^ 2 := by
        apply Finset.sum_le_sum
        intro χ _hχ
        exact
          (vaughanTwistedSumThreeSmallEndpointMaximum_lt_sqrt_mul_cutoff_mul_log_sq
            hx hU hq (by exact_mod_cast hqQ) hQsqrt χ.1 χ.2).le
      _ = (Fintype.card (primitiveCharacters q) : ℝ) *
          (Real.sqrt (q : ℝ) * U *
            (Real.log ((x : ℝ) * U)) ^ 2) := by
        simp
      _ ≤ (q.totient : ℝ) *
          (Real.sqrt (q : ℝ) * U *
            (Real.log ((x : ℝ) * U)) ^ 2) := by
        gcongr
        exact_mod_cast card_primitiveCharacters_le_totient hqpos
  calc
    (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : primitiveCharacters q,
          vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1 ≤
      (q : ℝ) / (q.totient : ℝ) *
        ((q.totient : ℝ) *
          (Real.sqrt (q : ℝ) * U *
            (Real.log ((x : ℝ) * U)) ^ 2)) := by
      gcongr
    _ = (q : ℝ) * Real.sqrt (q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
      field_simp

private theorem sum_weightedPrimitiveVaughanTwistedSumThreeSmallEndpointMaximum_rest_le
    {U V : ℝ} {x Q : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 1 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : primitiveCharacters q,
          vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1) ≤
      (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
  have hUsqrtNonneg :
      0 ≤ Real.sqrt (Q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
    positivity
  calc
    (∑ q ∈ Finset.Ioc 1 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ χ : primitiveCharacters q,
            vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1) ≤
        ∑ q ∈ Finset.Ioc 1 Q,
          (q : ℝ) * Real.sqrt (q : ℝ) * U *
            (Real.log ((x : ℝ) * U)) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact weightedPrimitiveVaughanTwistedSumThreeSmallEndpointMaximum_le
        hx hU (Finset.mem_Ioc.mp hq).1 (Finset.mem_Ioc.mp hq).2 hQsqrt
    _ ≤ ∑ _q ∈ Finset.Ioc 1 Q,
        (Q : ℝ) * Real.sqrt (Q : ℝ) * U *
          (Real.log ((x : ℝ) * U)) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hqQ : (q : ℝ) ≤ Q := by
        exact_mod_cast (Finset.mem_Ioc.mp hq).2
      have hsqrt : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) :=
        Real.sqrt_le_sqrt hqQ
      gcongr
    _ ≤ (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * U *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc
        (Finset.Ioc 1 Q).card *
            ((Q : ℝ) * Real.sqrt (Q : ℝ) * U *
              (Real.log ((x : ℝ) * U)) ^ 2) ≤
            (Q : ℝ) *
              ((Q : ℝ) * Real.sqrt (Q : ℝ) * U *
                (Real.log ((x : ℝ) * U)) ^ 2) := by
          gcongr
          exact_mod_cast (show (Finset.Ioc 1 Q).card ≤ Q by
            simp [Nat.card_Ioc])
        _ = (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * U *
            (Real.log ((x : ℝ) * U)) ^ 2 := by ring

/-- Natural-cutoff specialization of Akbary--Hambrook equation (6.12). -/
theorem sum_weightedPrimitiveVaughanTwistedSumThreeSmallEndpointMaximum_lt
    {U V : ℝ} {x Q : ℕ}
    (hx : 4 ≤ x) (hU : 1 ≤ U) (hQ : 2 ≤ Q)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : primitiveCharacters q,
          vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1) <
      ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * U) *
        (Real.log ((x : ℝ) * U)) ^ 2 := by
  have hone : 1 ∈ Finset.Ioc 0 Q :=
    Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have honeValue :
      (1 : ℝ) / ((1 : ℕ).totient : ℝ) *
          ∑ χ : primitiveCharacters 1,
            vaughanTwistedSumThreeSmallEndpointMaximum U V x 1 χ.1 <
        (x : ℝ) * (Real.log ((x : ℝ) * U)) ^ 2 := by
    simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul]
    rw [Fintype.sum_unique]
    exact
      vaughanTwistedSumThreeSmallEndpointMaximum_level_one_lt_endpoint_mul_log_sq
        hx hU primitiveCharacterOne.1
  have hsplit : Finset.Ioc 0 Q \ {1} = Finset.Ioc 1 Q := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_singleton]
    omega
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ χ : primitiveCharacters q,
            vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1) =
        (1 : ℝ) / ((1 : ℕ).totient : ℝ) *
            ∑ χ : primitiveCharacters 1,
              vaughanTwistedSumThreeSmallEndpointMaximum U V x 1 χ.1 +
          ∑ q ∈ Finset.Ioc 1 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ χ : primitiveCharacters q,
                vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1 := by
      rw [← hsplit, Finset.sdiff_singleton_eq_erase]
      simpa only [Nat.cast_one] using
        (Finset.add_sum_erase (M := ℝ) (Finset.Ioc 0 Q)
        (fun q : ℕ ↦
          (q : ℝ) / (q.totient : ℝ) *
            ∑ χ : primitiveCharacters q,
              vaughanTwistedSumThreeSmallEndpointMaximum U V x q χ.1) hone).symm
    _ < (x : ℝ) * (Real.log ((x : ℝ) * U)) ^ 2 +
        (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * U *
          (Real.log ((x : ℝ) * U)) ^ 2 :=
      add_lt_add_of_lt_of_le honeValue
        (sum_weightedPrimitiveVaughanTwistedSumThreeSmallEndpointMaximum_rest_le
          hx hU hQsqrt)
    _ = ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * U) *
        (Real.log ((x : ℝ) * U)) ^ 2 := by ring

end

end BoundedGaps.Maynard
