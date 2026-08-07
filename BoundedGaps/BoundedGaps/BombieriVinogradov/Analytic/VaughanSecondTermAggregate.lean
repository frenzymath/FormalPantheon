import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermTrivial
import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermPolyaVinogradov
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFirstTermBound

/-!
# Vaughan's second-term aggregate bound

This file isolates the level-one contribution and combines it with the
primitive Polya--Vinogradov estimate to prove the natural-cutoff version of
Akbary--Hambrook2013v2, equation (6.10).
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
  uniq chi := by
    apply Subtype.ext
    exact DirichletCharacter.level_one chi.1

/-- There is exactly one primitive complex Dirichlet character at level one. -/
theorem card_primitiveCharacters_one :
    Fintype.card (primitiveCharacters 1) = 1 :=
  Fintype.card_unique

/-- Maximum second Vaughan term over positive natural endpoints through `x`,
totalized to zero when the interval is empty. -/
noncomputable def vaughanTwistedSumTwoEndpointMaximum
    (V : ℝ) (x q : ℕ) (chi : DirichletCharacter ℂ q) : ℝ :=
  if hx : 1 ≤ x then
    (Finset.Icc 1 x).sup'
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩
      (fun y ↦ ‖vaughanTwistedSumTwo V y q chi‖)
  else 0

/-- The level-one endpoint maximum satisfies the source's strict trivial
bound. -/
theorem vaughanTwistedSumTwoEndpointMaximum_level_one_lt_endpoint_mul_log_sq
    {V : ℝ} {x : ℕ} (hx : 4 ≤ x) (hV : 1 ≤ V)
    (chi : DirichletCharacter ℂ 1) :
    vaughanTwistedSumTwoEndpointMaximum V x 1 chi <
      (x : ℝ) * (Real.log ((x : ℝ) * V)) ^ 2 := by
  unfold vaughanTwistedSumTwoEndpointMaximum
  rw [dif_pos (by omega)]
  rw [Finset.sup'_lt_iff]
  intro y hy
  exact norm_vaughanTwistedSumTwo_level_one_lt_endpoint_mul_log_sq
    hx hV (Finset.mem_Icc.mp hy).2 chi

/-- The primitive Polya--Vinogradov estimate, maximized over natural
endpoints. -/
theorem vaughanTwistedSumTwoEndpointMaximum_lt_sqrt_mul_cutoff_mul_log_sq
    {Q V : ℝ} {x q : ℕ}
    (hx : 4 ≤ x) (hV : 1 ≤ V)
    (hq : 1 < q) (hqQ : (q : ℝ) ≤ Q)
    (hQsqrt : Q ≤ Real.sqrt (x : ℝ))
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive) :
    vaughanTwistedSumTwoEndpointMaximum V x q chi <
      Real.sqrt (q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
  unfold vaughanTwistedSumTwoEndpointMaximum
  rw [dif_pos (by omega)]
  rw [Finset.sup'_lt_iff]
  intro y hy
  exact norm_vaughanTwistedSumTwo_lt_sqrt_mul_cutoff_mul_log_sq
    hx hV (Finset.mem_Icc.mp hy).2 hq hqQ hQsqrt chi hchi

private theorem weightedPrimitiveVaughanTwistedSumTwoEndpointMaximum_le
    {V : ℝ} {x Q q : ℕ}
    (hx : 4 ≤ x) (hV : 1 ≤ V)
    (hq : 1 < q) (hqQ : q ≤ Q)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumTwoEndpointMaximum V x q chi.1 ≤
      (q : ℝ) * Real.sqrt (q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hphi : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  have hboundNonneg :
      0 ≤ Real.sqrt (q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
    positivity
  have hmass :
      (∑ chi : primitiveCharacters q,
          vaughanTwistedSumTwoEndpointMaximum V x q chi.1) ≤
        (q.totient : ℝ) *
          (Real.sqrt (q : ℝ) * V *
            (Real.log ((x : ℝ) * V)) ^ 2) := by
    calc
      (∑ chi : primitiveCharacters q,
          vaughanTwistedSumTwoEndpointMaximum V x q chi.1) ≤
          ∑ _chi : primitiveCharacters q,
            Real.sqrt (q : ℝ) * V *
              (Real.log ((x : ℝ) * V)) ^ 2 := by
        apply Finset.sum_le_sum
        intro chi _hchi
        exact (vaughanTwistedSumTwoEndpointMaximum_lt_sqrt_mul_cutoff_mul_log_sq
          hx hV hq (by exact_mod_cast hqQ) hQsqrt chi.1 chi.2).le
      _ = (Fintype.card (primitiveCharacters q) : ℝ) *
          (Real.sqrt (q : ℝ) * V *
            (Real.log ((x : ℝ) * V)) ^ 2) := by
        simp
      _ ≤ (q.totient : ℝ) *
          (Real.sqrt (q : ℝ) * V *
            (Real.log ((x : ℝ) * V)) ^ 2) := by
        gcongr
        exact_mod_cast card_primitiveCharacters_le_totient hqpos
  calc
    (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumTwoEndpointMaximum V x q chi.1 ≤
      (q : ℝ) / (q.totient : ℝ) *
        ((q.totient : ℝ) *
          (Real.sqrt (q : ℝ) * V *
            (Real.log ((x : ℝ) * V)) ^ 2)) := by
      gcongr
    _ = (q : ℝ) * Real.sqrt (q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
      field_simp

private theorem sum_weightedPrimitiveVaughanTwistedSumTwoEndpointMaximum_rest_le
    {V : ℝ} {x Q : ℕ}
    (hx : 4 ≤ x) (hV : 1 ≤ V)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 1 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumTwoEndpointMaximum V x q chi.1) ≤
      (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
  have hVsqrtNonneg :
      0 ≤ Real.sqrt (Q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
    positivity
  calc
    (∑ q ∈ Finset.Ioc 1 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumTwoEndpointMaximum V x q chi.1) ≤
        ∑ q ∈ Finset.Ioc 1 Q,
          (q : ℝ) * Real.sqrt (q : ℝ) * V *
            (Real.log ((x : ℝ) * V)) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact weightedPrimitiveVaughanTwistedSumTwoEndpointMaximum_le
        hx hV (Finset.mem_Ioc.mp hq).1 (Finset.mem_Ioc.mp hq).2 hQsqrt
    _ ≤ ∑ _q ∈ Finset.Ioc 1 Q,
        (Q : ℝ) * Real.sqrt (Q : ℝ) * V *
          (Real.log ((x : ℝ) * V)) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hqQ : (q : ℝ) ≤ Q := by
        exact_mod_cast (Finset.mem_Ioc.mp hq).2
      have hsqrt : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) :=
        Real.sqrt_le_sqrt hqQ
      gcongr
    _ ≤ (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * V *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc
        (Finset.Ioc 1 Q).card *
            ((Q : ℝ) * Real.sqrt (Q : ℝ) * V *
              (Real.log ((x : ℝ) * V)) ^ 2) ≤
            (Q : ℝ) *
              ((Q : ℝ) * Real.sqrt (Q : ℝ) * V *
                (Real.log ((x : ℝ) * V)) ^ 2) := by
          gcongr
          exact_mod_cast (show (Finset.Ioc 1 Q).card ≤ Q by
            simp [Nat.card_Ioc])
        _ = (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * V *
            (Real.log ((x : ℝ) * V)) ^ 2 := by ring

/-- Natural-cutoff specialization of Akbary--Hambrook equation (6.10). -/
theorem sum_weightedPrimitiveVaughanTwistedSumTwoEndpointMaximum_lt
    {V : ℝ} {x Q : ℕ}
    (hx : 4 ≤ x) (hV : 1 ≤ V) (hQ : 2 ≤ Q)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumTwoEndpointMaximum V x q chi.1) <
      ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * V) *
        (Real.log ((x : ℝ) * V)) ^ 2 := by
  have hone : 1 ∈ Finset.Ioc 0 Q := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have honeValue :
      (1 : ℝ) / ((1 : ℕ).totient : ℝ) *
          ∑ chi : primitiveCharacters 1,
            vaughanTwistedSumTwoEndpointMaximum V x 1 chi.1 <
        (x : ℝ) * (Real.log ((x : ℝ) * V)) ^ 2 := by
    simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul]
    rw [Fintype.sum_unique]
    exact vaughanTwistedSumTwoEndpointMaximum_level_one_lt_endpoint_mul_log_sq
      hx hV primitiveCharacterOne.1
  have hsplit : Finset.Ioc 0 Q \ {1} = Finset.Ioc 1 Q := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_singleton]
    omega
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumTwoEndpointMaximum V x q chi.1) =
        (1 : ℝ) / ((1 : ℕ).totient : ℝ) *
            ∑ chi : primitiveCharacters 1,
              vaughanTwistedSumTwoEndpointMaximum V x 1 chi.1 +
          ∑ q ∈ Finset.Ioc 1 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ chi : primitiveCharacters q,
                vaughanTwistedSumTwoEndpointMaximum V x q chi.1 := by
      rw [← hsplit, Finset.sdiff_singleton_eq_erase]
      simpa only [Nat.cast_one] using
        (Finset.add_sum_erase (M := ℝ) (Finset.Ioc 0 Q)
        (fun q : ℕ ↦
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanTwistedSumTwoEndpointMaximum V x q chi.1) hone).symm
    _ < (x : ℝ) * (Real.log ((x : ℝ) * V)) ^ 2 +
        (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * V *
          (Real.log ((x : ℝ) * V)) ^ 2 :=
      add_lt_add_of_lt_of_le honeValue
        (sum_weightedPrimitiveVaughanTwistedSumTwoEndpointMaximum_rest_le
          hx hV hQsqrt)
    _ = ((x : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (Q : ℝ) * V) *
        (Real.log ((x : ℝ) * V)) ^ 2 := by ring

end

end BoundedGaps.Maynard
