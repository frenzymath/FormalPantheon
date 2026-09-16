import PrimesRestrictedDigits.PrimeNumberTheorem.BuchstabInduction

/-!
# The Maynard rough-number cutoff bridge

Maynard's displayed rough-number count has a strict outer cutoff and a weak
prime-factor threshold.  The Montgomery--Vaughan estimate already formalized
in `BuchstabInduction` uses the same positive carrier and weak threshold, but
has a weak outer cutoff.  This file records the finite endpoint transfer and
the resulting quantitative power reparameterization.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

/-- Positive rough integers below a strict real cutoff, with a weak factor
threshold.  The lower endpoint excludes zero and includes one. -/
noncomputable def maynardRoughCarrier (Y y : Real) : Finset Nat := by
  classical
  exact ((naturalLeftClosedRightOpenInterval 1 Y).filter
    (fun n : Nat => ∀ p, p.Prime → p ∣ n → y ≤ (p : Real)))

noncomputable def maynardRoughCount (Y y : Real) : Nat :=
  (maynardRoughCarrier Y y).card

@[simp] theorem mem_maynardRoughCarrier {Y y : Real} {n : Nat} :
    n ∈ maynardRoughCarrier Y y ↔
      1 ≤ n ∧ (n : Real) < Y ∧
        ∀ p, p.Prime → p ∣ n → y ≤ (p : Real) := by
  classical
  simp [maynardRoughCarrier, mem_naturalLeftClosedRightOpenInterval]
  constructor
  · rintro ⟨⟨hn1, hnY⟩, hrough⟩
    exact ⟨hn1, hnY, hrough⟩
  · rintro ⟨hn1, hnY, hrough⟩
    exact ⟨⟨hn1, hnY⟩, hrough⟩

/-- Positive rough integers below a strict real cutoff, with a strict factor
threshold.  The quantified divisor predicate deliberately avoids `minFac` at
zero and one. -/
noncomputable def maynardStrictRoughCarrier (Y y : Real) : Finset Nat := by
  classical
  exact ((naturalLeftClosedRightOpenInterval 1 Y).filter
    (fun n : Nat => ∀ p, p.Prime → p ∣ n → y < (p : Real)))

noncomputable def maynardStrictRoughCount (Y y : Real) : Nat :=
  (maynardStrictRoughCarrier Y y).card

@[simp] theorem mem_maynardStrictRoughCarrier {Y y : Real} {n : Nat} :
    n ∈ maynardStrictRoughCarrier Y y ↔
      1 ≤ n ∧ (n : Real) < Y ∧
        ∀ p, p.Prime → p ∣ n → y < (p : Real) := by
  classical
  simp [maynardStrictRoughCarrier, mem_naturalLeftClosedRightOpenInterval]
  constructor
  · rintro ⟨⟨hn1, hnY⟩, hrough⟩
    exact ⟨hn1, hnY, hrough⟩
  · rintro ⟨hn1, hnY, hrough⟩
    exact ⟨⟨hn1, hnY⟩, hrough⟩

theorem maynardStrictRoughCarrier_subset_maynardRoughCarrier
    (Y y : Real) :
    maynardStrictRoughCarrier Y y ⊆ maynardRoughCarrier Y y := by
  intro n hn
  rw [mem_maynardStrictRoughCarrier] at hn
  rw [mem_maynardRoughCarrier]
  refine ⟨hn.1, hn.2.1, ?_⟩
  intro p hp hpn
  exact (hn.2.2 p hp hpn).le

theorem maynardStrictRoughCount_le_maynardRoughCount
    (Y y : Real) :
    maynardStrictRoughCount Y y ≤ maynardRoughCount Y y := by
  have hcard := Finset.card_le_card
    (maynardStrictRoughCarrier_subset_maynardRoughCarrier Y y)
  exact hcard

private noncomputable def maynardClosedRoughCarrier (Y y : Real) : Finset Nat := by
  classical
  exact (naturalClosedInterval 1 Y).filter
    (fun n : Nat => ∀ p, p.Prime → p ∣ n → y ≤ (p : Real))

private theorem maynardClosedRoughCarrier_eq_buchstab
    {Y y : Real} (hY : 0 ≤ Y) :
    maynardClosedRoughCarrier Y y = buchstabRoughNumbers Y y := by
  classical
  ext n
  simp only [maynardClosedRoughCarrier, Finset.mem_filter,
    mem_naturalClosedInterval hY, mem_buchstabRoughNumbers]
  constructor
  · rintro ⟨⟨hn1, hnY⟩, hrough⟩
    exact ⟨by exact_mod_cast hn1, hnY, hrough⟩
  · rintro ⟨hn1, hnY, hrough⟩
    exact ⟨⟨by exact_mod_cast hn1, hnY⟩, hrough⟩

private theorem maynardRoughCarrier_subset_closed
    (Y y : Real) :
    maynardRoughCarrier Y y ⊆
      maynardClosedRoughCarrier Y y := by
  classical
  exact Finset.filter_subset_filter _
    (naturalLeftClosedRightOpenInterval_subset_closed 1 Y)

private theorem maynardRoughCarrier_diff_card_le_one
    (Y y : Real) :
    (maynardClosedRoughCarrier Y y \
        maynardRoughCarrier Y y).card ≤ 1 := by
  classical
  apply (Finset.card_le_card
    (filteredNaturalClosedInterval_sdiff_halfOpen_subset_singleton
      (fun n : Nat => ∀ p, p.Prime → p ∣ n → y ≤ (p : Real)) 1 Y)).trans
  simp

/-- The strict outer cutoff differs from the weak one by at most the endpoint. -/
theorem abs_maynardRoughCount_sub_buchstabPhi_le_one
    {Y y : Real} (hY : 0 < Y) :
    |(maynardRoughCount Y y : Real) - (buchstabPhi Y y : Real)| ≤ 1 := by
  classical
  let half := maynardRoughCarrier Y y
  let closed := maynardClosedRoughCarrier Y y
  have hsub : half ⊆ closed := by
    simpa [half, closed] using maynardRoughCarrier_subset_closed Y y
  have hcardEq : (closed \ half).card + half.card = closed.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hdiff : (closed \ half).card ≤ 1 := by
    simpa [closed, half] using maynardRoughCarrier_diff_card_le_one Y y
  have hclosedPhi : closed.card = buchstabPhi Y y := by
    have heq := maynardClosedRoughCarrier_eq_buchstab
      (Y := Y) (y := y) (le_of_lt hY)
    simpa [closed, buchstabPhi] using congrArg Finset.card heq
  have hhalfCount : half.card = maynardRoughCount Y y := by
    simp [half, maynardRoughCount]
  have hcardLe : half.card ≤ closed.card := by omega
  have hsubNat : closed.card - half.card ≤ 1 := by omega
  have hsubCast :
      (closed.card : Real) - (half.card : Real) =
        ((closed.card - half.card : Nat) : Real) := by
    rw [Nat.cast_sub hcardLe]
  have hnonneg : (0 : Real) ≤ (closed.card : Real) - half.card := by
    rw [hsubCast]
    exact_mod_cast (Nat.zero_le (closed.card - half.card))
  have hupper : (closed.card : Real) - half.card ≤ 1 := by
    rw [hsubCast]
    exact_mod_cast hsubNat
  have hclosedCast : (closed.card : Real) = (buchstabPhi Y y : Real) := by
    exact_mod_cast hclosedPhi
  have hhalfCast : (half.card : Real) = (maynardRoughCount Y y : Real) := by
    exact_mod_cast hhalfCount
  rw [← hhalfCast, ← hclosedCast]
  rw [abs_sub_comm]
  rw [abs_of_nonneg hnonneg]
  exact hupper

private theorem maynardRoughCount_le_buchstabPhi
    {Y y : Real} (hY : 0 < Y) :
    (maynardRoughCount Y y : Real) ≤ (buchstabPhi Y y : Real) := by
  have hnonneg : (0 : Real) ≤
      (buchstabPhi Y y : Real) - (maynardRoughCount Y y : Real) := by
    have h := maynardRoughCarrier_subset_closed Y y
    have hcard := Finset.card_le_card h
    have hclosed := maynardClosedRoughCarrier_eq_buchstab
      (Y := Y) (y := y) (le_of_lt hY)
    have hnat : maynardRoughCount Y y ≤ buchstabPhi Y y := by
      simpa [maynardRoughCount, hclosed, buchstabPhi] using hcard
    have hnatCast : (maynardRoughCount Y y : Real) ≤
        (buchstabPhi Y y : Real) := by
      exact_mod_cast hnat
    linarith
  linarith

/-- Quantitative transfer of the compact-uniform Buchstab estimate to
Maynard's strict outer cutoff. -/
theorem exists_maynardRoughCount_error :
    ∀ U : Real, 1 ≤ U →
      ∃ C : Real, 0 < C ∧
        ∀ Y y u : Real, 0 < Y → 2 ≤ y → 1 ≤ u → u ≤ U →
          u = Real.log Y / Real.log y →
          |(maynardRoughCount Y y : Real) -
            (buchstabFunction u * Y / Real.log y - y / Real.log y)| ≤
            C * (Y / Real.log Y ^ 2) + 1 := by
  intro U hU
  obtain ⟨C, hC, hEstimate⟩ := buchstabPhi_estimate U hU
  refine ⟨C, hC, ?_⟩
  intro Y y u hY hy hu huU hparam
  have hPhi := hEstimate Y y u hY hy hu huU hparam
  have hEndpoint := abs_maynardRoughCount_sub_buchstabPhi_le_one
    (Y := Y) (y := y) hY
  calc
    |(maynardRoughCount Y y : Real) -
        (buchstabFunction u * Y / Real.log y - y / Real.log y)| ≤
        |(maynardRoughCount Y y : Real) - (buchstabPhi Y y : Real)| +
          |(buchstabPhi Y y : Real) -
            (buchstabFunction u * Y / Real.log y - y / Real.log y)| :=
      abs_sub_le _ _ _
    _ ≤ 1 + C * (Y / Real.log Y ^ 2) :=
      add_le_add hEndpoint hPhi
    _ = C * (Y / Real.log Y ^ 2) + 1 := by ring

/-- The power-parameter form of the Maynard rough-number estimate. -/
theorem exists_maynardRoughCount_power_error :
    ∀ U : Real, 1 ≤ U →
      ∃ C : Real, 0 < C ∧
        ∀ Y u : Real, 0 < Y → 2 ≤ Y ^ (1 / u) → 1 ≤ u → u ≤ U →
          |(maynardRoughCount Y (Y ^ (1 / u)) : Real) -
            buchstabFunction u * u * Y / Real.log Y| ≤
            C * (Y / Real.log Y ^ 2) +
              Y ^ (1 / u) / Real.log (Y ^ (1 / u)) + 1 := by
  intro U hU
  obtain ⟨C, hC, hEstimate⟩ := exists_maynardRoughCount_error U hU
  refine ⟨C, hC, ?_⟩
  intro Y u hY hy hu huU
  have hu0 : 0 < u := by linarith
  have hy0 : 0 < Y ^ (1 / u) := Real.rpow_pos_of_pos hY _
  have hlogPower :
      Real.log (Y ^ (1 / u)) = (1 / u) * Real.log Y := by
    exact Real.log_rpow hY (1 / u)
  have hlogY : 0 < Real.log Y := by
    have hlogy : 0 < Real.log (Y ^ (1 / u)) :=
      Real.log_pos (by linarith)
    rw [hlogPower] at hlogy
    have hInv : 0 < (1 / u : Real) := one_div_pos.mpr hu0
    exact pos_of_mul_pos_right hlogy hInv.le
  have hparam : u = Real.log Y / Real.log (Y ^ (1 / u)) := by
    rw [hlogPower]
    field_simp
  have hmain := hEstimate Y (Y ^ (1 / u)) u hY hy hu huU hparam
  have hnormal :
      buchstabFunction u * Y / Real.log (Y ^ (1 / u)) -
          Y ^ (1 / u) / Real.log (Y ^ (1 / u)) =
        buchstabFunction u * u * Y / Real.log Y -
          Y ^ (1 / u) / Real.log (Y ^ (1 / u)) := by
    rw [hlogPower]
    field_simp
  rw [hnormal] at hmain
  have hsec : 0 ≤ Y ^ (1 / u) / Real.log (Y ^ (1 / u)) := by
    exact le_of_lt (div_pos hy0 (Real.log_pos (by linarith)))
  have hdiff :
      |buchstabFunction u * u * Y / Real.log Y -
          Y ^ (1 / u) / Real.log (Y ^ (1 / u)) -
        buchstabFunction u * u * Y / Real.log Y| =
      Y ^ (1 / u) / Real.log (Y ^ (1 / u)) := by
    rw [show buchstabFunction u * u * Y / Real.log Y -
          Y ^ (1 / u) / Real.log (Y ^ (1 / u)) -
          buchstabFunction u * u * Y / Real.log Y =
        -(Y ^ (1 / u) / Real.log (Y ^ (1 / u))) by ring]
    rw [abs_neg, abs_of_nonneg hsec]
  calc
    |(maynardRoughCount Y (Y ^ (1 / u)) : Real) -
        buchstabFunction u * u * Y / Real.log Y| ≤
        |(maynardRoughCount Y (Y ^ (1 / u)) : Real) -
            (buchstabFunction u * u * Y / Real.log Y -
              Y ^ (1 / u) / Real.log (Y ^ (1 / u)))| +
          |(buchstabFunction u * u * Y / Real.log Y -
              Y ^ (1 / u) / Real.log (Y ^ (1 / u))) -
            buchstabFunction u * u * Y / Real.log Y| :=
      abs_sub_le _ _ _
    _ = |(maynardRoughCount Y (Y ^ (1 / u)) : Real) -
          (buchstabFunction u * u * Y / Real.log Y -
            Y ^ (1 / u) / Real.log (Y ^ (1 / u)))| +
          Y ^ (1 / u) / Real.log (Y ^ (1 / u)) := by rw [hdiff]
    _ ≤ (C * (Y / Real.log Y ^ 2) + 1) +
          Y ^ (1 / u) / Real.log (Y ^ (1 / u)) := by
      exact add_le_add hmain (le_refl _)
    _ = C * (Y / Real.log Y ^ 2) +
          Y ^ (1 / u) / Real.log (Y ^ (1 / u)) + 1 := by ring

/-- A one-sided form for a negative coefficient. -/
private theorem maynardRoughCount_le_buchstabMain_add_error
    {Y y u C : Real} (hY : 0 < Y) (hy : 2 ≤ y)
    (hEstimate :
      |(buchstabPhi Y y : Real) -
        (buchstabFunction u * Y / Real.log y - y / Real.log y)| ≤
        C * (Y / Real.log Y ^ 2)) :
    (maynardRoughCount Y y : Real) ≤
      buchstabFunction u * Y / Real.log y +
        C * (Y / Real.log Y ^ 2) := by
  have hrough := maynardRoughCount_le_buchstabPhi (Y := Y) (y := y) hY
  have hsecondary : 0 ≤ y / Real.log y := by
    exact le_of_lt (div_pos (by linarith) (Real.log_pos (by linarith)))
  have hupper := (abs_le.mp hEstimate).2
  linarith

/-- The one-sided weak-threshold estimate used when the count has a negative
coefficient.  The secondary term is retained in the proof and discarded only
in the favorable direction. -/
theorem exists_maynardRoughCount_upper :
    ∀ U : Real, 1 ≤ U →
      ∃ C : Real, 0 < C ∧
        ∀ Y y u : Real, 0 < Y → 2 ≤ y → 1 ≤ u → u ≤ U →
          u = Real.log Y / Real.log y →
          (maynardRoughCount Y y : Real) ≤
            buchstabFunction u * Y / Real.log y +
              C * (Y / Real.log Y ^ 2) := by
  intro U hU
  obtain ⟨C, hC, hEstimate⟩ := buchstabPhi_estimate U hU
  refine ⟨C, hC, ?_⟩
  intro Y y u hY hy hu huU hparam
  exact maynardRoughCount_le_buchstabMain_add_error hY hy
    (hEstimate Y y u hY hy hu huU hparam)

/- The strict carrier is used only through this upper estimate in the present
   slice. An exact prime-threshold fiber identity is intentionally deferred. -/
theorem exists_maynardStrictRoughCount_upper :
    ∀ U : Real, 1 ≤ U →
      ∃ C : Real, 0 < C ∧
        ∀ Y y u : Real, 0 < Y → 2 ≤ y → 1 ≤ u → u ≤ U →
          u = Real.log Y / Real.log y →
          (maynardStrictRoughCount Y y : Real) ≤
            buchstabFunction u * Y / Real.log y +
              C * (Y / Real.log Y ^ 2) := by
  intro U hU
  obtain ⟨C, hC, hWeak⟩ := exists_maynardRoughCount_upper U hU
  refine ⟨C, hC, ?_⟩
  intro Y y u hY hy hu huU hparam
  have hNat := maynardStrictRoughCount_le_maynardRoughCount Y y
  have hReal : (maynardStrictRoughCount Y y : Real) ≤
      (maynardRoughCount Y y : Real) := by
    exact_mod_cast hNat
  exact hReal.trans (hWeak Y y u hY hy hu huU hparam)

end PrimesRestrictedDigits
