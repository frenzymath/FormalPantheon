import BoundedGaps.Maynard.MaynardS1CrossYTransform

noncomputable section

/-!
# Starred coprimality for surviving S1 cross terms

Nonzero left and right Y factors force the coprimality restrictions denoted by
Maynard's starred cross-variable sum.
-/

namespace BoundedGaps.Maynard

def IsStarredCrossTuple
    (H : Finset ℕ) (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : Prop :=
  (∀ (ab : H × H) (hab : ab ∈ offDiagonalPairs H),
      Nat.Coprime (s ab hab) (u ab.1) ∧
        Nat.Coprime (s ab hab) (u ab.2)) ∧
    ∀ (ab cd : H × H)
      (hab : ab ∈ offDiagonalPairs H) (hcd : cd ∈ offDiagonalPairs H),
      ab ≠ cd → (ab.1 = cd.1 ∨ ab.2 = cd.2) →
        Nat.Coprime (s ab hab) (s cd hcd)

theorem u_dvd_leftCrossLowerTuple
    (H : Finset ℕ) (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) (h : H) :
    u h ∣ leftCrossLowerTuple H u s h :=
  Nat.dvd_lcm_left _ _

theorem u_dvd_rightCrossLowerTuple
    (H : Finset ℕ) (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) (h : H) :
    u h ∣ rightCrossLowerTuple H u s h :=
  Nat.dvd_lcm_left _ _

theorem cross_dvd_leftCrossLowerTuple
    {H : Finset ℕ}
    (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (ab : H × H) (hab : ab ∈ offDiagonalPairs H) :
    s ab hab ∣ leftCrossLowerTuple H u s ab.1 := by
  apply dvd_trans ?_ (Nat.dvd_lcm_right _ _)
  unfold outgoingCrossLcm
  let x : ↑(offDiagonalPairs H) := ⟨ab, hab⟩
  have hx : x ∈ (offDiagonalPairs H).attach.filter (fun z => z.1.1 = ab.1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, rfl⟩
  simpa [x] using Finset.dvd_lcm hx

theorem cross_dvd_rightCrossLowerTuple
    {H : Finset ℕ}
    (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (ab : H × H) (hab : ab ∈ offDiagonalPairs H) :
    s ab hab ∣ rightCrossLowerTuple H u s ab.2 := by
  apply dvd_trans ?_ (Nat.dvd_lcm_right _ _)
  unfold incomingCrossLcm
  let x : ↑(offDiagonalPairs H) := ⟨ab, hab⟩
  have hx : x ∈ (offDiagonalPairs H).attach.filter (fun z => z.1.2 = ab.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, rfl⟩
  simpa [x] using Finset.dvd_lcm hx

theorem leftCrossYFactor_ne_zero_y_ne_zero
    {H : Finset ℕ} {y : (H → ℕ) → ℝ}
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (h : leftCrossYFactor H y u s ≠ 0) :
    y (leftCrossLowerTuple H u s) ≠ 0 := by
  intro hy
  apply h
  simp [leftCrossYFactor, hy]

theorem rightCrossYFactor_ne_zero_y_ne_zero
    {H : Finset ℕ} {y : (H → ℕ) → ℝ}
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (h : rightCrossYFactor H y u s ≠ 0) :
    y (rightCrossLowerTuple H u s) ≠ 0 := by
  intro hy
  apply h
  simp [rightCrossYFactor, hy]

theorem isStarredCrossTuple_of_yFactors_ne_zero
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hl : leftCrossYFactor H y u s ≠ 0)
    (hr : rightCrossYFactor H y u s ≠ 0) :
    IsStarredCrossTuple H u s := by
  have hlSupport := hy _ (leftCrossYFactor_ne_zero_y_ne_zero hl)
  have hrSupport := hy _ (rightCrossYFactor_ne_zero_y_ne_zero hr)
  constructor
  · intro ab hab
    have habNe : ab.1 ≠ ab.2 := (Finset.mem_filter.mp hab).2
    have hright := hrSupport.coordinates_coprime habNe
    have hleft := hlSupport.coordinates_coprime habNe
    exact ⟨
      Nat.Coprime.of_dvd
        (cross_dvd_rightCrossLowerTuple u s ab hab)
        (u_dvd_rightCrossLowerTuple H u s ab.1) hright.symm,
      Nat.Coprime.of_dvd
        (cross_dvd_leftCrossLowerTuple u s ab hab)
        (u_dvd_leftCrossLowerTuple H u s ab.2) hleft⟩
  · intro ab cd hab hcd habcd hshared
    rcases hshared with hfirst | hsecond
    · have hne : ab.2 ≠ cd.2 := by
        intro h
        apply habcd
        exact Prod.ext hfirst h
      have hcop := hrSupport.coordinates_coprime hne
      exact Nat.Coprime.of_dvd
        (cross_dvd_rightCrossLowerTuple u s ab hab)
        (cross_dvd_rightCrossLowerTuple u s cd hcd) hcop
    · have hne : ab.1 ≠ cd.1 := by
        intro h
        apply habcd
        exact Prod.ext h hsecond
      have hcop := hlSupport.coordinates_coprime hne
      exact Nat.Coprime.of_dvd
        (cross_dvd_leftCrossLowerTuple u s ab hab)
        (cross_dvd_leftCrossLowerTuple u s cd hcd) hcop

end BoundedGaps.Maynard
