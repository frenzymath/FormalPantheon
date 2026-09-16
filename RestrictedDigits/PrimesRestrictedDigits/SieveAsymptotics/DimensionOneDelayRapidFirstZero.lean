import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayRapidFoundations

/-!
# Bounded first-zero data for the dimension-one rapid defect

This repairs the unbounded first-infimum step in Iwaniec's proof of Lemma 16. A bad witness
first bounds the search interval; a compact least zero and a second IVT then give strict
negativity before it.
-/

open Set

namespace PrimesRestrictedDigits

private theorem exists_firstZero_after_negativeInterval
    {D : Real -> Real} {a b t : Real}
    (hab : a <= b)
    (hDcont : ContinuousOn D (Ici a))
    (hDneg : ∀ x ∈ Icc a b, D x < 0)
    (hat : a <= t) (htD : 0 <= D t) :
    ∃ u, b < u ∧ u <= t ∧ D u = 0 ∧
      ∀ x ∈ Ico a u, D x < 0 := by
  have hDb : D b < 0 := hDneg b ⟨hab, le_rfl⟩
  have hbt : b < t := by
    by_contra h
    linarith [hDneg t ⟨hat, le_of_not_gt h⟩]
  have hDcontIcc : ContinuousOn D (Icc b t) :=
    hDcont.mono fun x hx => hab.trans hx.1
  obtain ⟨z, hzIcc, hzD⟩ := intermediate_value_Icc hbt.le hDcontIcc
    (show (0 : Real) ∈ Icc (D b) (D t) from ⟨hDb.le, htD⟩)
  let zeroSet := Icc b t ∩ D ⁻¹' ({0} : Set Real)
  have hclosed : IsClosed zeroSet := by
    dsimp [zeroSet]
    exact hDcontIcc.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hcompact : IsCompact zeroSet :=
    IsCompact.of_isClosed_subset isCompact_Icc hclosed inter_subset_left
  obtain ⟨u, huZero, huLeast⟩ :=
    hcompact.exists_isLeast ⟨z, hzIcc, by simpa using hzD⟩
  have huIcc : u ∈ Icc b t := huZero.1
  have huD : D u = 0 := by simpa using huZero.2
  have hbu : b < u := by
    apply lt_of_le_of_ne huIcc.1
    intro hbuEq
    have : u = b := hbuEq.symm
    subst u
    linarith
  refine ⟨u, hbu, huIcc.2, huD, ?_⟩
  intro x hx
  by_cases hxb : x <= b
  · exact hDneg x ⟨hx.1, hxb⟩
  have hbx : b < x := lt_of_not_ge hxb
  by_contra hxNeg
  have hxD : 0 <= D x := le_of_not_gt hxNeg
  have hDcontBx : ContinuousOn D (Icc b x) :=
    hDcont.mono fun y hy => hab.trans hy.1
  obtain ⟨y, hyIcc, hyD⟩ := intermediate_value_Icc hbx.le hDcontBx
    (show (0 : Real) ∈ Icc (D b) (D x) from ⟨hDb.le, hxD⟩)
  have hyZero : y ∈ zeroSet := by
    refine ⟨⟨hyIcc.1, hyIcc.2.trans (hx.2.le.trans huIcc.2)⟩, ?_⟩
    simpa using hyD
  have huy : u <= y := huLeast hyZero
  linarith [hyIcc.2, hx.2]

private theorem dimensionOneDelayRapidDefect_neg_on_base
    {s : Real} (hs : s ∈ Icc (3 : Real) 128) :
    dimensionOneDelayRapidDefect s < 0 := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hRatio0 : 0 <= s / 128 := by positivity
  have hRatio1 : s / 128 <= 1 :=
    (div_le_one (by norm_num : (0 : Real) < 128)).2 hs.2
  have hLog : dimensionOneDelayLogWeight s <= 0 := by
    unfold dimensionOneDelayLogWeight
    exact Real.log_nonpos hRatio0 hRatio1
  have hProduct :
      s * dimensionOneDelaySum s * dimensionOneDelayLogWeight s <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hs0.le (dimensionOneDelaySum_pos hs0).le) hLog
  have hShiftPos : 0 < dimensionOneDelaySum (s - 1) :=
    dimensionOneDelaySum_pos (by linarith [hs.1])
  unfold dimensionOneDelayRapidDefect
  linarith

/-- Any nonnegative rapid defect produces a bounded first zero and strict
decrease of the rapid weighted sum up to that zero. -/
theorem dimensionOneDelayRapidDefect_firstZero
    {t : Real} (ht : 3 <= t)
    (hbad : 0 <= dimensionOneDelayRapidDefect t) :
    ∃ u, 128 < u ∧ u <= t ∧ dimensionOneDelayRapidDefect u = 0 ∧
      StrictAntiOn dimensionOneDelayRapidWeightedSum (Icc 3 u) := by
  have hDcont : ContinuousOn dimensionOneDelayRapidDefect (Ici (3 : Real)) :=
    dimensionOneDelayRapidDefect_continuousOn.mono fun s hs => by
      change 3 <= s at hs
      change 1 < s
      linarith
  obtain ⟨u, hu128, hut, huD, hPrior⟩ :=
    exists_firstZero_after_negativeInterval
      (D := dimensionOneDelayRapidDefect)
      (a := (3 : Real)) (b := 128) (t := t)
      (by norm_num) hDcont
      (fun s hs => dimensionOneDelayRapidDefect_neg_on_base hs) ht hbad
  refine ⟨u, hu128, hut, huD, ?_⟩
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (D := Icc (3 : Real) u)
    (f' := fun s => dimensionOneDelayRapidWeight s * s *
      dimensionOneDelayRapidDefect s)
    (convex_Icc 3 u)
    (dimensionOneDelayRapidWeightedSum_continuousOn.mono fun s hs => by
      change 0 < s
      linarith [hs.1]) ?_ ?_
  · intro s hs
    rw [interior_Icc] at hs
    exact (dimensionOneDelayRapidWeightedSum_hasDerivAt hs.1).hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact mul_neg_of_pos_of_neg
      (mul_pos (by
        unfold dimensionOneDelayRapidWeight
        exact Real.exp_pos _) (by linarith [hs.1]))
      (hPrior s ⟨hs.1.le, hs.2⟩)

end PrimesRestrictedDigits
