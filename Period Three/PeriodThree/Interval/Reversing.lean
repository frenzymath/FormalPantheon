module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by strict-step arithmetic)

/-!
# Reversing nested intervals

This file gives the strict pullback construction used in the reversing branch
of the Li--Yorke interval argument.
-/

@[expose] public section

open Set

namespace PeriodThree

private theorem existsLastLevel
    {G : ℝ → ℝ} {p q x y : ℝ}
    (hG : ContinuousOn G (Icc p q)) (hx : x ∈ Icc p q) (hxy : G x = y) :
    ∃ r ∈ Icc p q, G r = y ∧ ∀ x ∈ Icc p q, G x = y → x ≤ r := by
  let A : Set (Icc p q) := {x | G x = y}
  letI : CompactSpace (Icc p q) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hclosed : IsClosed A := isClosed_eq hG.restrict continuous_const
  obtain ⟨r, hr, hrmax⟩ := hclosed.isCompact.exists_isMaxOn
    ⟨_, (show (⟨x, hx⟩ : Icc p q) ∈ A from hxy)⟩
    continuous_subtype_val.continuousOn
  exact ⟨r, r.property, hr, fun x hx hxy => @hrmax ⟨x, hx⟩ hxy⟩

private theorem existsFirstLevel
    {G : ℝ → ℝ} {p q x y : ℝ}
    (hG : ContinuousOn G (Icc p q)) (hx : x ∈ Icc p q) (hxy : G x = y) :
    ∃ s ∈ Icc p q, G s = y ∧ ∀ x ∈ Icc p q, G x = y → s ≤ x := by
  let A : Set (Icc p q) := {x | G x = y}
  letI : CompactSpace (Icc p q) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hclosed : IsClosed A := isClosed_eq hG.restrict continuous_const
  obtain ⟨s, hs, hsmin⟩ := hclosed.isCompact.exists_isMinOn
    ⟨_, (show (⟨x, hx⟩ : Icc p q) ∈ A from hxy)⟩
    continuous_subtype_val.continuousOn
  exact ⟨s, s.property, hs, fun x hx hxy => @hsmin ⟨x, hx⟩ hxy⟩

/-- A strict reversing crossing has a compact subinterval on which the image
is exactly the original interval and interior points map to interior points.
This is the endpoint-selection step in [LY75, Lemma 0, p. 987]. -/
theorem existsStrictReversingInterval
    {G : ℝ → ℝ} {u v : ℝ} (huv : u < v)
    (hG : ContinuousOn G (Icc u v))
    (hu : v ≤ G u) (hv : G v ≤ u) :
    ∃ r s : ℝ,
      u ≤ r ∧ r < s ∧ s ≤ v ∧
      G r = v ∧ G s = u ∧
      G '' Icc r s = Icc u v ∧
      MapsTo G (Ioo r s) (Ioo u v) := by
  have huv' : u ≤ v := huv.le
  have hv_image : v ∈ G '' Icc u v := by
    apply (intermediate_value_Icc' huv' hG)
    exact ⟨hv.trans huv', hu⟩
  obtain ⟨p, hp, hpv⟩ := hv_image
  obtain ⟨r, hrI, hrv, hrmax⟩ := existsLastLevel hG hp hpv
  have hrv_sub : Icc r v ⊆ Icc u v := by
    intro x hx
    exact ⟨hrI.1.trans hx.1, hx.2⟩
  have hu_image : u ∈ G '' Icc r v := by
    apply intermediate_value_Icc' hrI.2 (hG.mono hrv_sub)
    exact ⟨hv, by simpa [hrv] using huv.le⟩
  obtain ⟨q, hq, hqu⟩ := hu_image
  obtain ⟨s, hsI, hsu, hsmin⟩ :=
    existsFirstLevel (hG.mono hrv_sub) hq hqu
  have hrs_le : r ≤ s := hsI.1
  have hrs : r < s := by
    refine lt_of_le_of_ne hrs_le ?_
    intro h
    have : v = u := by rw [← hrv, h, hsu]
    exact huv.ne this.symm
  have hrs_sub : Icc r s ⊆ Icc u v := by
    intro x hx
    exact ⟨hrI.1.trans hx.1, hx.2.trans hsI.2⟩
  have himage : G '' Icc r s = Icc u v := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      constructor
      · by_contra hxu
        have hxu' : G x < u := lt_of_not_ge hxu
        have hrx_sub : Icc r x ⊆ Icc u v := by
          intro z hz
          exact hrs_sub ⟨hz.1, hz.2.trans hx.2⟩
        obtain ⟨z, hz, hzu⟩ := intermediate_value_Icc' hx.1
          (hG.mono hrx_sub) (by simpa [hrv] using ⟨hxu'.le, huv.le⟩)
        have hsz : s ≤ z := hsmin z
          ⟨hz.1, hz.2.trans hx.2 |>.trans hsI.2⟩ hzu
        have hzs : z ≤ s := hz.2.trans hx.2
        have hzs_eq : z = s := le_antisymm hzs hsz
        have hxs_eq : x = s := le_antisymm hx.2 (hzs_eq ▸ hz.2)
        exact (ne_of_lt hxu') (by simpa [hxs_eq] using hsu)
      · by_contra hxv
        have hxv' : v < G x := lt_of_not_ge hxv
        have hxs_sub : Icc x s ⊆ Icc u v := by
          intro z hz
          exact hrs_sub ⟨hx.1.trans hz.1, hz.2⟩
        obtain ⟨z, hz, hzv⟩ := intermediate_value_Icc' hx.2
          (hG.mono hxs_sub) (by simpa [hsu] using ⟨huv.le, hxv'.le⟩)
        have hzr : z ≤ r := hrmax z (hxs_sub hz) hzv
        have hrz : r ≤ z := hx.1.trans hz.1
        have hzr_eq : z = r := le_antisymm hzr hrz
        have hrx_eq : x = r := le_antisymm (hzr_eq ▸ hz.1) hx.1
        exact (ne_of_gt hxv') (by simpa [hrx_eq] using hrv)
    · simpa [hrv, hsu] using intermediate_value_Icc' hrs_le (hG.mono hrs_sub)
  refine ⟨r, s, hrI.1, hrs, hsI.2, hrv, hsu, himage, ?_⟩
  intro x hx
  have hx_image : G x ∈ Icc u v := himage ▸ ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
  refine ⟨lt_of_le_of_ne hx_image.1 ?_, lt_of_le_of_ne hx_image.2 ?_⟩
  · intro h
    have hsx : s ≤ x := hsmin x
      ⟨hx.1.le, hx.2.le.trans hsI.2⟩ h.symm
    exact (not_le_of_gt hx.2) hsx
  · intro h
    have hxr : x ≤ r := hrmax x (hrs_sub ⟨hx.1.le, hx.2.le⟩) h
    exact (not_le_of_gt hx.1) hxr

/-- The recursively selected compact intervals in the reversing construction
of [LY75, Lemma 0, p. 987]. -/
structure ReversingNest (F : ℝ → ℝ) (b c : ℝ) where
  /-- Lower endpoint at each recursive level. -/
  lower : ℕ → ℝ
  /-- Upper endpoint at each recursive level. -/
  upper : ℕ → ℝ
  /-- Initial lower endpoint. -/
  lower_zero : lower 0 = b
  /-- Initial upper endpoint. -/
  upper_zero : upper 0 = c
  /-- Every selected interval is nondegenerate. -/
  lower_lt_upper : ∀ n, lower n < upper n
  /-- Successive intervals are nested. -/
  nested : ∀ n, Icc (lower (n + 1)) (upper (n + 1)) ⊆ Icc (lower n) (upper n)
  /-- The map sends each next lower endpoint to the current upper endpoint. -/
  map_lower : ∀ n, F (lower (n + 1)) = upper n
  /-- The map sends each next upper endpoint to the current lower endpoint. -/
  map_upper : ∀ n, F (upper (n + 1)) = lower n
  /-- Interior points map into the preceding interior. -/
  maps_interior : ∀ n, MapsTo F
    (Ioo (lower (n + 1)) (upper (n + 1)))
    (Ioo (lower n) (upper n))

private structure CrossingState (F : ℝ → ℝ) (b c : ℝ) where
  lower : ℝ
  upper : ℝ
  lower_lt_upper : lower < upper
  subset_base : Icc lower upper ⊆ Icc b c
  upper_le_image_lower : upper ≤ F lower
  image_upper_le_lower : F upper ≤ lower

private noncomputable def stepWitness {F : ℝ → ℝ} {b c : ℝ}
    (hF : ContinuousOn F (Icc b c)) (S : CrossingState F b c) : ℝ × ℝ :=
  let H := existsStrictReversingInterval S.lower_lt_upper
    (hF.mono S.subset_base) S.upper_le_image_lower S.image_upper_le_lower
  (Classical.choose H, Classical.choose (Classical.choose_spec H))

private theorem stepWitness_spec {F : ℝ → ℝ} {b c : ℝ}
    (hF : ContinuousOn F (Icc b c)) (S : CrossingState F b c) :
    S.lower ≤ (stepWitness hF S).1 ∧ (stepWitness hF S).1 < (stepWitness hF S).2 ∧
      (stepWitness hF S).2 ≤ S.upper ∧
      F (stepWitness hF S).1 = S.upper ∧ F (stepWitness hF S).2 = S.lower ∧
      F '' Icc (stepWitness hF S).1 (stepWitness hF S).2 = Icc S.lower S.upper ∧
      MapsTo F (Ioo (stepWitness hF S).1 (stepWitness hF S).2)
        (Ioo S.lower S.upper) :=
  by
    let H := existsStrictReversingInterval S.lower_lt_upper
      (hF.mono S.subset_base) S.upper_le_image_lower S.image_upper_le_lower
    simpa [stepWitness, H] using
      (Classical.choose_spec (Classical.choose_spec H) :
        S.lower ≤ Classical.choose H ∧
          Classical.choose H < Classical.choose (Classical.choose_spec H) ∧
          Classical.choose (Classical.choose_spec H) ≤ S.upper ∧
          F (Classical.choose H) = S.upper ∧
            F (Classical.choose (Classical.choose_spec H)) = S.lower ∧
          F '' Icc (Classical.choose H) (Classical.choose (Classical.choose_spec H)) =
            Icc S.lower S.upper ∧
          MapsTo F (Ioo (Classical.choose H) (Classical.choose (Classical.choose_spec H)))
            (Ioo S.lower S.upper))

private noncomputable def strictStep {F : ℝ → ℝ} {b c : ℝ}
    (hF : ContinuousOn F (Icc b c)) (S : CrossingState F b c) : CrossingState F b c where
  lower := (stepWitness hF S).1
  upper := (stepWitness hF S).2
  lower_lt_upper := (stepWitness_spec hF S).2.1
  subset_base := (Icc_subset_Icc (stepWitness_spec hF S).1 (stepWitness_spec hF S).2.2.1).trans
    S.subset_base
  upper_le_image_lower := by
    rw [(stepWitness_spec hF S).2.2.2.1]
    exact (stepWitness_spec hF S).2.2.1
  image_upper_le_lower := by
    rw [(stepWitness_spec hF S).2.2.2.2.1]
    exact (stepWitness_spec hF S).1

private theorem strictStep_nested {F : ℝ → ℝ} {b c : ℝ}
    (hF : ContinuousOn F (Icc b c)) (S : CrossingState F b c) :
    Icc (strictStep hF S).lower (strictStep hF S).upper ⊆ Icc S.lower S.upper :=
  Icc_subset_Icc (stepWitness_spec hF S).1 (stepWitness_spec hF S).2.2.1

private theorem strictStep_map_lower {F : ℝ → ℝ} {b c : ℝ}
    (hF : ContinuousOn F (Icc b c)) (S : CrossingState F b c) :
    F (strictStep hF S).lower = S.upper :=
  (stepWitness_spec hF S).2.2.2.1

private theorem strictStep_map_upper {F : ℝ → ℝ} {b c : ℝ}
    (hF : ContinuousOn F (Icc b c)) (S : CrossingState F b c) :
    F (strictStep hF S).upper = S.lower :=
  (stepWitness_spec hF S).2.2.2.2.1

private theorem strictStep_maps_interior {F : ℝ → ℝ} {b c : ℝ}
    (hF : ContinuousOn F (Icc b c)) (S : CrossingState F b c) :
    MapsTo F (Ioo (strictStep hF S).lower (strictStep hF S).upper)
      (Ioo S.lower S.upper) :=
  (stepWitness_spec hF S).2.2.2.2.2.2

/-- A reversing crossing produces nested compact pullbacks with exchanged
endpoints, following the recursive construction in [LY75, Lemma 0, p. 987]. -/
theorem existsReversingNest
    {F : ℝ → ℝ} {b c : ℝ} (hbc : b < c)
    (hF : ContinuousOn F (Icc b c))
    (hFb : F b = c) (hFc : F c ≤ b) :
    Nonempty (ReversingNest F b c) := by
  let S0 : CrossingState F b c :=
    ⟨b, c, hbc, subset_rfl, hFb.ge, hFc⟩
  let states : ℕ → CrossingState F b c := fun n => (strictStep hF)^[n] S0
  have states_zero : states 0 = S0 := by simp [states]
  have states_succ (n : ℕ) : states (n + 1) = strictStep hF (states n) := by
    simp [states, Function.iterate_succ_apply']
  refine ⟨{
    lower := fun n => (states n).lower
    upper := fun n => (states n).upper
    lower_zero := by simp [states_zero, S0]
    upper_zero := by simp [states_zero, S0]
    lower_lt_upper := fun n => (states n).lower_lt_upper
    nested := fun n => by rw [states_succ]; exact strictStep_nested hF (states n)
    map_lower := fun n => by rw [states_succ]; exact strictStep_map_lower hF (states n)
    map_upper := fun n => by rw [states_succ]; exact strictStep_map_upper hF (states n)
    maps_interior := fun n => by rw [states_succ]; exact strictStep_maps_interior hF (states n)
  }⟩

end PeriodThree
