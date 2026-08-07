module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by endpoint arithmetic)

/-!
# Compact interval pullbacks

This file formalizes the compact pullback construction from Li and Yorke's
Lemma 0.  It extracts a source interval whose image is exactly a prescribed
compact interval, without assuming monotonicity of the map.
-/

@[expose] public section

open Set

namespace PeriodThree

private theorem existsLastPreimage
    {G : ℝ → ℝ} {p q u : ℝ} (hpq : p ≤ q)
    (hG : ContinuousOn G (Icc p q)) (hp : G p = u) :
    ∃ r ∈ Icc p q, G r = u ∧ ∀ x ∈ Icc p q, G x = u → x ≤ r := by
  let A : Set (Icc p q) := {x | G x = u}
  letI : CompactSpace (Icc p q) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hAclosed : IsClosed A := isClosed_eq hG.restrict continuous_const
  have hAcompact : IsCompact A := hAclosed.isCompact
  have hp_mem : (⟨p, left_mem_Icc.mpr hpq⟩ : Icc p q) ∈ A := hp
  obtain ⟨r, hrA, hrmax⟩ :=
    hAcompact.exists_isMaxOn ⟨_, hp_mem⟩ continuous_subtype_val.continuousOn
  refine ⟨r, r.property, hrA, ?_⟩
  intro x hxI hxG
  exact @hrmax ⟨x, hxI⟩ hxG

private theorem existsFirstPreimage
    {G : ℝ → ℝ} {p q v : ℝ} (hpq : p ≤ q)
    (hG : ContinuousOn G (Icc p q)) (hq : G q = v) :
    ∃ s ∈ Icc p q, G s = v ∧ ∀ x ∈ Icc p q, G x = v → s ≤ x := by
  let A : Set (Icc p q) := {x | G x = v}
  letI : CompactSpace (Icc p q) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hAclosed : IsClosed A := isClosed_eq hG.restrict continuous_const
  have hAcompact : IsCompact A := hAclosed.isCompact
  have hq_mem : (⟨q, right_mem_Icc.mpr hpq⟩ : Icc p q) ∈ A := hq
  obtain ⟨s, hsA, hsmin⟩ :=
    hAcompact.exists_isMinOn ⟨_, hq_mem⟩ continuous_subtype_val.continuousOn
  refine ⟨s, s.property, hsA, ?_⟩
  intro x hxI hxG
  exact @hsmin ⟨x, hxI⟩ hxG

private theorem imageIntervalEqOfOrderedPreimages
    {G : ℝ → ℝ} {p q u v : ℝ} (hpq : p ≤ q) (huv : u ≤ v)
    (hG : ContinuousOn G (Icc p q)) (hp : G p = u) (hq : G q = v) :
    ∃ r s : ℝ, r ≤ s ∧ Icc r s ⊆ Icc p q ∧ G '' Icc r s = Icc u v := by
  obtain ⟨r, hrI, hrG, hrmax⟩ := existsLastPreimage hpq hG hp
  have hrq : r ≤ q := hrI.2
  have hrq_sub : Icc r q ⊆ Icc p q := by
    intro x hx
    exact ⟨hrI.1.trans hx.1, hx.2⟩
  obtain ⟨s, hsI, hsG, hsmin⟩ :=
    existsFirstPreimage hrq (hG.mono hrq_sub) hq
  have hrs : r ≤ s := hsI.1
  have hrs_sub : Icc r s ⊆ Icc p q := by
    intro x hx
    exact ⟨hrI.1.trans hx.1, hx.2.trans hsI.2⟩
  refine ⟨r, s, hrs, hrs_sub, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · by_contra hxu
      have hxu' : G x < u := lt_of_not_ge hxu
      have hxs : x ≤ s := hx.2
      have hxs_sub : Icc x s ⊆ Icc p q := by
        intro z hz
        exact ⟨(hrs_sub hx).1.trans hz.1, hz.2.trans hsI.2⟩
      have hu_between : u ∈ Icc (G x) (G s) := by
        rw [hsG]
        exact ⟨hxu'.le, huv⟩
      obtain ⟨z, hzI, hzG⟩ :=
        intermediate_value_Icc hxs (hG.mono hxs_sub) hu_between
      have hz_source : z ∈ Icc p q := hxs_sub hzI
      have hz_le_r : z ≤ r := hrmax z hz_source hzG
      have hr_le_z : r ≤ z := hx.1.trans hzI.1
      have hz_eq : z = r := le_antisymm hz_le_r hr_le_z
      have hx_eq : x = r := le_antisymm (hz_eq ▸ hzI.1) hx.1
      exact (not_lt_of_ge (by simpa [hx_eq] using hrG.symm.le)) hxu'
    · by_contra hxv
      have hxv' : v < G x := lt_of_not_ge hxv
      have hrx : r ≤ x := hx.1
      have hrx_sub : Icc r x ⊆ Icc r q := by
        intro z hz
        exact ⟨hz.1, hz.2.trans (hx.2.trans hsI.2)⟩
      have hv_between : v ∈ Icc (G r) (G x) := by
        rw [hrG]
        exact ⟨huv, hxv'.le⟩
      obtain ⟨z, hzI, hzG⟩ :=
        intermediate_value_Icc hrx ((hG.mono hrq_sub).mono hrx_sub) hv_between
      have hz_le_s : z ≤ s := hzI.2.trans hx.2
      have hs_le_z : s ≤ z := hsmin z (hrx_sub hzI) hzG
      have hz_eq : z = s := le_antisymm hz_le_s hs_le_z
      have hx_eq : x = s := le_antisymm hx.2 (hz_eq ▸ hzI.2)
      exact (not_lt_of_ge (by simpa [hx_eq] using hsG.le)) hxv'
  · simpa [hrG, hsG] using intermediate_value_Icc hrs (hG.mono hrs_sub)

private theorem imageIntervalEqOfReversedPreimages
    {G : ℝ → ℝ} {p q u v : ℝ} (hpq : p ≤ q) (huv : u ≤ v)
    (hG : ContinuousOn G (Icc p q)) (hp : G p = v) (hq : G q = u) :
    ∃ r s : ℝ, r ≤ s ∧ Icc r s ⊆ Icc p q ∧ G '' Icc r s = Icc u v := by
  obtain ⟨r, s, hrs, hrs_sub, himage⟩ :=
    imageIntervalEqOfOrderedPreimages
      (G := fun z => -G z) (p := p) (q := q) (u := -v) (v := -u)
      hpq (by linarith : -v ≤ -u) hG.neg
      (by simpa using congrArg Neg.neg hp)
      (by simpa using congrArg Neg.neg hq)
  refine ⟨r, s, hrs, hrs_sub, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hyneg_image : -G x ∈ (fun z => -G z) '' Icc r s := ⟨x, hx, rfl⟩
    have hyneg : -G x ∈ Icc (-v) (-u) := himage ▸ hyneg_image
    constructor <;> linarith [hyneg.1, hyneg.2]
  · intro hy
    have hyneg : -y ∈ Icc (-v) (-u) := by
      constructor <;> linarith [hy.1, hy.2]
    obtain ⟨z, hz, hzg⟩ := (himage ▸ hyneg : -y ∈ (fun z => -G z) '' Icc r s)
    refine ⟨z, hz, ?_⟩
    linarith

/-- A compact target interval covered by the image of an interval has a compact
source subinterval whose image is exactly the target. This is [LY75, Lemma 0,
p. 987]. -/
theorem existsCompactIntervalPreimage
    {I : Set ℝ} (hI : I.OrdConnected) {G : ℝ → ℝ}
    (hG : ContinuousOn G I) {u v : ℝ} (huv : u ≤ v)
    (hT : Icc u v ⊆ G '' I) :
    ∃ r s : ℝ, r ≤ s ∧ Icc r s ⊆ I ∧ G '' Icc r s = Icc u v := by
  by_cases huv_eq : u = v
  · obtain ⟨x, hxI, hxG⟩ := hT (show u ∈ Icc u v by simp [huv_eq])
    refine ⟨x, x, le_rfl, ?_, ?_⟩
    · simp [hxI]
    · simp [huv_eq, hxG]
  obtain ⟨x, hxI, hxG⟩ := hT (left_mem_Icc.mpr huv)
  obtain ⟨y, hyI, hyG⟩ := hT (right_mem_Icc.mpr huv)
  have hxy_source : Icc x y ⊆ I := hI.out hxI hyI
  by_cases hxy : x ≤ y
  · obtain ⟨r, s, hrs, hrs_sub, himage⟩ :=
      imageIntervalEqOfOrderedPreimages hxy huv (hG.mono hxy_source) hxG hyG
    exact ⟨r, s, hrs, hrs_sub.trans hxy_source, himage⟩
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hyx_source : Icc y x ⊆ I := hI.out hyI hxI
    obtain ⟨r, s, hrs, hrs_sub, himage⟩ :=
      imageIntervalEqOfReversedPreimages hyx huv (hG.mono hyx_source) hyG hxG
    exact ⟨r, s, hrs, hrs_sub.trans hyx_source, himage⟩

end PeriodThree
