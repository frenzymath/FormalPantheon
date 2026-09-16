import PrimesRestrictedDigits.SieveAsymptotics.TypeIICubeGrid
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIInteriorFiber

/-!
# Projected Type II source-region geometry

This is the finite geometric classification used in the proof of Proposition 7.2. It replaces
the false literal cube identity in published Eq. (9.2) by relevant, interior, and remainder
grid families. No polytope boundary count is asserted here.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The ordered eta-simplex `Q_ell(eta)` used by Proposition 7.2. -/
def typeIIExponentSimplex {ell : Nat} (eta : Real) :
    Set (Fin ell -> Real) :=
  {e | (forall i, eta <= e i) ∧ Monotone e ∧ (∑ i, e i) = 1}

/-- The source-region conditions needed for boundary counting. -/
def IsTypeIISourceRegion {ell : Nat} (eta : Real)
    (region : Set (Fin ell -> Real)) : Prop :=
  region ⊆ typeIIExponentSimplex eta

/-- The source convenience condition for one fixed coordinate subset. -/
def IsTypeIIRegionConvenientFor {ell : Nat} (epsilon : Real)
    (region : Set (Fin ell -> Real)) (I : Finset (Fin ell)) : Prop :=
  ∀ e, e ∈ region ->
    (∑ i ∈ I, e i) ∈
      Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon)

/-- Proposition 7.2 chooses one coordinate subset before the region point. -/
def IsTypeIIRegionConvenient {ell : Nat} (epsilon : Real)
    (region : Set (Fin ell -> Real)) : Prop :=
  ∃ I, IsTypeIIRegionConvenientFor epsilon region I

/-- The canonical first-coordinate projection of a sum-one source region. -/
def typeIIProjectedRegion {k : Nat}
    (region : Set (Fin (k + 1) -> Real)) : Set (Fin k -> Real) :=
  {x | completeProjectedLogTuple x ∈ region}

/-- The doubled projected cube used to decide interior and remainder cells. -/
def typeIIDoubledProjectedCube {k : Nat} (delta : Real)
    (anchor : Fin k -> Nat) : Set (Fin k -> Real) :=
  projectedLogBox (scaledNaturalCubeAnchor delta anchor) (2 * delta)

/-- Grid anchors whose doubled cube meets the projected source region. -/
noncomputable def typeIIRelevantCubeAnchors {k : Nat} (delta : Real)
    (region : Set (Fin (k + 1) -> Real)) : Finset (Fin k -> Nat) := by
  classical
  exact (typeIINaturalCubeGrid k delta).filter fun anchor =>
    (typeIIDoubledProjectedCube delta anchor ∩
      typeIIProjectedRegion region).Nonempty

/-- Relevant anchors whose whole doubled cube lies in the projection. -/
noncomputable def typeIIInteriorCubeAnchors {k : Nat} (delta : Real)
    (region : Set (Fin (k + 1) -> Real)) : Finset (Fin k -> Nat) := by
  classical
  exact (typeIIRelevantCubeAnchors delta region).filter fun anchor =>
    typeIIDoubledProjectedCube delta anchor ⊆ typeIIProjectedRegion region

/-- Relevant anchors not wholly contained in the projected region. -/
noncomputable def typeIIRemainderCubeAnchors {k : Nat} (delta : Real)
    (region : Set (Fin (k + 1) -> Real)) : Finset (Fin k -> Nat) := by
  classical
  exact (typeIIRelevantCubeAnchors delta region).filter fun anchor =>
    ¬typeIIDoubledProjectedCube delta anchor ⊆ typeIIProjectedRegion region

/-- Sum one uniquely determines the last coordinate from the prefix. -/
theorem completeProjectedLogTuple_init_eq_of_sum_eq_one
    {k : Nat} {e : Fin (k + 1) -> Real} (hsum : (∑ i, e i) = 1) :
    completeProjectedLogTuple (Fin.init e) = e := by
  have hlast : 1 - ∑ i, Fin.init e i = e (Fin.last k) := by
    rw [Fin.sum_univ_castSucc] at hsum
    simp only [Fin.init_def]
    linarith
  rw [completeProjectedLogTuple, hlast]
  exact Fin.snoc_init_self e

@[simp] theorem mem_typeIIRelevantCubeAnchors
    {k : Nat} {delta : Real} {region : Set (Fin (k + 1) -> Real)}
    {anchor : Fin k -> Nat} :
    anchor ∈ typeIIRelevantCubeAnchors delta region <->
      anchor ∈ typeIINaturalCubeGrid k delta ∧
        (typeIIDoubledProjectedCube delta anchor ∩
          typeIIProjectedRegion region).Nonempty := by
  classical
  simp [typeIIRelevantCubeAnchors]

@[simp] theorem mem_typeIIInteriorCubeAnchors
    {k : Nat} {delta : Real} {region : Set (Fin (k + 1) -> Real)}
    {anchor : Fin k -> Nat} :
    anchor ∈ typeIIInteriorCubeAnchors delta region <->
      anchor ∈ typeIIRelevantCubeAnchors delta region ∧
        typeIIDoubledProjectedCube delta anchor ⊆
          typeIIProjectedRegion region := by
  classical
  simp [typeIIInteriorCubeAnchors]

@[simp] theorem mem_typeIIRemainderCubeAnchors
    {k : Nat} {delta : Real} {region : Set (Fin (k + 1) -> Real)}
    {anchor : Fin k -> Nat} :
    anchor ∈ typeIIRemainderCubeAnchors delta region <->
      anchor ∈ typeIIRelevantCubeAnchors delta region ∧
        ¬typeIIDoubledProjectedCube delta anchor ⊆
          typeIIProjectedRegion region := by
  classical
  simp [typeIIRemainderCubeAnchors]

/-- On sum-one regions, canonical completion is exactly the literal image
under `Fin.init`. -/
theorem image_init_eq_typeIIProjectedRegion
    {k : Nat} {eta : Real} {region : Set (Fin (k + 1) -> Real)}
    (hregion : IsTypeIISourceRegion eta region) :
    Fin.init '' region = typeIIProjectedRegion region := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    change completeProjectedLogTuple (Fin.init e) ∈ region
    have hsum : (∑ i, e i) = 1 := (hregion he).2.2
    have hcomplete := completeProjectedLogTuple_init_eq_of_sum_eq_one hsum
    simpa only [hcomplete] using he
  · intro hx
    exact ⟨completeProjectedLogTuple x, hx, init_completeProjectedLogTuple x⟩

/-- Relevant anchors split exactly into interior and remainder anchors. -/
theorem typeIIRelevantCubeAnchors_eq_interior_union_remainder
    {k : Nat} (delta : Real) (region : Set (Fin (k + 1) -> Real)) :
    typeIIRelevantCubeAnchors delta region =
      typeIIInteriorCubeAnchors delta region ∪
        typeIIRemainderCubeAnchors delta region := by
  classical
  ext anchor
  by_cases hsubset : typeIIDoubledProjectedCube delta anchor ⊆
      typeIIProjectedRegion region <;> simp [hsubset]

/-- The two parts of the relevant-anchor partition are disjoint. -/
theorem disjoint_typeIIInteriorCubeAnchors_typeIIRemainderCubeAnchors
    {k : Nat} (delta : Real) (region : Set (Fin (k + 1) -> Real)) :
    Disjoint (typeIIInteriorCubeAnchors delta region)
      (typeIIRemainderCubeAnchors delta region) := by
  classical
  rw [Finset.disjoint_left]
  intro anchor hinterior hremainder
  exact (mem_typeIIRemainderCubeAnchors.mp hremainder).2
    (mem_typeIIInteriorCubeAnchors.mp hinterior).2

/-- Every relevant anchor lies in the bounded grid. -/
theorem typeIIRelevantCubeAnchors_subset_grid
    {k : Nat} (delta : Real) (region : Set (Fin (k + 1) -> Real)) :
    typeIIRelevantCubeAnchors delta region ⊆
      typeIINaturalCubeGrid k delta := by
  intro anchor hanchor
  exact (mem_typeIIRelevantCubeAnchors.mp hanchor).1

/-- A relevant doubled cube inherits the source eta margin at its anchor. -/
theorem typeIIRelevantCubeAnchor_margin
    {k : Nat} {eta delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (hregion : IsTypeIISourceRegion eta region)
    (hsmall : 2 * delta <= eta / 2)
    {anchor : Fin k -> Nat}
    (hanchor : anchor ∈ typeIIRelevantCubeAnchors delta region) :
    forall i, eta / 2 <= scaledNaturalCubeAnchor delta anchor i := by
  obtain ⟨x, hxCube, hxRegion⟩ :=
    (mem_typeIIRelevantCubeAnchors.mp hanchor).2
  have hxSource := hregion hxRegion
  intro i
  have heta : eta <= x i := by
    simpa [typeIIProjectedRegion, completeProjectedLogTuple] using
      hxSource.1 i.castSucc
  have hupper := (hxCube i).2
  dsimp only [typeIIDoubledProjectedCube] at hxCube
  linarith

/-- A relevant anchor has room for the final coordinate. -/
theorem typeIIRelevantCubeAnchor_room
    {k : Nat} {eta delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (heta : 0 < eta) (hk : 0 < k)
    (hregion : IsTypeIISourceRegion eta region)
    {anchor : Fin k -> Nat}
    (hanchor : anchor ∈ typeIIRelevantCubeAnchors delta region) :
    (∑ i, scaledNaturalCubeAnchor delta anchor i) < 1 - eta / 2 := by
  obtain ⟨x, hxCube, hxRegion⟩ :=
    (mem_typeIIRelevantCubeAnchors.mp hanchor).2
  have hxSource := hregion hxRegion
  have hsumlt : (∑ i, scaledNaturalCubeAnchor delta anchor i) < ∑ i, x i := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hxCube i).1.le
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _, (hxCube ⟨0, hk⟩).1⟩
  have hlast : eta <= 1 - ∑ i, x i := by
    simpa [typeIIProjectedRegion] using hxSource.1 (Fin.last k)
  linarith

/-- Interior containment forces the strict coordinate gaps. -/
theorem typeIIInteriorCubeAnchor_separated
    {k : Nat} {eta delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (hdelta : 0 < delta)
    (hregion : IsTypeIISourceRegion eta region)
    {anchor : Fin k -> Nat}
    (hanchor : anchor ∈ typeIIInteriorCubeAnchors delta region) :
    typeIIInteriorCellSeparated
      (scaledNaturalCubeAnchor delta anchor) delta := by
  let a : Fin k -> Real := scaledNaturalCubeAnchor delta anchor
  have hsubset := (mem_typeIIInteriorCubeAnchors.mp hanchor).2
  constructor
  · intro i j hij
    let x : Fin k -> Real := fun h =>
      if h = i then a i + 2 * delta
      else if h = j then a j + delta / 2
      else a h + delta
    have hxCube : x ∈ typeIIDoubledProjectedCube delta anchor := by
      intro h
      by_cases hi : h = i
      · subst h
        simp only [x, if_pos]
        constructor <;> linarith
      · by_cases hj : h = j
        · subst h
          simp only [x, hi, if_false, if_pos]
          constructor <;> linarith
        · simp only [x, hi, hj, if_false]
          constructor <;> linarith
    have hxSource := hregion (hsubset hxCube)
    have hmono : completeProjectedLogTuple x i.castSucc <=
        completeProjectedLogTuple x j.castSucc :=
      hxSource.2.1 (Fin.castSucc_le_castSucc_iff.mpr hij.le)
    have hne : j ≠ i := Ne.symm (Fin.ne_of_lt hij)
    simp only [completeProjectedLogTuple, Fin.snoc_castSucc, x,
      if_pos, hne, if_false] at hmono
    linarith
  · intro i
    let x : Fin k -> Real :=
      Function.update (fun h => a h + delta) i (a i + 2 * delta)
    have hxCube : x ∈ typeIIDoubledProjectedCube delta anchor := by
      intro h
      by_cases hi : h = i
      · subst h
        simp only [x, Function.update_self]
        constructor <;> linarith
      · simp [x, hi]
        constructor <;> linarith
    have hxSource := hregion (hsubset hxCube)
    have hmono : completeProjectedLogTuple x i.castSucc <=
        completeProjectedLogTuple x (Fin.last k) :=
      hxSource.2.1 i.castSucc_lt_last.le
    have hsumx : (∑ h, x h) =
        (∑ h, a h) + ((k + 1 : Nat) : Real) * delta := by
      let f : Fin k -> Real := fun h => a h + delta
      have hupdate : Function.update f i (f i) = f := by
        funext h
        by_cases hi : h = i <;> simp [hi]
      have hbase : (∑ h, f h) =
          f i + ∑ h ∈ (Finset.univ : Finset (Fin k)) \ {i}, f h := by
        have hsum := Finset.sum_update_of_mem
          (Finset.mem_univ i) f (f i)
        rw [hupdate] at hsum
        exact hsum
      calc
        (∑ h, x h) =
            (a i + 2 * delta) +
              ∑ h ∈ (Finset.univ : Finset (Fin k)) \ {i}, f h := by
          simpa only [x, f] using
            (Finset.sum_update_of_mem (Finset.mem_univ i) f
              (a i + 2 * delta))
        _ = (∑ h, f h) + delta := by rw [hbase]; ring
        _ = (∑ h, a h) + (k : Real) * delta + delta := by
          simp only [f, Finset.sum_add_distrib, Fin.sum_const, nsmul_eq_mul]
        _ = (∑ h, a h) + ((k + 1 : Nat) : Real) * delta := by
          push_cast
          ring
    simp only [completeProjectedLogTuple, Fin.snoc_castSucc,
      Fin.snoc_last, x, Function.update_self, hsumx] at hmono
    linarith

/-- Restrict a full-coordinate subset to the projected coordinates. -/
def typeIIPrefixIndexSet {k : Nat} (I : Finset (Fin (k + 1))) :
    Finset (Fin k) :=
  Finset.univ.filter fun i => i.castSucc ∈ I

/-- If the last coordinate is absent, a subset sum of a canonical completion
is exactly its restricted prefix sum. -/
theorem sum_completeProjectedLogTuple_subset_eq_prefix
    {k : Nat} (x : Fin k -> Real) (I : Finset (Fin (k + 1)))
    (hlast : Fin.last k ∉ I) :
    (∑ i ∈ I, completeProjectedLogTuple x i) =
      ∑ i ∈ typeIIPrefixIndexSet I, x i := by
  classical
  calc
    (∑ i ∈ I, completeProjectedLogTuple x i) =
        ∑ i, if i ∈ I then completeProjectedLogTuple x i else 0 := by simp
    _ = (∑ i : Fin k,
          if i.castSucc ∈ I then completeProjectedLogTuple x i.castSucc else 0) +
        (if Fin.last k ∈ I then
          completeProjectedLogTuple x (Fin.last k) else 0) := by
      rw [Fin.sum_univ_castSucc]
    _ = ∑ i ∈ typeIIPrefixIndexSet I, x i := by
      simp only [completeProjectedLogTuple, Fin.snoc_castSucc, hlast,
        if_false, add_zero]
      rw [typeIIPrefixIndexSet, Finset.sum_filter]

/-- A point of a doubled cube differs from its anchor by at most two widths
on every projected subset sum. -/
theorem typeIIDoubledProjectedCube_subsetSum_bounds
    {k : Nat} {delta : Real} {anchor : Fin k -> Nat} {x : Fin k -> Real}
    (hdelta : 0 <= delta)
    (hx : x ∈ typeIIDoubledProjectedCube delta anchor)
    (J : Finset (Fin k)) :
    (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) <=
        ∑ i ∈ J, x i ∧
      (∑ i ∈ J, x i) <=
        (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) +
          2 * (k : Real) * delta := by
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact (hx i).1.le
  · have hcardNat : J.card <= k := by
      simpa using Finset.card_le_univ J
    have hcard : (J.card : Real) <= k := by exact_mod_cast hcardNat
    calc
      (∑ i ∈ J, x i) <=
          ∑ i ∈ J,
            (scaledNaturalCubeAnchor delta anchor i + 2 * delta) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hx i).2
      _ = (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) +
          (J.card : Real) * (2 * delta) := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ <= (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) +
          (k : Real) * (2 * delta) := by
        have htwoDelta : 0 <= 2 * delta := by positivity
        have hmul := mul_le_mul_of_nonneg_right hcard htwoDelta
        linarith
      _ = (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) +
          2 * (k : Real) * delta := by ring

/--
The fixed source subset gives one two projected convenience intervals on every relevant
anchor.
-/
theorem typeIIRelevantCubeAnchor_convenient
    {k : Nat} {epsilon delta : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (herror : 2 * (k : Real) * delta <= epsilon / 2)
    (hconvenient : IsTypeIIRegionConvenient epsilon region)
    {anchor : Fin k -> Nat}
    (hanchor : anchor ∈ typeIIRelevantCubeAnchors delta region) :
    ∃ J : Finset (Fin k),
      (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) ∈
            Set.Icc (9 / 25 + epsilon / 2) (17 / 40 - epsilon / 2) ∨
        (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) ∈
            Set.Icc (23 / 40 + epsilon / 2) (16 / 25 - epsilon / 2) := by
  obtain ⟨x, hxCube, hxRegion⟩ :=
    (mem_typeIIRelevantCubeAnchors.mp hanchor).2
  obtain ⟨I, hI⟩ := hconvenient
  have hISource := hI (completeProjectedLogTuple x) hxRegion
  have hbounds (J : Finset (Fin k)) :
      (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) <=
          ∑ i ∈ J, x i ∧
        (∑ i ∈ J, x i) <=
          (∑ i ∈ J, scaledNaturalCubeAnchor delta anchor i) + epsilon / 2 := by
    have h := typeIIDoubledProjectedCube_subsetSum_bounds hdelta.le hxCube J
    refine ⟨h.1, h.2.trans ?_⟩
    linarith
  by_cases hlast : Fin.last k ∈ I
  · let Icompl : Finset (Fin (k + 1)) := Finset.univ \ I
    let J : Finset (Fin k) := typeIIPrefixIndexSet Icompl
    have hlastCompl : Fin.last k ∉ Icompl := by simp [Icompl, hlast]
    have hprefix : (∑ i ∈ J, x i) =
        1 - ∑ i ∈ I, completeProjectedLogTuple x i := by
      have hbridge := sum_completeProjectedLogTuple_subset_eq_prefix
        x Icompl hlastCompl
      have hsubset : I ⊆ (Finset.univ : Finset (Fin (k + 1))) :=
        Finset.subset_univ I
      have hcompl :
          (∑ i ∈ Icompl, completeProjectedLogTuple x i) =
            1 - ∑ i ∈ I, completeProjectedLogTuple x i := by
        rw [show Icompl = Finset.univ \ I by rfl,
          Finset.sum_sdiff_eq_sub hsubset]
        simp
      exact hbridge.symm.trans hcompl
    refine ⟨J, Or.inr ⟨?_, ?_⟩⟩
    · have hupper := (hbounds J).2
      rw [hprefix] at hupper
      linarith [hISource.2]
    · have hlower := (hbounds J).1
      rw [hprefix] at hlower
      linarith [hISource.1, hepsilon.le]
  · let J : Finset (Fin k) := typeIIPrefixIndexSet I
    have hprefix : (∑ i ∈ J, x i) =
        ∑ i ∈ I, completeProjectedLogTuple x i := by
      exact (sum_completeProjectedLogTuple_subset_eq_prefix x I hlast).symm
    refine ⟨J, Or.inl ⟨?_, ?_⟩⟩
    · have hupper := (hbounds J).2
      rw [hprefix] at hupper
      linarith [hISource.1]
    · have hlower := (hbounds J).1
      rw [hprefix] at hlower
      linarith [hISource.2, hepsilon.le]

end

end PrimesRestrictedDigits
