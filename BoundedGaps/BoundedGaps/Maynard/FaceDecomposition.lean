import BoundedGaps.Maynard.SimplexCompositionMoments
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Fin.SuccAboveOrderIso

/-!
# Omitted-coordinate face decomposition

The retained coordinates on a Maynard face are reindexed by `Fin n` through
`Fin.succAbove`. The induced equivalences preserve product Lebesgue volume,
transport the cube and simplex exactly, and reduce every quadratic face moment
in dimension 104 to the checked `smallKG104` simplex moment.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

def faceIndexEquiv {n : ℕ} (m : Fin (n + 1)) :
    Fin n ≃ maynardFaceIndex (n + 1) m :=
  Equiv.ofBijective
    (fun i : Fin n =>
      (⟨m.succAbove i, Fin.succAbove_ne m i⟩ :
        maynardFaceIndex (n + 1) m)) (by
    constructor
    · intro i j h
      apply Fin.succAbove_right_injective
      exact congrArg Subtype.val h
    · intro j
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq j.2
      exact ⟨i, Subtype.ext hi⟩)

theorem faceIndexEquiv_apply {n : ℕ} (m : Fin (n + 1)) (i : Fin n) :
    faceIndexEquiv m i = ⟨m.succAbove i, Fin.succAbove_ne m i⟩ := rfl

/-- Split one coordinate from a finite real product. -/
def faceCoordinateEquiv {n : ℕ} (m : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃ᵐ
      (ℝ × (maynardFaceIndex (n + 1) m → ℝ)) := by
  let p : Fin (n + 1) → Prop := fun i => i = m
  letI : Fintype {i : Fin (n + 1) // p i} := Subtype.fintype p
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (n + 1) => ℝ) p
  let e1 := MeasurableEquiv.piUnique
    (fun _ : {i : Fin (n + 1) // p i} => ℝ)
  let e2 := MeasurableEquiv.piCongrLeft
    (fun _ : {i : Fin (n + 1) // ¬p i} => ℝ) (Equiv.refl _)
  let ec : (Fin (n + 1) → ℝ) ≃ᵐ
      (ℝ × ({i : Fin (n + 1) // ¬p i} → ℝ)) :=
    e.trans (MeasurableEquiv.prodCongr e1 e2)
  let er : ({i : Fin (n + 1) // ¬p i} → ℝ) ≃ᵐ
      (maynardFaceIndex (n + 1) m → ℝ) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : maynardFaceIndex (n + 1) m => ℝ) (Equiv.refl _)
  exact ec.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) er)

theorem faceCoordinateEquiv_apply {n : ℕ} (m : Fin (n + 1))
    (u : Fin (n + 1) → ℝ) :
    faceCoordinateEquiv m u =
      (u m, fun j : maynardFaceIndex (n + 1) m => u j.1) := by
  change (u m, fun j : maynardFaceIndex (n + 1) m => u j.1) = _
  rfl

theorem faceCoordinateEquiv_symm_apply {n : ℕ} (m : Fin (n + 1))
    (x : ℝ) (t : maynardFaceIndex (n + 1) m → ℝ) :
    (faceCoordinateEquiv m).symm (x, t) =
      maynardInsertCoordinate m x t := by
  apply (faceCoordinateEquiv m).injective
  rw [(faceCoordinateEquiv m).apply_symm_apply]
  rw [faceCoordinateEquiv_apply]
  apply Prod.ext
  · simp [maynardInsertCoordinate]
  · funext j
    simp [maynardInsertCoordinate, j.2]

theorem faceCoordinateEquiv_measurePreserving {n : ℕ} (m : Fin (n + 1)) :
    MeasurePreserving (faceCoordinateEquiv m) volume volume := by
  let p : Fin (n + 1) → Prop := fun i => i = m
  letI : Fintype {i : Fin (n + 1) // p i} := Subtype.fintype p
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (n + 1) => ℝ) p
  let e1 := MeasurableEquiv.piUnique
    (fun _ : {i : Fin (n + 1) // p i} => ℝ)
  let e2 := MeasurableEquiv.piCongrLeft
    (fun _ : {i : Fin (n + 1) // ¬p i} => ℝ) (Equiv.refl _)
  let er := MeasurableEquiv.piCongrLeft
    (fun _ : maynardFaceIndex (n + 1) m => ℝ) (Equiv.refl _)
  have h1 : MeasurePreserving e1 volume volume :=
    volume_preserving_piUnique _
  have h2 : MeasurePreserving e2 volume volume :=
    volume_measurePreserving_piCongrLeft _ _
  have h3 : MeasurePreserving er volume volume :=
    volume_measurePreserving_piCongrLeft _ _
  have heprod : MeasurePreserving (MeasurableEquiv.prodCongr e1 e2)
      (volume.prod volume) (volume.prod volume) := h1.prod h2
  have he : MeasurePreserving e volume (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact volume_preserving_piEquivPiSubtypeProd
      (fun _ : Fin (n + 1) => ℝ) p
  have hc : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) er)
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod h3
  have hcomp := hc.comp (heprod.comp he)
  refine ⟨(faceCoordinateEquiv m).measurable, ?_⟩
  rw [Measure.volume_eq_prod]
  have hfun : (faceCoordinateEquiv m : (Fin (n + 1) → ℝ) →
      ℝ × (maynardFaceIndex (n + 1) m → ℝ)) =
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) er : _ → _) ∘
        (MeasurableEquiv.prodCongr e1 e2 : _ → _) ∘ (e : _ → _)) := by
    rfl
  rw [hfun]
  exact hcomp.map_eq

theorem faceCoordinateEquiv_mem_cube_iff {n : ℕ} (m : Fin (n + 1))
    (u : Fin (n + 1) → ℝ) :
    faceCoordinateEquiv m u ∈
        Set.Icc (0 : ℝ) 1 ×ˢ maynardCubeOf (maynardFaceIndex (n + 1) m) ↔
      u ∈ maynardCube (n + 1) := by
  rw [faceCoordinateEquiv_apply]
  unfold maynardCube maynardCubeOf
  constructor
  · rintro ⟨hx, ht⟩ i hi
    by_cases him : i = m
    · subst i
      exact hx
    · let j : maynardFaceIndex (n + 1) m := ⟨i, him⟩
      simpa using ht j (by simp)
  · intro hu
    refine ⟨hu m (by simp), ?_⟩
    intro j hj
    simpa using hu j.1 (by simp)

theorem faceCoordinateEquiv_symm_preimage_cube {n : ℕ}
    (m : Fin (n + 1)) :
    (faceCoordinateEquiv m).symm ⁻¹' maynardCube (n + 1) =
      Set.Icc (0 : ℝ) 1 ×ˢ
        maynardCubeOf (maynardFaceIndex (n + 1) m) := by
  ext z
  have h := faceCoordinateEquiv_mem_cube_iff m
    ((faceCoordinateEquiv m).symm z)
  simpa using h.symm

/-- Reindex retained face coordinates increasingly by `Fin n`. -/
def faceReindexEquiv {n : ℕ} (m : Fin (n + 1)) :
    (Fin n → ℝ) ≃ᵐ (maynardFaceIndex (n + 1) m → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : maynardFaceIndex (n + 1) m => ℝ) (faceIndexEquiv m)

theorem faceReindexEquiv_measurePreserving {n : ℕ} (m : Fin (n + 1)) :
    MeasurePreserving (faceReindexEquiv m) volume volume :=
  volume_measurePreserving_piCongrLeft _ _

@[simp] theorem faceReindexEquiv_apply {n : ℕ} (m : Fin (n + 1))
    (u : Fin n → ℝ) (i : Fin n) :
    faceReindexEquiv m u (faceIndexEquiv m i) = u i := by
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : maynardFaceIndex (n + 1) m => ℝ)
    (faceIndexEquiv m) u i

theorem faceReindexEquiv_sum {n : ℕ} (m : Fin (n + 1))
    (u : Fin n → ℝ) :
    (∑ j, faceReindexEquiv m u j) = ∑ i, u i := by
  rw [← (faceIndexEquiv m).sum_comp (faceReindexEquiv m u)]
  simp

theorem faceReindexEquiv_sq_sum {n : ℕ} (m : Fin (n + 1))
    (u : Fin n → ℝ) :
    (∑ j, (faceReindexEquiv m u j) ^ 2) = ∑ i, (u i) ^ 2 := by
  rw [← (faceIndexEquiv m).sum_comp
    (fun j => (faceReindexEquiv m u j) ^ 2)]
  simp

theorem sum_insertCoordinate {n : ℕ} (m : Fin (n + 1)) (x : ℝ)
    (t : maynardFaceIndex (n + 1) m → ℝ) :
    (∑ i, maynardInsertCoordinate m x t i) = x + ∑ j, t j := by
  rw [Fin.sum_univ_succAbove]
  rw [maynardInsertCoordinate_at]
  rw [← (faceIndexEquiv m).sum_comp t]
  apply congrArg (fun z => x + z)
  apply Finset.sum_congr rfl
  intro i hi
  rw [maynardInsertCoordinate_off]
  apply congrArg t
  apply Subtype.ext
  rfl

theorem sq_sum_insertCoordinate {n : ℕ} (m : Fin (n + 1)) (x : ℝ)
    (t : maynardFaceIndex (n + 1) m → ℝ) :
    (∑ i, (maynardInsertCoordinate m x t i) ^ 2) =
      x ^ 2 + ∑ j, (t j) ^ 2 := by
  rw [Fin.sum_univ_succAbove]
  rw [maynardInsertCoordinate_at]
  rw [← (faceIndexEquiv m).sum_comp
    (fun j => (t j) ^ 2)]
  apply congrArg (fun z => x ^ 2 + z)
  apply Finset.sum_congr rfl
  intro i hi
  rw [maynardInsertCoordinate_off]
  apply congrArg (fun z => z ^ 2)
  apply congrArg t
  apply Subtype.ext
  rfl

def maynardFaceSimplex {n : ℕ} (m : Fin (n + 1)) :
    Set (maynardFaceIndex (n + 1) m → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1}

theorem maynardFaceSimplex_measurable {n : ℕ} (m : Fin (n + 1)) :
    MeasurableSet (maynardFaceSimplex m) := by
  unfold maynardFaceSimplex
  measurability

theorem faceSimplex_subset_cube {n : ℕ} (m : Fin (n + 1)) :
    maynardFaceSimplex m ⊆
      maynardCubeOf (maynardFaceIndex (n + 1) m) := by
  intro t ht j hj
  refine ⟨ht.1 j, ?_⟩
  exact (Finset.single_le_sum (fun l hl => ht.1 l) (by simp)).trans ht.2

theorem face_mem_of_insert_mem_simplex {n : ℕ} (m : Fin (n + 1))
    (x : ℝ) (t : maynardFaceIndex (n + 1) m → ℝ)
    (h : maynardInsertCoordinate m x t ∈ maynardSimplex (n + 1)) :
    t ∈ maynardFaceSimplex m := by
  refine ⟨?_, ?_⟩
  · intro j
    have hj := (h.1 j.1 (by simp)).1
    simpa [maynardInsertCoordinate, j.2] using hj
  · have hx0 := (h.1 m (by simp)).1
    have hx0' : 0 ≤ x := by
      simpa [maynardInsertCoordinate] using hx0
    have hsum := h.2
    rw [sum_insertCoordinate] at hsum
    exact (show ∑ j, t j ≤ 1 by linarith)

theorem insert_mem_simplex_iff {n : ℕ} (m : Fin (n + 1))
    (x : ℝ) (t : maynardFaceIndex (n + 1) m → ℝ)
    (ht : t ∈ maynardFaceSimplex m) :
    maynardInsertCoordinate m x t ∈ maynardSimplex (n + 1) ↔
      x ∈ Set.Icc (0 : ℝ) (1 - ∑ j, t j) := by
  rcases ht with ⟨htnonneg, htsum⟩
  rw [maynardSimplex]
  constructor
  · rintro ⟨hcube, hsum⟩
    have hx0 : 0 ≤ x := by
      simpa [maynardInsertCoordinate] using (hcube m (by simp)).1
    have hxsum : x + ∑ j, t j ≤ 1 := by
      rw [← sum_insertCoordinate]
      exact hsum
    exact ⟨hx0, by linarith⟩
  · rintro ⟨hx0, hxsum⟩
    have hsum : x + ∑ j, t j ≤ 1 := by linarith
    have hsum_nonneg : 0 ≤ ∑ j, t j :=
      Finset.sum_nonneg (fun j hj => htnonneg j)
    have hface_le_one : ∀ j : maynardFaceIndex (n + 1) m, t j ≤ 1 := by
      intro j
      have hsingle : t j ≤ ∑ l, t l :=
        Finset.single_le_sum (fun l hl => htnonneg l) (by simp)
      linarith
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst i
        have hxle1 : x ≤ 1 := by linarith
        simpa [maynardInsertCoordinate] using And.intro hx0 hxle1
      · let j : maynardFaceIndex (n + 1) m := ⟨i, him⟩
        simpa [maynardInsertCoordinate, him] using And.intro (htnonneg j)
          (hface_le_one j)
    · rw [sum_insertCoordinate]
      exact hsum

theorem faceReindexEquiv_mem_faceSimplex_iff {n : ℕ}
    (m : Fin (n + 1)) (u : Fin n → ℝ) :
    faceReindexEquiv m u ∈ maynardFaceSimplex m ↔
      u ∈ maynardSimplex n := by
  rw [maynardSimplex_eq_radius]
  unfold maynardFaceSimplex maynardSimplexRadius
  simp only [Set.mem_setOf_eq, faceReindexEquiv_sum]
  constructor
  · rintro ⟨hu, hsum⟩
    exact ⟨fun i => by
      simpa using hu (faceIndexEquiv m i), hsum⟩
  · rintro ⟨hu, hsum⟩
    refine ⟨?_, hsum⟩
    intro j
    obtain ⟨i, rfl⟩ := (faceIndexEquiv m).surjective j
    simpa using hu i

theorem faceReindexEquiv_preimage_faceSimplex {n : ℕ}
    (m : Fin (n + 1)) :
    faceReindexEquiv m ⁻¹' maynardFaceSimplex m = maynardSimplex n := by
  ext u
  exact faceReindexEquiv_mem_faceSimplex_iff m u

theorem faceReindexEquiv_mem_cube_iff {n : ℕ} (m : Fin (n + 1))
    (u : Fin n → ℝ) :
    faceReindexEquiv m u ∈ maynardCubeOf (maynardFaceIndex (n + 1) m) ↔
      u ∈ maynardCube n := by
  unfold maynardCube maynardCubeOf
  constructor
  · intro hu i hi
    simpa using hu (faceIndexEquiv m i) (by simp)
  · intro hu j hj
    obtain ⟨i, rfl⟩ := (faceIndexEquiv m).surjective j
    simpa using hu i (by simp)

theorem faceReindexEquiv_preimage_cube {n : ℕ} (m : Fin (n + 1)) :
    faceReindexEquiv m ⁻¹'
        maynardCubeOf (maynardFaceIndex (n + 1) m) = maynardCube n := by
  ext u
  exact faceReindexEquiv_mem_cube_iff m u

theorem face_setIntegral_reindex {n : ℕ} (m : Fin (n + 1))
    (f : (maynardFaceIndex (n + 1) m → ℝ) → ℝ) :
    (∫ t in maynardFaceSimplex m, f t) =
      ∫ u in maynardSimplex n, f (faceReindexEquiv m u) := by
  let e := faceReindexEquiv m
  have he := faceReindexEquiv_measurePreserving m
  calc
    (∫ t in maynardFaceSimplex m, f t) =
        ∫ t, (maynardFaceSimplex m).indicator f t := by
      rw [integral_indicator (maynardFaceSimplex_measurable m)]
    _ = ∫ u, (maynardFaceSimplex m).indicator f (e u) := by
      exact (he.integral_comp' ((maynardFaceSimplex m).indicator f)).symm
    _ = ∫ u, (maynardSimplex n).indicator (fun u => f (e u)) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ maynardSimplex n
      · simp [Set.indicator, hu,
          (faceReindexEquiv_mem_faceSimplex_iff m u).2 hu, e]
      · simp [Set.indicator, hu,
          (faceReindexEquiv_mem_faceSimplex_iff m u).not.mpr hu, e]
    _ = ∫ u in maynardSimplex n, f (e u) := by
      rw [integral_indicator (maynardSimplex_measurable (k := n))]

theorem faceCube_setIntegral_reindex {n : ℕ} (m : Fin (n + 1))
    (f : (maynardFaceIndex (n + 1) m → ℝ) → ℝ) :
    (∫ t in maynardCubeOf (maynardFaceIndex (n + 1) m), f t) =
      ∫ u in maynardCube n, f (faceReindexEquiv m u) := by
  let e := faceReindexEquiv m
  have he := faceReindexEquiv_measurePreserving m
  calc
    (∫ t in maynardCubeOf (maynardFaceIndex (n + 1) m), f t) =
        ∫ t, (maynardCubeOf
          (maynardFaceIndex (n + 1) m)).indicator f t := by
      exact (integral_indicator (MeasurableSet.pi Set.countable_univ
        (fun _ _ => measurableSet_Icc))).symm
    _ = ∫ u, (maynardCubeOf
        (maynardFaceIndex (n + 1) m)).indicator f (e u) := by
      exact (he.integral_comp'
        ((maynardCubeOf (maynardFaceIndex (n + 1) m)).indicator f)).symm
    _ = ∫ u, (maynardCube n).indicator (fun u => f (e u)) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ maynardCube n
      · simp [Set.indicator, hu,
          (faceReindexEquiv_mem_cube_iff m u).2 hu, e]
      · simp [Set.indicator, hu,
          (faceReindexEquiv_mem_cube_iff m u).not.mpr hu, e]
    _ = ∫ u in maynardCube n, f (e u) := by
      rw [integral_indicator (maynardCube_measurable n)]

theorem betaNatIntegral_scaled (a b : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x in Set.Icc (0 : ℝ) r, x ^ a * (r - x) ^ b) =
      r ^ (a + b + 1) *
        ((a.factorial : ℝ) * b.factorial / (a + b + 1).factorial) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hr.le]
  let f : ℝ → ℝ := fun x => x ^ a * (r - x) ^ b
  have hcomp := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) f hr.ne'
  have hbeta := betaNatIntegral a b
  have hpoint : (fun x => f (r * x)) =
      (fun x => r ^ (a + b) * (x ^ a * (1 - x) ^ b)) := by
    funext x
    dsimp [f]
    rw [show r - r * x = r * (1 - x) by ring]
    rw [mul_pow, mul_pow]
    ring
  rw [hpoint, intervalIntegral.integral_const_mul, hbeta] at hcomp
  simp only [smul_eq_mul] at hcomp
  norm_num at hcomp
  field_simp [hr.ne'] at hcomp ⊢
  calc
    _ = (a + (b + 1)).factorial * ∫ x in (0 : ℝ)..r, f x := by
      rfl
    _ = r ^ (a + b) * (a.factorial : ℝ) * b.factorial * r := hcomp.symm
    _ = r ^ (a + b) * ((a.factorial : ℝ) * (b.factorial * r)) := by ring
    _ = _ := by
      rw [pow_succ]
      ring

def faceQuadraticIntegrand {n : ℕ} (m : Fin (n + 1)) (b c : ℕ)
    (t : maynardFaceIndex (n + 1) m → ℝ) : ℝ :=
  (1 - ∑ i, t i) ^ b * (∑ i, (t i) ^ 2) ^ c

theorem faceQuadraticIntegrand_reindex {n : ℕ} (m : Fin (n + 1))
    (b c : ℕ) (u : Fin n → ℝ) :
    faceQuadraticIntegrand m b c (faceReindexEquiv m u) =
      simplexQuadraticIntegrand n b c u := by
  simp [faceQuadraticIntegrand, simplexQuadraticIntegrand,
    faceReindexEquiv_sum, faceReindexEquiv_sq_sum]

theorem faceQuadratic_integrableOn (m : Fin 105) (b c : ℕ) :
    IntegrableOn (faceQuadraticIntegrand m b c) (maynardFaceSimplex m) := by
  let e := faceReindexEquiv m
  have he := faceReindexEquiv_measurePreserving m
  have hcomp : IntegrableOn (faceQuadraticIntegrand m b c ∘ e)
      (e ⁻¹' maynardFaceSimplex m) := by
    rw [faceReindexEquiv_preimage_faceSimplex]
    have heq : faceQuadraticIntegrand m b c ∘ e =
        simplexQuadraticIntegrand 104 b c := by
      funext u
      exact faceQuadraticIntegrand_reindex m b c u
    rw [heq]
    exact simplexQuadratic_integrableOn 104 b c
  exact (he.integrableOn_comp_preimage e.measurableEmbedding).mp hcomp

theorem faceQuadratic_moment_104_smallKG (m : Fin 105) (b : ℕ)
    (c : Fin 11) :
    (∫ t in maynardFaceSimplex m,
      faceQuadraticIntegrand m b c.1 t) =
      ((Nat.factorial b : ℚ) /
        Nat.factorial (104 + b + 2 * c.1) * smallKG104 c.1 : ℝ) := by
  rw [face_setIntegral_reindex]
  simp_rw [faceQuadraticIntegrand_reindex]
  exact simplexQuadratic_moment_104_smallKG b c

end
end BoundedGaps.Maynard
