import BoundedGaps.Maynard.SmallKCertificate
import BoundedGaps.Maynard.SmallKNumeratorGeneratedEvaluation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity

/-!
# Maynard's variational functionals

This module fixes the measure-theoretic presentation of the functionals in
Maynard2013v3, Proposition `MainProp`.  The source uses Riemann-integrable
functions on the unit cube supported on the simplex.  We use Bochner set
integrals, with the integrability requirements kept explicit in
`MaynardAdmissible`; no analytic integral identity is hidden in a definition.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

variable {k : ℕ}

/-- The product unit cube for an arbitrary finite coordinate type. -/
def maynardCubeOf (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)

/-- The unit cube indexed by `Fin k`. -/
def maynardCube (k : ℕ) : Set (Fin k → ℝ) := maynardCubeOf (Fin k)

/-- Maynard's simplex inside the unit cube. -/
def maynardSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {t | t ∈ maynardCube k ∧ ∑ i, t i ≤ 1}

/-- The coordinates retained on the face obtained by omitting `m`. -/
def maynardFaceIndex (k : ℕ) (m : Fin k) := {i : Fin k // i ≠ m}

instance maynardFaceIndex.fintype (k : ℕ) (m : Fin k) :
    Fintype (maynardFaceIndex k m) :=
  by
    classical
    exact Fintype.subtype (Finset.univ.filter (fun i => i ≠ m)) (by simp)

/-- Reinsert a value at the omitted coordinate. -/
def maynardInsertCoordinate (m : Fin k) (x : ℝ)
    (t : maynardFaceIndex k m → ℝ) : Fin k → ℝ :=
  fun i => if h : i = m then x else t ⟨i, h⟩

theorem maynardInsertCoordinate_at (m : Fin k) (x : ℝ)
    (t : maynardFaceIndex k m → ℝ) :
    maynardInsertCoordinate m x t m = x := by
  simp [maynardInsertCoordinate]

theorem maynardInsertCoordinate_off (m : Fin k) (x : ℝ)
    (t : maynardFaceIndex k m → ℝ) (i : Fin k) (h : i ≠ m) :
    maynardInsertCoordinate m x t i = t ⟨i, h⟩ := by
  simp [maynardInsertCoordinate, h]

/-- The denominator functional `I_k(F)`. -/
def maynardI (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t in maynardCube k, F t ^ 2

/-- The face functional `J_k^(m)(F)`. -/
def maynardJ (k : ℕ) (m : Fin k) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t in maynardCubeOf (maynardFaceIndex k m),
    (∫ x in Set.Icc (0 : ℝ) 1,
      F (maynardInsertCoordinate m x t)) ^ 2

theorem maynardI_nonneg (F : (Fin k → ℝ) → ℝ) :
    0 ≤ maynardI k F := by
  unfold maynardI
  exact setIntegral_nonneg
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
    (fun t _ => sq_nonneg (F t))

theorem maynardJ_nonneg (m : Fin k) (F : (Fin k → ℝ) → ℝ) :
    0 ≤ maynardJ k m F := by
  unfold maynardJ
  exact setIntegral_nonneg
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
    (fun t _ => sq_nonneg _)

/-- Pointwise support on Maynard's simplex. -/
def MaynardSimplexSupported (k : ℕ) (F : (Fin k → ℝ) → ℝ) : Prop :=
  ∀ t, t ∉ maynardSimplex k → F t = 0

/-- The Bochner hypotheses needed by the displayed functionals. -/
def MaynardAdmissible (k : ℕ) (F : (Fin k → ℝ) → ℝ) : Prop :=
  MaynardSimplexSupported k F ∧
    IntegrableOn (fun t => F t ^ 2) (maynardCube k) ∧
    (∀ m : Fin k, ∀ t : maynardFaceIndex k m → ℝ,
      IntegrableOn (fun x => F (maynardInsertCoordinate m x t)) (Set.Icc 0 1)) ∧
    (∀ m : Fin k,
      IntegrableOn
        (fun t => (∫ x in Set.Icc (0 : ℝ) 1,
          F (maynardInsertCoordinate m x t)) ^ 2)
        (maynardCubeOf (maynardFaceIndex k m)))

/-- The quotient appearing in the variational problem. -/
def maynardRatio (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  (∑ m : Fin k, maynardJ k m F) / maynardI k F

/-- The set of quotients of admissible functions with positive denominator. -/
def maynardRatioSet (k : ℕ) : Set ℝ :=
  {r | ∃ F : (Fin k → ℝ) → ℝ,
    MaynardAdmissible k F ∧ 0 < maynardI k F ∧ r = maynardRatio k F}

/-- Maynard's supremum, with the real supremum understood under the usual
boundedness side condition needed by `csSup`. -/
noncomputable def maynardM (k : ℕ) : ℝ := sSup (maynardRatioSet k)

theorem maynard_ratio_mem_set {F : (Fin k → ℝ) → ℝ}
    (hF : MaynardAdmissible k F) (hI : 0 < maynardI k F) :
    maynardRatio k F ∈ maynardRatioSet k := by
  exact ⟨F, hF, hI, rfl⟩

theorem maynard_ratio_le_M {F : (Fin k → ℝ) → ℝ}
    (hF : MaynardAdmissible k F) (hI : 0 < maynardI k F)
    (hbound : BddAbove (maynardRatioSet k)) :
    maynardRatio k F ≤ maynardM k := by
  exact le_csSup hbound (maynard_ratio_mem_set hF hI)

/-! The exact polynomial candidate used by the `k = 105` certificate. -/

def smallKRealCoefficient (i : Fin 42) : ℝ := smallKCoefficient i

def smallKRealP1 (t : Fin 105 → ℝ) : ℝ := ∑ i, t i

def smallKRealP2 (t : Fin 105 → ℝ) : ℝ := ∑ i, (t i) ^ 2

def smallKRealPolynomial (t : Fin 105 → ℝ) : ℝ :=
  ∑ i : Fin 42,
    smallKRealCoefficient i *
      (1 - smallKRealP1 t) ^ smallKExponentB i *
      (smallKRealP2 t) ^ smallKExponentC i

/-- The source's zero extension outside the simplex. -/
noncomputable def smallKCandidate (t : Fin 105 → ℝ) : ℝ := by
  classical
  exact if t ∈ maynardSimplex 105 then smallKRealPolynomial t else 0

theorem smallKCandidate_simplexSupported :
    MaynardSimplexSupported 105 smallKCandidate := by
  classical
  intro t ht
  simp [smallKCandidate, ht]

theorem maynardCube_measurable (k : ℕ) :
    MeasurableSet (maynardCube k) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i hi
  exact measurableSet_Icc

theorem maynardCubeOf_measure_lt_top (ι : Type*) [Fintype ι] :
    volume (maynardCubeOf ι) < ⊤ := by
  unfold maynardCubeOf
  rw [volume_pi_pi]
  exact ENNReal.prod_lt_top (fun i _ => measure_Icc_lt_top)

theorem maynardCube_measure_lt_top (k : ℕ) :
    volume (maynardCube k) < ⊤ := by
  exact maynardCubeOf_measure_lt_top (Fin k)

theorem maynardSimplex_measurable :
    MeasurableSet (maynardSimplex k) := by
  change MeasurableSet (maynardCube k ∩ {t | ∑ i, t i ≤ 1})
  exact (maynardCube_measurable k).inter (by measurability)

theorem measurable_smallKCandidate : Measurable smallKCandidate := by
  classical
  unfold smallKCandidate
  apply Measurable.ite (maynardSimplex_measurable (k := 105))
  · unfold smallKRealPolynomial smallKRealP1 smallKRealP2
    fun_prop
  · exact measurable_const

def smallKCandidateBound : ℝ :=
  ∑ i : Fin 42,
    ‖smallKRealCoefficient i‖ * (106 : ℝ) ^ smallKExponentB i *
      (105 : ℝ) ^ smallKExponentC i

theorem smallKCandidateBound_nonneg : 0 ≤ smallKCandidateBound := by
  unfold smallKCandidateBound
  positivity

theorem maynard_integrableOn_of_measurable_bounded
    {α : Type*} [MeasureSpace α]
    (s : Set α) (hs : MeasurableSet s) (hsfinite : volume s < ⊤)
    (f : α → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) : IntegrableOn f s := by
  refine IntegrableOn.of_bound hsfinite hf.aestronglyMeasurable.restrict C ?_
  exact (ae_restrict_iff' hs).2 (ae_of_all _ (fun x hx => hC x hx))

theorem smallKRealP1_norm_le (t : Fin 105 → ℝ)
    (ht : t ∈ maynardCube 105) : ‖smallKRealP1 t‖ ≤ 105 := by
  unfold smallKRealP1
  calc
    ‖∑ i, t i‖ ≤ ∑ i, ‖t i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 105, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hti : t i ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [maynardCube, maynardCubeOf] using ht i (by simp)
      simpa [Real.norm_eq_abs] using
        (abs_le.2 ⟨by linarith [hti.1], hti.2⟩)
    _ = 105 := by simp

theorem smallKRealP2_nonneg (t : Fin 105 → ℝ) : 0 ≤ smallKRealP2 t := by
  unfold smallKRealP2
  exact Finset.sum_nonneg fun i _ => sq_nonneg (t i)

theorem smallKRealP2_le (t : Fin 105 → ℝ)
    (ht : t ∈ maynardCube 105) : smallKRealP2 t ≤ 105 := by
  unfold smallKRealP2
  calc
    ∑ i, (t i) ^ 2 ≤ ∑ _ : Fin 105, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi : t i ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [maynardCube, maynardCubeOf] using ht i (by simp)
      nlinarith [mul_nonneg hi.1 (sub_nonneg.mpr hi.2)]
    _ = 105 := by simp

theorem smallKRealPolynomial_norm_le (t : Fin 105 → ℝ)
    (ht : t ∈ maynardCube 105) :
    ‖smallKRealPolynomial t‖ ≤ smallKCandidateBound := by
  unfold smallKRealPolynomial smallKCandidateBound
  calc
    ‖∑ i : Fin 42, smallKRealCoefficient i *
        (1 - smallKRealP1 t) ^ smallKExponentB i *
        (smallKRealP2 t) ^ smallKExponentC i‖ ≤
      ∑ i : Fin 42, ‖smallKRealCoefficient i *
        (1 - smallKRealP1 t) ^ smallKExponentB i *
        (smallKRealP2 t) ^ smallKExponentC i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 42,
        ‖smallKRealCoefficient i‖ * (106 : ℝ) ^ smallKExponentB i *
          (105 : ℝ) ^ smallKExponentC i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have hsub : ‖1 - smallKRealP1 t‖ ≤ (106 : ℝ) := by
        calc
          ‖1 - smallKRealP1 t‖ ≤ ‖(1 : ℝ)‖ + ‖smallKRealP1 t‖ := norm_sub_le _ _
          _ = 1 + ‖smallKRealP1 t‖ := by norm_num
          _ ≤ 106 := by linarith [smallKRealP1_norm_le t ht]
      have hp2 : ‖smallKRealP2 t‖ ≤ (105 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (smallKRealP2_nonneg t)]
        exact smallKRealP2_le t ht
      gcongr

theorem smallKCandidate_norm_le (t : Fin 105 → ℝ) :
    ‖smallKCandidate t‖ ≤ smallKCandidateBound := by
  by_cases ht : t ∈ maynardSimplex 105
  · simpa [smallKCandidate, ht] using smallKRealPolynomial_norm_le t ht.1
  · simp [smallKCandidate, ht, smallKCandidateBound_nonneg]

theorem smallKCandidate_sq_integrableOn :
    IntegrableOn (fun t : Fin 105 → ℝ => smallKCandidate t ^ 2)
      (maynardCube 105) := by
  have hC := smallKCandidateBound_nonneg
  refine maynard_integrableOn_of_measurable_bounded
    (s := maynardCube 105) (hs := maynardCube_measurable 105)
    (hsfinite := maynardCube_measure_lt_top 105)
    (f := fun t : Fin 105 → ℝ => smallKCandidate t ^ 2)
    (measurable_smallKCandidate.pow_const 2) (smallKCandidateBound ^ 2) ?_
  intro t ht
  rw [norm_pow]
  simpa [pow_two] using
    mul_self_le_mul_self (norm_nonneg (smallKCandidate t)) (smallKCandidate_norm_le t)

theorem smallKCandidate_face_integrableOn (m : Fin 105)
    (t : maynardFaceIndex 105 m → ℝ) :
    IntegrableOn (fun x : ℝ => smallKCandidate (maynardInsertCoordinate m x t))
      (Set.Icc 0 1) := by
  have hinsert : Measurable (fun x : ℝ => maynardInsertCoordinate m x t) := by
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i = m
    · simp only [maynardInsertCoordinate, dif_pos hi]
      exact measurable_id
    · simp [maynardInsertCoordinate, hi]
  refine maynard_integrableOn_of_measurable_bounded
    (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
    (hsfinite := measure_Icc_lt_top)
    (f := fun x : ℝ => smallKCandidate (maynardInsertCoordinate m x t))
    (measurable_smallKCandidate.comp hinsert) smallKCandidateBound ?_
  intro x hx
  exact smallKCandidate_norm_le _

def smallKFaceJoint (m : Fin 105) :
    ((maynardFaceIndex 105 m → ℝ) × ℝ) → ℝ := fun z =>
  if z.2 ∈ Set.Icc (0 : ℝ) 1 then
    smallKCandidate (maynardInsertCoordinate m z.2 z.1) else 0

theorem smallKFaceJoint_measurable (m : Fin 105) :
    Measurable (smallKFaceJoint m) := by
  have hinsert : Measurable
      (fun z : (maynardFaceIndex 105 m → ℝ) × ℝ =>
        maynardInsertCoordinate m z.2 z.1) := by
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i = m
    · simp only [maynardInsertCoordinate, dif_pos hi]
      exact measurable_snd
    · let j : maynardFaceIndex 105 m := ⟨i, hi⟩
      simpa [maynardInsertCoordinate, hi, j, Function.comp_def] using
        ((measurable_pi_apply j).comp measurable_fst)
  unfold smallKFaceJoint
  apply Measurable.ite (measurableSet_Icc.preimage measurable_snd)
  · exact measurable_smallKCandidate.comp hinsert
  · exact measurable_const

theorem smallKFaceInner_measurable (m : Fin 105) :
    Measurable (fun t : maynardFaceIndex 105 m → ℝ =>
      ∫ x in Set.Icc (0 : ℝ) 1,
        smallKCandidate (maynardInsertCoordinate m x t)) := by
  have hsm : StronglyMeasurable (fun t : maynardFaceIndex 105 m → ℝ =>
      ∫ x : ℝ, smallKFaceJoint m (t, x)) :=
    (smallKFaceJoint_measurable m).stronglyMeasurable.integral_prod_right'
  have hm : Measurable (fun t : maynardFaceIndex 105 m → ℝ =>
      ∫ x, smallKFaceJoint m (t, x)) := hsm.measurable
  convert hm using 1
  funext t
  simp only [smallKFaceJoint]
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [Set.indicator, hx]

theorem smallKFaceInner_norm_le (m : Fin 105)
    (t : maynardFaceIndex 105 m → ℝ) :
    ‖∫ x in Set.Icc (0 : ℝ) 1,
      smallKCandidate (maynardInsertCoordinate m x t)‖ ≤ smallKCandidateBound := by
  calc
    ‖∫ x in Set.Icc (0 : ℝ) 1,
        smallKCandidate (maynardInsertCoordinate m x t)‖ ≤
      smallKCandidateBound * volume.real (Set.Icc (0 : ℝ) 1) :=
        norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
          (fun x _ => smallKCandidate_norm_le _)
    _ = smallKCandidateBound := by rw [Real.volume_real_Icc_of_le] <;> norm_num

theorem smallKCandidate_face_integrand_integrableOn (m : Fin 105) :
    IntegrableOn
      (fun t : maynardFaceIndex 105 m → ℝ =>
        (∫ x in Set.Icc (0 : ℝ) 1,
          smallKCandidate (maynardInsertCoordinate m x t)) ^ 2)
      (maynardCubeOf (maynardFaceIndex 105 m)) := by
  refine maynard_integrableOn_of_measurable_bounded
    (s := maynardCubeOf (maynardFaceIndex 105 m))
    (hs := MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
    (hsfinite := maynardCubeOf_measure_lt_top _)
    (f := fun t : maynardFaceIndex 105 m → ℝ =>
      (∫ x in Set.Icc (0 : ℝ) 1,
        smallKCandidate (maynardInsertCoordinate m x t)) ^ 2)
    (smallKFaceInner_measurable m |>.pow_const 2)
    (smallKCandidateBound ^ 2) ?_
  intro t ht
  rw [norm_pow]
  simpa [pow_two] using
    mul_self_le_mul_self (norm_nonneg _) (smallKFaceInner_norm_le m t)

theorem smallKCandidate_admissible :
    MaynardAdmissible 105 smallKCandidate := by
  exact ⟨smallKCandidate_simplexSupported, smallKCandidate_sq_integrableOn,
    smallKCandidate_face_integrableOn, smallKCandidate_face_integrand_integrableOn⟩

theorem smallKCandidate_I_pos_of_denominator_identity
    (hI : maynardI 105 smallKCandidate = (smallKDenominator : ℝ)) :
    0 < maynardI 105 smallKCandidate := by
  rw [hI]
  have hq : 0 < smallKDenominator := by
    rw [smallK_denominator_eq_certified]
    exact smallK_certified_denominator_pos
  exact_mod_cast hq

theorem smallK_candidate_ratio_gt_four_of_functionals
    (hI : maynardI 105 smallKCandidate = (smallKDenominator : ℝ))
    (hN : (∑ m : Fin 105, maynardJ 105 m smallKCandidate) =
      (smallKNumerator : ℝ)) :
    (4 : ℝ) < maynardRatio 105 smallKCandidate := by
  have hq : (4 : ℚ) < smallKNumerator / smallKDenominator := by
    simpa [smallKRatio] using smallK_ratio_gt_four
  have hq' : (4 : ℝ) < (smallKNumerator / smallKDenominator : ℚ) := by
    exact_mod_cast hq
  rw [maynardRatio, hN, hI]
  simpa using hq'

theorem maynardM_gt_four_of_smallKCandidate
    (hF : MaynardAdmissible 105 smallKCandidate)
    (hI : 0 < maynardI 105 smallKCandidate)
    (hbound : BddAbove (maynardRatioSet 105))
    (hId : maynardI 105 smallKCandidate = (smallKDenominator : ℝ))
    (hNd : (∑ m : Fin 105, maynardJ 105 m smallKCandidate) =
      (smallKNumerator : ℝ)) :
    (4 : ℝ) < maynardM 105 := by
  exact lt_of_lt_of_le
    (smallK_candidate_ratio_gt_four_of_functionals hId hNd)
    (maynard_ratio_le_M hF hI hbound)

theorem maynardM_gt_four_of_smallKCandidate_of_functionals
    (hbound : BddAbove (maynardRatioSet 105))
    (hId : maynardI 105 smallKCandidate = (smallKDenominator : ℝ))
    (hNd : (∑ m : Fin 105, maynardJ 105 m smallKCandidate) =
      (smallKNumerator : ℝ)) :
    (4 : ℝ) < maynardM 105 := by
  exact maynardM_gt_four_of_smallKCandidate smallKCandidate_admissible
    (smallKCandidate_I_pos_of_denominator_identity hId) hbound hId hNd

end
end BoundedGaps.Maynard
