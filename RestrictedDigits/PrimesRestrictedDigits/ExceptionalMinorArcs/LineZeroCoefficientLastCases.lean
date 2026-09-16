import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientFiberCount
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The last two zero-coefficient cases

The cases `v3 = 0` and `v4 = 0` require a separate zero-target branch.
This repairs the phrase "entirely analogous" in `MAYNARD-PRD-PUBLISHED`,
Lemma 15.2, pp. 210--211, without treating zero as having finitely many
factor pairs.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem zero_third_target_structure
    {X : Nat} {C : Finset (Fin X)} {V : Real}
    {w : LowHeightPlaneWitness X}
    (hw : w ∈ zeroThirdCoefficientPlaneWitnesses C V)
    (htarget : w.v 1 * (w.a2.val : Int) + w.v4 = 0) :
    And (w.v 0 = 0) (w.v 1 ≠ 0) := by
  have hwCase := Finset.mem_filter.mp hw
  have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
  have hwCandidate := mem_positivePlaneWitnessCandidates.mp hwZero.1
  have hwRelation := hwZero.2.1
  have hproduct : w.v 0 * (w.a1.val : Int) = 0 := by
    have hrelation := LowHeightPlaneWitness.relation_eq hwRelation
    rw [hwCase.2] at hrelation
    linear_combination hrelation - htarget
  have ha1 : (w.a1.val : Int) ≠ 0 := by
    exact_mod_cast hwCandidate.2.1.ne'
  have hv1 : w.v 0 = 0 :=
    (Int.mul_eq_zero.mp hproduct).resolve_right ha1
  refine ⟨hv1, ?_⟩
  intro hv2
  have hv4 : w.v4 = 0 := by
    rw [hv2] at htarget
    simpa using htarget
  have hvAll : w.v = 0 := by
    funext i
    fin_cases i
    · exact hv1
    · exact hv2
    · exact hwCase.2
  exact hwRelation.1.elim (fun h => h hvAll) (fun h => h hv4)

private theorem zero_fourth_target_structure
    {X : Nat} {C : Finset (Fin X)} {V : Real}
    {w : LowHeightPlaneWitness X} (hX : X ≠ 0)
    (hw : w ∈ zeroFourthCoefficientPlaneWitnesses C V)
    (htarget : w.v 1 * (w.a2.val : Int) + w.v 2 * (X : Int) = 0) :
    And (w.v 0 = 0) (w.v 1 ≠ 0) := by
  have hwCase := Finset.mem_filter.mp hw
  have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
  have hwCandidate := mem_positivePlaneWitnessCandidates.mp hwZero.1
  have hwRelation := hwZero.2.1
  have hproduct : w.v 0 * (w.a1.val : Int) = 0 := by
    have hrelation := LowHeightPlaneWitness.relation_eq hwRelation
    rw [hwCase.2] at hrelation
    linear_combination hrelation - htarget
  have ha1 : (w.a1.val : Int) ≠ 0 := by
    exact_mod_cast hwCandidate.2.1.ne'
  have hv1 : w.v 0 = 0 :=
    (Int.mul_eq_zero.mp hproduct).resolve_right ha1
  refine ⟨hv1, ?_⟩
  intro hv2
  have hXInt : (X : Int) ≠ 0 := by exact_mod_cast hX
  have hv3Product : w.v 2 * (X : Int) = 0 := by
    rw [hv2] at htarget
    simpa using htarget
  have hv3 : w.v 2 = 0 :=
    (Int.mul_eq_zero.mp hv3Product).resolve_right hXInt
  have hvAll : w.v = 0 := by
    funext i
    fin_cases i
    · exact hv1
    · exact hv2
    · exact hv3
  exact hwRelation.1.elim (fun h => h hvAll) (fun h => h hwCase.2)

/-- The `v3=0` case is the sum of a signed divisor branch and a uniquely
determined zero-target branch. -/
theorem zeroThirdCoefficientPlaneWitnesses_card_real_le
    {X : Nat} (C : Finset (Fin X)) (V Q : Real)
    (hV : 1 <= V) (hVX : V < (X : Real))
    (hQ : 1 <= Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) <= 3 * ((X : Real) ^ 2) ->
      (z.divisorsAntidiag.card : Real) <= Q) :
    ((zeroThirdCoefficientPlaneWitnesses C V).card : Real) <=
      2 * (C.card : Real) *
        ((lineCoefficientBox V).card : Real) ^ 2 * Q := by
  classical
  let Cpos := C.filter fun a => 0 < a.val
  let coeff := lineCoefficientBox V
  let S := zeroThirdCoefficientPlaneWitnesses C V
  let target : LowHeightPlaneWitness X -> Int := fun w =>
    -(w.v 1 * (w.a2.val : Int) + w.v4)
  let Snonzero := S.filter fun w => target w ≠ 0
  let Szero := S.filter fun w => target w = 0
  let outer := Cpos.product (coeff.product coeff)
  let key : LowHeightPlaneWitness X -> Prod (Fin X) (Prod Int Int) :=
    fun w => (w.a2, (w.v 1, w.v4))
  let targetOfKey : Prod (Fin X) (Prod Int Int) -> Int := fun k =>
    -(k.2.1 * (k.1.val : Int) + k.2.2)
  let embedding : LowHeightPlaneWitness X -> Prod Int Int := fun w =>
    (w.v 0, (w.a1.val : Int))
  have hVNonneg : 0 <= V := zero_le_one.trans hV
  have hmaps : Set.MapsTo key (Snonzero : Set (LowHeightPlaneWitness X))
      (outer : Set (Prod (Fin X) (Prod Int Int))) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hwData := mem_positivePlaneWitnessCandidates.mp hwZero.1
    change key w ∈ outer
    dsimp only [outer, Cpos, coeff, key]
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨hwData.2.2.1, hwData.2.2.2.1⟩,
      Finset.mem_product.mpr
        ⟨hwData.2.2.2.2.1 1, hwData.2.2.2.2.2⟩⟩
  have hnonzero : forall w, w ∈ Snonzero -> targetOfKey (key w) ≠ 0 := by
    intro w hw
    simpa only [targetOfKey, key, target] using (Finset.mem_filter.mp hw).2
  have hproduct : forall w, w ∈ Snonzero ->
      (embedding w).1 * (embedding w).2 = targetOfKey (key w) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hrelation := LowHeightPlaneWitness.relation_eq hwZero.2.1
    dsimp only [embedding, targetOfKey, key]
    rw [hwCase.2] at hrelation
    linear_combination hrelation
  have hinjective : forall k, Set.InjOn embedding
      (Snonzero.filter fun w => key w = k : Set (LowHeightPlaneWitness X)) := by
    intro k w hw w' hw' hembedding
    have hwData := Finset.mem_filter.mp hw
    have hw'Data := Finset.mem_filter.mp hw'
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hwData.1).1
    have hw'Case := Finset.mem_filter.mp (Finset.mem_filter.mp hw'Data.1).1
    have hkey : key w = key w' := hwData.2.trans hw'Data.2.symm
    apply LowHeightPlaneWitness.ext
    · apply Fin.ext
      have hval : (w.a1.val : Int) = (w'.a1.val : Int) :=
        congrArg (fun q => q.2) hembedding
      exact_mod_cast hval
    · exact congrArg (fun q => q.1) hkey
    · funext i
      fin_cases i
      · exact congrArg (fun q => q.1) hembedding
      · exact congrArg (fun q => q.2.1) hkey
      · exact hwCase.2.trans hw'Case.2.symm
    · exact congrArg (fun q => q.2.2) hkey
  have hbound : forall w, w ∈ Snonzero ->
      ((targetOfKey (key w)).natAbs : Real) <= 3 * ((X : Real) ^ 2) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hwRelation := hwZero.2.1
    have h := lineZeroTermTarget_natAbs_le_three_mul_sq
      w.a2 (w.v 1) 0 w.v4 hVNonneg hVX (hwRelation.2.1 1)
        (by simpa using hVNonneg) hwRelation.2.2.1
    simpa only [targetOfKey, key, Int.natAbs_neg, zero_mul, add_zero] using h
  have hnonzeroCard : (Snonzero.card : Real) <=
      (outer.card : Real) * Q :=
    lineZeroCoefficient_card_nonzero_target_real_le
      Snonzero outer key targetOfKey embedding
      (3 * ((X : Real) ^ 2)) Q hmaps hnonzero hproduct hinjective
        hbound (zero_le_one.trans hQ) hfactor
  let zeroKey : LowHeightPlaneWitness X -> Prod (Fin X) (Prod Int Int) :=
    fun w => (w.a1, (w.v 1, w.v4))
  have hzeroMaps : Set.MapsTo zeroKey
      (Szero : Set (LowHeightPlaneWitness X))
      (outer : Set (Prod (Fin X) (Prod Int Int))) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hwData := mem_positivePlaneWitnessCandidates.mp hwZero.1
    change zeroKey w ∈ outer
    dsimp only [outer, Cpos, coeff, zeroKey]
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨hwData.1, hwData.2.1⟩,
      Finset.mem_product.mpr
        ⟨hwData.2.2.2.2.1 1, hwData.2.2.2.2.2⟩⟩
  have hzeroInjective : Set.InjOn zeroKey
      (Szero : Set (LowHeightPlaneWitness X)) := by
    intro w hw w' hw' hkey
    have hwData := Finset.mem_filter.mp hw
    have hw'Data := Finset.mem_filter.mp hw'
    have hwTarget : w.v 1 * (w.a2.val : Int) + w.v4 = 0 := by
      simpa only [target, neg_eq_zero] using hwData.2
    have hw'Target : w'.v 1 * (w'.a2.val : Int) + w'.v4 = 0 := by
      simpa only [target, neg_eq_zero] using hw'Data.2
    have hwStructure := zero_third_target_structure hwData.1 hwTarget
    have hw'Structure := zero_third_target_structure hw'Data.1 hw'Target
    have hv2 : w.v 1 = w'.v 1 := congrArg (fun q => q.2.1) hkey
    have hv4 : w.v4 = w'.v4 := congrArg (fun q => q.2.2) hkey
    have hw'TargetAligned :
        w.v 1 * (w'.a2.val : Int) + w.v4 = 0 := by
      rw [hv2, hv4]
      exact hw'Target
    have hmul : w.v 1 * (w.a2.val : Int) =
        w.v 1 * (w'.a2.val : Int) := by
      linear_combination hwTarget - hw'TargetAligned
    have ha2Val : (w.a2.val : Int) = (w'.a2.val : Int) :=
      mul_left_cancel₀ hwStructure.2 hmul
    apply LowHeightPlaneWitness.ext
    · exact congrArg (fun q => q.1) hkey
    · apply Fin.ext
      exact_mod_cast ha2Val
    · funext i
      fin_cases i
      · exact hwStructure.1.trans hw'Structure.1.symm
      · exact hv2
      · have hwCase := Finset.mem_filter.mp hwData.1
        have hw'Case := Finset.mem_filter.mp hw'Data.1
        exact hwCase.2.trans hw'Case.2.symm
    · exact hv4
  have hzeroCard : (Szero.card : Real) <= (outer.card : Real) := by
    exact_mod_cast Finset.card_le_card_of_injOn zeroKey hzeroMaps hzeroInjective
  have hsplit : S = Snonzero ∪ Szero := by
    ext w
    by_cases h : target w = 0 <;>
      simp [Snonzero, Szero, h]
  have houter : (outer.card : Real) <=
      (C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2 := by
    simpa only [outer, Cpos, coeff] using
      lineZeroCoefficient_last_case_outer_card_real_le C V
  have houterNonneg : 0 <= (outer.card : Real) := Nat.cast_nonneg _
  have hzeroCardQ : (Szero.card : Real) <= (outer.card : Real) * Q := by
    calc
      (Szero.card : Real) <= (outer.card : Real) := hzeroCard
      _ = (outer.card : Real) * 1 := by ring
      _ <= (outer.card : Real) * Q := by
        simpa using mul_le_mul_of_nonneg_left hQ houterNonneg
  have hsplitCard : (S.card : Real) <=
      (Snonzero.card : Real) + (Szero.card : Real) := by
    have hnat : S.card <= Snonzero.card + Szero.card := by
      rw [hsplit]
      exact Finset.card_union_le Snonzero Szero
    exact_mod_cast hnat
  calc
    ((zeroThirdCoefficientPlaneWitnesses C V).card : Real) = S.card := rfl
    _ <= (Snonzero.card : Real) + (Szero.card : Real) := hsplitCard
    _ <= (outer.card : Real) * Q + (outer.card : Real) * Q :=
      add_le_add hnonzeroCard hzeroCardQ
    _ = 2 * (outer.card : Real) * Q := by ring
    _ <= 2 * ((C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2) * Q := by
      gcongr
    _ = 2 * (C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2 * Q := by ring

/-- The `v4=0` case has the same repaired split, with the scale coefficient
retained in the target. -/
theorem zeroFourthCoefficientPlaneWitnesses_card_real_le
    {X : Nat} (C : Finset (Fin X)) (V Q : Real)
    (hV : 1 <= V) (hVX : V < (X : Real))
    (hQ : 1 <= Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) <= 3 * ((X : Real) ^ 2) ->
      (z.divisorsAntidiag.card : Real) <= Q) :
    ((zeroFourthCoefficientPlaneWitnesses C V).card : Real) <=
      2 * (C.card : Real) *
        ((lineCoefficientBox V).card : Real) ^ 2 * Q := by
  classical
  let Cpos := C.filter fun a => 0 < a.val
  let coeff := lineCoefficientBox V
  let S := zeroFourthCoefficientPlaneWitnesses C V
  let target : LowHeightPlaneWitness X -> Int := fun w =>
    -(w.v 1 * (w.a2.val : Int) + w.v 2 * (X : Int))
  let Snonzero := S.filter fun w => target w ≠ 0
  let Szero := S.filter fun w => target w = 0
  let outer := Cpos.product (coeff.product coeff)
  let key : LowHeightPlaneWitness X -> Prod (Fin X) (Prod Int Int) :=
    fun w => (w.a2, (w.v 1, w.v 2))
  let targetOfKey : Prod (Fin X) (Prod Int Int) -> Int := fun k =>
    -(k.2.1 * (k.1.val : Int) + k.2.2 * (X : Int))
  let embedding : LowHeightPlaneWitness X -> Prod Int Int := fun w =>
    (w.v 0, (w.a1.val : Int))
  have hVNonneg : 0 <= V := zero_le_one.trans hV
  have hX : X ≠ 0 := by
    have hXReal : (0 : Real) < X := by linarith
    exact_mod_cast hXReal.ne'
  have hmaps : Set.MapsTo key (Snonzero : Set (LowHeightPlaneWitness X))
      (outer : Set (Prod (Fin X) (Prod Int Int))) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hwData := mem_positivePlaneWitnessCandidates.mp hwZero.1
    change key w ∈ outer
    dsimp only [outer, Cpos, coeff, key]
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨hwData.2.2.1, hwData.2.2.2.1⟩,
      Finset.mem_product.mpr
        ⟨hwData.2.2.2.2.1 1, hwData.2.2.2.2.1 2⟩⟩
  have hnonzero : forall w, w ∈ Snonzero -> targetOfKey (key w) ≠ 0 := by
    intro w hw
    simpa only [targetOfKey, key, target] using (Finset.mem_filter.mp hw).2
  have hproduct : forall w, w ∈ Snonzero ->
      (embedding w).1 * (embedding w).2 = targetOfKey (key w) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hrelation := LowHeightPlaneWitness.relation_eq hwZero.2.1
    dsimp only [embedding, targetOfKey, key]
    rw [hwCase.2] at hrelation
    linear_combination hrelation
  have hinjective : forall k, Set.InjOn embedding
      (Snonzero.filter fun w => key w = k : Set (LowHeightPlaneWitness X)) := by
    intro k w hw w' hw' hembedding
    have hwData := Finset.mem_filter.mp hw
    have hw'Data := Finset.mem_filter.mp hw'
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hwData.1).1
    have hw'Case := Finset.mem_filter.mp (Finset.mem_filter.mp hw'Data.1).1
    have hkey : key w = key w' := hwData.2.trans hw'Data.2.symm
    apply LowHeightPlaneWitness.ext
    · apply Fin.ext
      have hval : (w.a1.val : Int) = (w'.a1.val : Int) :=
        congrArg (fun q => q.2) hembedding
      exact_mod_cast hval
    · exact congrArg (fun q => q.1) hkey
    · funext i
      fin_cases i
      · exact congrArg (fun q => q.1) hembedding
      · exact congrArg (fun q => q.2.1) hkey
      · exact congrArg (fun q => q.2.2) hkey
    · exact hwCase.2.trans hw'Case.2.symm
  have hbound : forall w, w ∈ Snonzero ->
      ((targetOfKey (key w)).natAbs : Real) <= 3 * ((X : Real) ^ 2) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hwRelation := hwZero.2.1
    have h := lineZeroTermTarget_natAbs_le_three_mul_sq
      w.a2 (w.v 1) (w.v 2) 0 hVNonneg hVX (hwRelation.2.1 1)
        (hwRelation.2.1 2) (by simpa using hVNonneg)
    simpa only [targetOfKey, key, Int.natAbs_neg, add_zero] using h
  have hnonzeroCard : (Snonzero.card : Real) <=
      (outer.card : Real) * Q :=
    lineZeroCoefficient_card_nonzero_target_real_le
      Snonzero outer key targetOfKey embedding
      (3 * ((X : Real) ^ 2)) Q hmaps hnonzero hproduct hinjective
        hbound (zero_le_one.trans hQ) hfactor
  let zeroKey : LowHeightPlaneWitness X -> Prod (Fin X) (Prod Int Int) :=
    fun w => (w.a1, (w.v 1, w.v 2))
  have hzeroMaps : Set.MapsTo zeroKey
      (Szero : Set (LowHeightPlaneWitness X))
      (outer : Set (Prod (Fin X) (Prod Int Int))) := by
    intro w hw
    have hwCase := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
    have hwZero := mem_positiveZeroCoefficientPlaneWitnesses.mp hwCase.1
    have hwData := mem_positivePlaneWitnessCandidates.mp hwZero.1
    change zeroKey w ∈ outer
    dsimp only [outer, Cpos, coeff, zeroKey]
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨hwData.1, hwData.2.1⟩,
      Finset.mem_product.mpr
        ⟨hwData.2.2.2.2.1 1, hwData.2.2.2.2.1 2⟩⟩
  have hzeroInjective : Set.InjOn zeroKey
      (Szero : Set (LowHeightPlaneWitness X)) := by
    intro w hw w' hw' hkey
    have hwData := Finset.mem_filter.mp hw
    have hw'Data := Finset.mem_filter.mp hw'
    have hwTarget :
        w.v 1 * (w.a2.val : Int) + w.v 2 * (X : Int) = 0 := by
      simpa only [target, neg_eq_zero] using hwData.2
    have hw'Target :
        w'.v 1 * (w'.a2.val : Int) + w'.v 2 * (X : Int) = 0 := by
      simpa only [target, neg_eq_zero] using hw'Data.2
    have hwStructure := zero_fourth_target_structure hX hwData.1 hwTarget
    have hw'Structure := zero_fourth_target_structure hX hw'Data.1 hw'Target
    have hv2 : w.v 1 = w'.v 1 := congrArg (fun q => q.2.1) hkey
    have hv3 : w.v 2 = w'.v 2 := congrArg (fun q => q.2.2) hkey
    have hw'TargetAligned :
        w.v 1 * (w'.a2.val : Int) + w.v 2 * (X : Int) = 0 := by
      rw [hv2, hv3]
      exact hw'Target
    have hmul : w.v 1 * (w.a2.val : Int) =
        w.v 1 * (w'.a2.val : Int) := by
      linear_combination hwTarget - hw'TargetAligned
    have ha2Val : (w.a2.val : Int) = (w'.a2.val : Int) :=
      mul_left_cancel₀ hwStructure.2 hmul
    apply LowHeightPlaneWitness.ext
    · exact congrArg (fun q => q.1) hkey
    · apply Fin.ext
      exact_mod_cast ha2Val
    · funext i
      fin_cases i
      · exact hwStructure.1.trans hw'Structure.1.symm
      · exact hv2
      · exact hv3
    · have hwCase := Finset.mem_filter.mp hwData.1
      have hw'Case := Finset.mem_filter.mp hw'Data.1
      exact hwCase.2.trans hw'Case.2.symm
  have hzeroCard : (Szero.card : Real) <= (outer.card : Real) := by
    exact_mod_cast Finset.card_le_card_of_injOn zeroKey hzeroMaps hzeroInjective
  have hsplit : S = Snonzero ∪ Szero := by
    ext w
    by_cases h : target w = 0 <;>
      simp [Snonzero, Szero, h]
  have houter : (outer.card : Real) <=
      (C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2 := by
    simpa only [outer, Cpos, coeff] using
      lineZeroCoefficient_last_case_outer_card_real_le C V
  have houterNonneg : 0 <= (outer.card : Real) := Nat.cast_nonneg _
  have hzeroCardQ : (Szero.card : Real) <= (outer.card : Real) * Q := by
    calc
      (Szero.card : Real) <= (outer.card : Real) := hzeroCard
      _ = (outer.card : Real) * 1 := by ring
      _ <= (outer.card : Real) * Q := by
        simpa using mul_le_mul_of_nonneg_left hQ houterNonneg
  have hsplitCard : (S.card : Real) <=
      (Snonzero.card : Real) + (Szero.card : Real) := by
    have hnat : S.card <= Snonzero.card + Szero.card := by
      rw [hsplit]
      exact Finset.card_union_le Snonzero Szero
    exact_mod_cast hnat
  calc
    ((zeroFourthCoefficientPlaneWitnesses C V).card : Real) = S.card := rfl
    _ <= (Snonzero.card : Real) + (Szero.card : Real) := hsplitCard
    _ <= (outer.card : Real) * Q + (outer.card : Real) * Q :=
      add_le_add hnonzeroCard hzeroCardQ
    _ = 2 * (outer.card : Real) * Q := by ring
    _ <= 2 * ((C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2) * Q := by
      gcongr
    _ = 2 * (C.card : Real) * ((lineCoefficientBox V).card : Real) ^ 2 * Q := by ring

end PrimesRestrictedDigits
