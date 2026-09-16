import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelSigmaExtremes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Necessary active-label reduction for the fixed I6 native cover

This module records only the logical filter forced by native-target membership. It is a
necessary condition, not a nonemptiness characterization. The fixed-delta source cover is
reindexed through the resulting finite subtype; labels outside the predicate are proved empty.
No tree, replay, or cap is introduced here.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowBelowI6D730ActiveLabel (label : i6D691Label) : Prop :=
  ((label.2.2 (1 : Fin 5) = true -> label.2.2 (0 : Fin 5) = true) ∧
    (label.2.2 (2 : Fin 5) = true -> label.2.2 (1 : Fin 5) = true) ∧
    (label.2.2 (3 : Fin 5) = false ->
      label.2.2 (0 : Fin 5) = false ∧ label.2.2 (4 : Fin 5) = false) ∧
    (label.2.2 (4 : Fin 5) = true -> label.2.2 (2 : Fin 5) = true)) ∧
    ((label.1 = false ->
      label.2.2 (0 : Fin 5) = false ∧ label.2.2 (4 : Fin 5) = false) ∧
      (label.1 = true -> label.2.2 (3 : Fin 5) = true))

theorem sectionSixFirstLowBelowI6_native_membership_admissible
    (label : i6D691Label)
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D691NativeTarget label) :
    sectionSixFirstLowBelowI6D730ActiveLabel label := by
  have hmono := sectionSixFirstLowBelowI6_native_target_sigma_monotone label hx
  have hs3 := fun h =>
    sectionSixFirstLowBelowI6_native_target_sigmaThree_false_forces_all_low
      label hx h
  have hs4 := fun h =>
    sectionSixFirstLowBelowI6_native_target_sigmaFour_true_forces_all_high
      label hx h
  have h01 : label.2.2 (1 : Fin 5) = true ->
      label.2.2 (0 : Fin 5) = true := hmono.1
  have h12 : label.2.2 (2 : Fin 5) = true ->
      label.2.2 (1 : Fin 5) = true := hmono.2
  have h3 : label.2.2 (3 : Fin 5) = false ->
      label.2.2 (0 : Fin 5) = false ∧ label.2.2 (4 : Fin 5) = false := by
    intro h
    exact ⟨(hs3 h).2 0, (hs3 h).2 4⟩
  have h4 : label.2.2 (4 : Fin 5) = true ->
      label.2.2 (2 : Fin 5) = true := by
    intro h
    exact (hs4 h).2 2
  have hrho0 : label.1 = false ->
      label.2.2 (0 : Fin 5) = false ∧ label.2.2 (4 : Fin 5) = false := by
    intro hrho
    constructor
    · cases hzero : label.2.2 (0 : Fin 5)
      · rfl
      · have hempty := i6D727_native_target_empty_of_rhoFalse_sigmaZero
          label hrho hzero
        rw [hempty] at hx
        simp at hx
    · cases hfour : label.2.2 (4 : Fin 5)
      · rfl
      · have hall := hs4 hfour
        exact Bool.noConfusion (hrho.symm.trans hall.1)
  have hrho1 : label.1 = true -> label.2.2 (3 : Fin 5) = true := by
    intro hrho
    cases hthree : label.2.2 (3 : Fin 5)
    · have hall := hs3 hthree
      exact Bool.noConfusion (hrho.symm.trans hall.1)
    · rfl
  exact ⟨⟨h01, h12, h3, h4⟩, ⟨hrho0, hrho1⟩⟩

theorem sectionSixFirstLowBelowI6D730_activeLabel_finite :
    Finite {l : i6D691Label // sectionSixFirstLowBelowI6D730ActiveLabel l} := by
  infer_instance

theorem sectionSixFirstLowBelowI6_exactRegion_subset_active_iUnion :
    sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ⊆
      ⋃ label : {l : i6D691Label // sectionSixFirstLowBelowI6D730ActiveLabel l},
        i6D691NativeTarget label.1 := by
  intro x hx
  obtain ⟨label, hlabel⟩ := Set.mem_iUnion.1
    (i6D691_exactRegion_subset_iUnion_nativeTarget hx)
  have hadm := sectionSixFirstLowBelowI6_native_membership_admissible label hlabel
  refine Set.mem_iUnion.2 ⟨⟨label, hadm⟩, ?_⟩
  exact hlabel

theorem sectionSixFirstLowBelowI6_nativeTarget_eq_empty_of_inactive
    (label : i6D691Label)
    (hinactive : ¬ sectionSixFirstLowBelowI6D730ActiveLabel label) :
    i6D691NativeTarget label =
      (∅ : Set (((Real × Real) × Real) × Real)) := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  rcases hnonempty with ⟨x, hx⟩
  exact hinactive (sectionSixFirstLowBelowI6_native_membership_admissible label hx)

end

end PrimesRestrictedDigits
