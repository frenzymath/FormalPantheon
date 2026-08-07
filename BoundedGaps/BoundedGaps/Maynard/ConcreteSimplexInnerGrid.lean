import BoundedGaps.Maynard.ConcreteRadiusMargin

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def fractionalGridIndex (H : Finset ℕ) (m : ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset fun _ => Finset.range m

def fractionalGridLower {H : Finset ℕ} (m : ℕ) (j : H → ℕ) : H → ℝ :=
  fun h => (j h : ℝ) / m

def fractionalGridUpper {H : Finset ℕ} (m : ℕ) (j : H → ℕ) : H → ℝ :=
  fun h => ((j h + 1 : ℕ) : ℝ) / m

def fractionalSimplexInnerGridIndex (H : Finset ℕ) (m : ℕ) :
    Finset (H → ℕ) :=
  (fractionalGridIndex H m).filter fun j =>
    ∑ h : H, fractionalGridUpper m j h < 1

theorem fractionalGridEndpoints_mem_Icc
    {H : Finset ℕ} {m : ℕ} (hm : 0 < m)
    {j : H → ℕ} (hj : j ∈ fractionalGridIndex H m) (h : H) :
    fractionalGridLower m j h ∈ Set.Icc (0 : ℝ) 1 ∧
      fractionalGridUpper m j h ∈ Set.Icc (0 : ℝ) 1 ∧
      fractionalGridLower m j h ≤ fractionalGridUpper m j h := by
  rw [fractionalGridIndex, Fintype.mem_piFinset] at hj
  have hjlt : j h < m := Finset.mem_range.mp (hj h)
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hjSucc : j h + 1 ≤ m := Nat.succ_le_of_lt hjlt
  have hjSuccReal : ((j h + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hjSucc
  have hjReal : (j h : ℝ) ≤ m := by
    exact_mod_cast (Nat.le_of_lt hjlt)
  unfold fractionalGridLower fractionalGridUpper
  constructor
  · exact ⟨by positivity, (div_le_one hmReal).2 hjReal⟩
  constructor
  · exact ⟨by positivity, (div_le_one hmReal).2 hjSuccReal⟩
  · exact (div_le_div_iff_of_pos_right hmReal).2 (by exact_mod_cast Nat.le_succ (j h))

theorem fractionalSimplexInnerGridIndex_data
    {H : Finset ℕ} {m : ℕ} (hm : 0 < m)
    {j : H → ℕ} (hj : j ∈ fractionalSimplexInnerGridIndex H m) :
    (∀ h : H,
      fractionalGridLower m j h ∈ Set.Icc (0 : ℝ) 1 ∧
      fractionalGridUpper m j h ∈ Set.Icc (0 : ℝ) 1 ∧
      fractionalGridLower m j h ≤ fractionalGridUpper m j h) ∧
      ∑ h : H, fractionalGridUpper m j h < 1 := by
  have hjData := Finset.mem_filter.mp hj
  exact ⟨fun h => fractionalGridEndpoints_mem_Icc hm hjData.1 h, hjData.2⟩

def engelsmaSimplexInnerGridSupport
    (H : Finset ℕ) (alpha : ℝ) (m N : ℕ) : Finset (H → ℕ) :=
  (fractionalSimplexInnerGridIndex H m).biUnion fun j =>
    engelsmaFractionalTupleShell H alpha
      (fractionalGridLower m j) (fractionalGridUpper m j) N

def normalizedEngelsmaSimplexInnerGridStepMass
    (H : Finset ℕ) (alpha : ℝ) (m N : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex H m,
    normalizedEngelsmaFractionalTupleShellMass H alpha
      (fractionalGridLower m j) (fractionalGridUpper m j) N

def simplexInnerGridVolume (H : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex H m,
    ∏ h : H, (fractionalGridUpper m j h - fractionalGridLower m j h)

theorem eventually_engelsmaSimplexInnerGridSupport_subset
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaSimplexInnerGridSupport H alpha m N ⊆
        preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) := by
  let I := fractionalSimplexInnerGridIndex H m
  have hcells : ∀ᶠ N : ℕ in atTop, ∀ j ∈ I,
      engelsmaFractionalTupleShell H alpha
          (fractionalGridLower m j) (fractionalGridUpper m j) N ⊆
        preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) := by
    apply I.eventually_all.mpr
    intro j hj
    have hjData := fractionalSimplexInnerGridIndex_data hm hj
    exact eventually_engelsmaFractionalTupleShell_subset_preSievedSimplexTupleSupport
      halpha (fractionalGridLower m j) (fractionalGridUpper m j)
      (fun h => (hjData.1 h).2.1.1) hjData.2
  filter_upwards [hcells] with N hcellsN
  intro u hu
  rw [engelsmaSimplexInnerGridSupport, Finset.mem_biUnion] at hu
  obtain ⟨j, hj, huj⟩ := hu
  exact hcellsN j hj huj

theorem tendsto_normalizedEngelsmaSimplexInnerGridStepMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaSimplexInnerGridStepMass H alpha m N)
      atTop (nhds (simplexInnerGridVolume H m)) := by
  let I := fractionalSimplexInnerGridIndex H m
  have hlim :=
    tendsto_finite_linear_combination_normalizedEngelsmaFractionalTupleShellMass
      halpha I (fun _ => (1 : ℝ))
      (fun j => fractionalGridLower m j)
      (fun j => fractionalGridUpper m j)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hm hj).1 h |>.1)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hm hj).1 h |>.2.1)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hm hj).1 h |>.2.2)
  simpa [I, normalizedEngelsmaSimplexInnerGridStepMass,
    simplexInnerGridVolume] using hlim

end BoundedGaps.Maynard
