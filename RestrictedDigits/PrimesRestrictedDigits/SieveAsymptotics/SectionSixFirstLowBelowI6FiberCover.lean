import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6ArgumentLowerBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6BranchRanges
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Fixed-base I6 fiber cells

This is the geometry-only fixed `delta = 1 / 1000000` cover for the low-below quadruple term.
It records the five `t`-dependent band choices, the independent base-family witness, and the
three weak Buchstab branches. No payload, replay, or integral estimate is asserted here.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), `R_4`.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

private abbrev i6Delta : Real := 1 / 1000000

def sectionSixFirstLowBelowI6Fiber (u v w : Real) : Set Real :=
  {t | (((u, v), w), t) ∈ sectionSixFirstLowBelowQuadrupleRegion i6Delta}

def sectionSixFirstLowBelowI6BaseFamily
    (u v w : Real) (rho : Bool) : Prop :=
  (rho = false ∧ u + v + w < sectionSixThetaOne i6Delta) ∨
    (rho = true ∧ sectionSixThetaTwo i6Delta < u + v + w)

private def sectionSixFirstLowBelowI6BandExpr
    (u v w t : Real) : Fin 5 → Real :=
  ![u + v + t, u + w + t, v + w + t,
    u + v + w + t, u + v + w + t]

def sectionSixFirstLowBelowI6BandLower
    (u v w : Real) : Fin 5 → Real :=
  ![sectionSixThetaOne i6Delta - u - v,
    sectionSixThetaOne i6Delta - u - w,
    sectionSixThetaOne i6Delta - v - w,
    sectionSixThetaOne i6Delta - u - v - w,
    1 - sectionSixThetaTwo i6Delta - u - v - w]

def sectionSixFirstLowBelowI6BandUpper
    (u v w : Real) : Fin 5 → Real :=
  ![sectionSixThetaTwo i6Delta - u - v,
    sectionSixThetaTwo i6Delta - u - w,
    sectionSixThetaTwo i6Delta - v - w,
    sectionSixThetaTwo i6Delta - u - v - w,
    1 - sectionSixThetaOne i6Delta - u - v - w]

def sectionSixFirstLowBelowI6BranchLower
    (u v w : Real) : Fin 3 → Real :=
  ![(1 - u - v - w) / 3, (1 - u - v - w) / 4,
    sectionSixThetaGap i6Delta]

def sectionSixFirstLowBelowI6BranchUpper
    (u v w : Real) : Fin 3 → Real :=
  ![(1 - u - v - w) / 2, (1 - u - v - w) / 3,
    (1 - u - v - w) / 4]

private def sectionSixFirstLowBelowI6MaxFold (f : Fin 5 → Real) : Real :=
  max 0 (max (f 0) (max (f 1) (max (f 2) (max (f 3) (f 4)))))

private def sectionSixFirstLowBelowI6MinFold (f : Fin 5 → Real) : Real :=
  min 1 (min (f 0) (min (f 1) (min (f 2) (min (f 3) (f 4)))))

def sectionSixFirstLowBelowI6CellLower
    (u v w : Real) (b : Fin 3) (sigma : Fin 5 → Bool) : Real :=
  max (sectionSixThetaGap i6Delta)
    (max (sectionSixFirstLowBelowI6BranchLower u v w b)
      (sectionSixFirstLowBelowI6MaxFold (fun i =>
        if sigma i = true then
          sectionSixFirstLowBelowI6BandUpper u v w i else 0)))

def sectionSixFirstLowBelowI6CellUpper
    (u v w : Real) (b : Fin 3) (sigma : Fin 5 → Bool) : Real :=
  min w
    (min (sectionSixFirstLowBelowI6BranchUpper u v w b)
      (sectionSixFirstLowBelowI6MinFold (fun i =>
        if sigma i = true then 1 else
          sectionSixFirstLowBelowI6BandLower u v w i)))

def sectionSixFirstLowBelowI6FiberCell
    (u v w : Real) (b : Fin 3) (sigma : Fin 5 → Bool) : Set Real :=
  Icc (sectionSixFirstLowBelowI6CellLower u v w b sigma)
    (sectionSixFirstLowBelowI6CellUpper u v w b sigma)

private theorem i6MaxFold_le {f : Fin 5 → Real} {z : Real}
    (hz : 0 <= z) (hf : ∀ i, f i <= z) :
    sectionSixFirstLowBelowI6MaxFold f <= z := by
  unfold sectionSixFirstLowBelowI6MaxFold
  exact max_le hz (max_le (hf 0)
    (max_le (hf 1) (max_le (hf 2) (max_le (hf 3) (hf 4)))))

private theorem le_i6MinFold {f : Fin 5 → Real} {z : Real}
    (hz : z <= 1) (hf : ∀ i, z <= f i) :
    z <= sectionSixFirstLowBelowI6MinFold f := by
  unfold sectionSixFirstLowBelowI6MinFold
  exact le_min hz (le_min (hf 0)
    (le_min (hf 1) (le_min (hf 2) (le_min (hf 3) (hf 4)))))

private theorem i6_not_mem_Icc {a b x : Real}
    (_hab : a < b) (h : x ∉ Icc a b) : x < a ∨ b < x := by
  by_cases hax : a <= x
  · right
    exact lt_of_not_ge (fun hxb => h ⟨hax, hxb⟩)
  · exact Or.inl (lt_of_not_ge hax)

private theorem sectionSixFirstLowBelowI6FiberCell_mem_of_bounds
    {u v w t : Real} {b : Fin 3} {sigma : Fin 5 → Bool}
    (hgap : 0 < sectionSixThetaGap i6Delta)
    (ht : sectionSixThetaGap i6Delta < t) (htw : t <= w)
    (hbranchLower :
      sectionSixFirstLowBelowI6BranchLower u v w b <= t)
    (hbranchUpper :
      t <= sectionSixFirstLowBelowI6BranchUpper u v w b)
    (hlow : ∀ i, sigma i = false ->
      t <= sectionSixFirstLowBelowI6BandLower u v w i)
    (hhigh : ∀ i, sigma i = true ->
      sectionSixFirstLowBelowI6BandUpper u v w i <= t)
    (hwv : w <= v) (hvu : v <= u)
    (huv : u + v < sectionSixThetaOne i6Delta) :
    t ∈ sectionSixFirstLowBelowI6FiberCell u v w b sigma := by
  have ht0 : 0 <= t := (hgap.trans ht).le
  have ht1 : t <= 1 := by
    have htheta : sectionSixThetaOne i6Delta < 1 := by
      norm_num [i6Delta, sectionSixThetaOne]
    have hv : 0 < v := (hgap.trans ht).trans_le htw |>.trans_le hwv
    have hbase : u < sectionSixThetaOne i6Delta := by linarith
    have hu : t <= u := le_trans htw (le_trans hwv hvu)
    linarith
  apply mem_Icc.mpr
  constructor
  · unfold sectionSixFirstLowBelowI6CellLower
    apply max_le
    · exact ht.le
    · apply max_le hbranchLower
      apply i6MaxFold_le ht0
      intro i
      by_cases hi : sigma i = true
      · simpa [hi] using hhigh i hi
      · simp [hi, ht0]
  · unfold sectionSixFirstLowBelowI6CellUpper
    apply le_min htw
    apply le_min hbranchUpper
    apply le_i6MinFold ht1
    intro i
    by_cases hi : sigma i = true
    · simp [hi, ht1]
    · have hi' : sigma i = false := by
        cases h : sigma i <;> simp_all
      simpa [hi] using hlow i hi'

/--
The fixed tail/all-high constructor used to transport a certified Cartesian cell into the
labelled fiber cover. The finite folds stay private; callers only supply their five upper-band
and tail-endpoint inequalities.
-/
theorem sectionSixFirstLowBelowI6FiberCell_mem_tail_allHigh_of_bounds
    {u v w t : Real}
    (hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real))
    (ht : sectionSixThetaGap (1 / 1000000 : Real) < t)
    (htw : t <= w)
    (h0 : sectionSixThetaTwo (1 / 1000000 : Real) - u - v <= t)
    (h1 : sectionSixThetaTwo (1 / 1000000 : Real) - u - w <= t)
    (h2 : sectionSixThetaTwo (1 / 1000000 : Real) - v - w <= t)
    (h3 : sectionSixThetaTwo (1 / 1000000 : Real) - u - v - w <= t)
    (h4 : 1 - sectionSixThetaOne (1 / 1000000 : Real) - u - v - w <= t)
    (htail : t <= (1 - u - v - w) / 4)
    (hwv : w <= v) (hvu : v <= u)
    (huv : u + v < sectionSixThetaOne (1 / 1000000 : Real)) :
    t ∈ sectionSixFirstLowBelowI6FiberCell u v w (2 : Fin 3)
      (fun _ : Fin 5 => true) := by
  have hgap' : 0 < sectionSixThetaGap i6Delta := by
    simpa [i6Delta] using hgap
  have ht' : sectionSixThetaGap i6Delta < t := by
    simpa [i6Delta] using ht
  have huv' : u + v < sectionSixThetaOne i6Delta := by
    simpa [i6Delta] using huv
  refine sectionSixFirstLowBelowI6FiberCell_mem_of_bounds
    hgap' ht' htw ?_ ?_ ?_ ?_ hwv hvu huv'
  · change sectionSixThetaGap i6Delta <= t
    exact ht'.le
  · change t <= (1 - u - v - w) / 4
    exact htail
  · intro i hi
    simp at hi
  · intro i hi
    fin_cases i
    · simpa [sectionSixFirstLowBelowI6BandUpper, i6Delta] using h0
    · simpa [sectionSixFirstLowBelowI6BandUpper, i6Delta] using h1
    · simpa [sectionSixFirstLowBelowI6BandUpper, i6Delta] using h2
    · simpa [sectionSixFirstLowBelowI6BandUpper, i6Delta] using h3
    · simpa [sectionSixFirstLowBelowI6BandUpper, i6Delta] using h4

/-
  The all-high tail adapter needs only the two endpoint projections below.
  Keeping this fact here preserves the private finite-fold boundary.
-/
theorem sectionSixFirstLowBelowI6FiberCell_tail_allHigh_endpoint_bounds
    {u v w : Real} :
    sectionSixThetaGap (1 / 1000000 : Real) <=
        sectionSixFirstLowBelowI6CellLower u v w (2 : Fin 3)
          (fun _ : Fin 5 => true) /\
      sectionSixFirstLowBelowI6CellUpper u v w (2 : Fin 3)
          (fun _ : Fin 5 => true) <=
        (1 - u - v - w) / 4 := by
  constructor
  · have h := le_max_left (sectionSixThetaGap i6Delta)
      (max (sectionSixFirstLowBelowI6BranchLower u v w (2 : Fin 3))
        (sectionSixFirstLowBelowI6MaxFold (fun i =>
          if (fun _ : Fin 5 => true) i = true then
            sectionSixFirstLowBelowI6BandUpper u v w i else 0)))
    change sectionSixThetaGap i6Delta <=
      sectionSixFirstLowBelowI6CellLower u v w (2 : Fin 3)
        (fun _ : Fin 5 => true)
    exact h
  · have hUpper :
        sectionSixFirstLowBelowI6CellUpper u v w (2 : Fin 3)
            (fun _ : Fin 5 => true) <=
          sectionSixFirstLowBelowI6BranchUpper u v w (2 : Fin 3) := by
      unfold sectionSixFirstLowBelowI6CellUpper
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    simpa [sectionSixFirstLowBelowI6BranchUpper] using hUpper

theorem sectionSixFirstLowBelowI6Fiber_mem_branchCell
    {u v w t : Real}
    (hgap : 0 < sectionSixThetaGap i6Delta)
    (ht : t ∈ sectionSixFirstLowBelowI6Fiber u v w) :
    ∃ rho : Bool, sectionSixFirstLowBelowI6BaseFamily u v w rho ∧
      ∃ b : Fin 3, ∃ sigma : Fin 5 → Bool,
        t ∈ sectionSixFirstLowBelowI6FiberCell u v w b sigma := by
  change (((u, v), w), t) ∈
    sectionSixFirstLowBelowQuadrupleRegion i6Delta at ht
  rcases ht with ⟨hgaplt, htw, hwv, hvu, huv, hbaseNot,
    h0not, h1not, h2not, h3not, h4not⟩
  change u + v + w ∉ Icc (sectionSixThetaOne i6Delta)
      (sectionSixThetaTwo i6Delta) at hbaseNot
  change u + v + t ∉ Icc (sectionSixThetaOne i6Delta)
      (sectionSixThetaTwo i6Delta) at h0not
  change u + w + t ∉ Icc (sectionSixThetaOne i6Delta)
      (sectionSixThetaTwo i6Delta) at h1not
  change v + w + t ∉ Icc (sectionSixThetaOne i6Delta)
      (sectionSixThetaTwo i6Delta) at h2not
  change u + v + w + t ∉ Icc (sectionSixThetaOne i6Delta)
      (sectionSixThetaTwo i6Delta) at h3not
  change u + v + w + t ∉ Icc (1 - sectionSixThetaTwo i6Delta)
      (1 - sectionSixThetaOne i6Delta) at h4not
  have htPos : 0 < t := hgap.trans hgaplt
  have hy : 1 < (1 - u - v - w - t) / t := by
    exact sectionSixFirstLowBelowQuadruple_argument_gt_one
      (epsilon := i6Delta) (by norm_num) ⟨hgaplt, htw, hwv, hvu, huv,
        hbaseNot, h0not, h1not, h2not, h3not, h4not⟩
  have hranges := sectionSixFirstLowBelowQuadruple_branch_ranges
    (epsilon := i6Delta)
    (x := (((u, v), w), t)) hgap
      ⟨hgaplt, htw, hwv, hvu, huv, hbaseNot, h0not, h1not, h2not, h3not,
        h4not⟩
  have hbase : u + v + w < sectionSixThetaOne i6Delta ∨
      sectionSixThetaTwo i6Delta < u + v + w := by
    have htheta : sectionSixThetaOne i6Delta <
        sectionSixThetaTwo i6Delta := by
      have hgap' : 0 < sectionSixThetaTwo i6Delta -
          sectionSixThetaOne i6Delta := by
        simpa [sectionSixThetaGap] using hgap
      exact sub_pos.mp hgap'
    exact i6_not_mem_Icc htheta hbaseNot
  have htheta : sectionSixThetaOne i6Delta <
      sectionSixThetaTwo i6Delta := by
    have hgap' : 0 < sectionSixThetaTwo i6Delta -
        sectionSixThetaOne i6Delta := by
      simpa [sectionSixThetaGap] using hgap
    exact sub_pos.mp hgap'
  have hthetaRef : 1 - sectionSixThetaTwo i6Delta <
      1 - sectionSixThetaOne i6Delta := by linarith
  let sigma : Fin 5 → Bool := fun i =>
    if sectionSixFirstLowBelowI6BandUpper u v w i <= t then true else false
  have hside : ∀ i : Fin 5,
      t <= sectionSixFirstLowBelowI6BandLower u v w i ∨
        sectionSixFirstLowBelowI6BandUpper u v w i <= t := by
    intro i
    fin_cases i
    · rcases i6_not_mem_Icc htheta h0not with h | h
      · left; change t <= sectionSixThetaOne i6Delta - u - v
        linarith
      · right; change sectionSixThetaTwo i6Delta - u - v <= t
        linarith
    · rcases i6_not_mem_Icc htheta h1not with h | h
      · left; change t <= sectionSixThetaOne i6Delta - u - w
        linarith
      · right; change sectionSixThetaTwo i6Delta - u - w <= t
        linarith
    · rcases i6_not_mem_Icc htheta h2not with h | h
      · left; change t <= sectionSixThetaOne i6Delta - v - w
        linarith
      · right; change sectionSixThetaTwo i6Delta - v - w <= t
        linarith
    · rcases i6_not_mem_Icc htheta h3not with h | h
      · left; change t <= sectionSixThetaOne i6Delta - u - v - w
        linarith
      · right; change sectionSixThetaTwo i6Delta - u - v - w <= t
        linarith
    · rcases i6_not_mem_Icc hthetaRef h4not with h | h
      · left; change t <= 1 - sectionSixThetaTwo i6Delta - u - v - w
        linarith
      · right; change 1 - sectionSixThetaOne i6Delta - u - v - w <= t
        linarith
  have hlow : ∀ i, sigma i = false ->
      t <= sectionSixFirstLowBelowI6BandLower u v w i := by
    intro i hi
    have hnot : ¬ sectionSixFirstLowBelowI6BandUpper u v w i <= t := by
      simpa [sigma] using hi
    exact (hside i).resolve_right hnot
  have hhigh : ∀ i, sigma i = true ->
      sectionSixFirstLowBelowI6BandUpper u v w i <= t := by
    intro i hi
    have hi' : sectionSixFirstLowBelowI6BandUpper u v w i <= t := by
      simpa [sigma] using hi
    exact hi'
  have hcell : ∃ b : Fin 3, ∃ sigma : Fin 5 → Bool,
      t ∈ sectionSixFirstLowBelowI6FiberCell u v w b sigma := by
    by_cases hy2 : (1 - u - v - w - t) / t <= 2
    · have hi := (hranges.2.2).1 ⟨hy.le, hy2⟩
      refine ⟨0, sigma, ?_⟩
      refine sectionSixFirstLowBelowI6FiberCell_mem_of_bounds
        hgap hgaplt htw ?_ ?_ hlow hhigh hwv hvu huv
      · change (1 - u - v - w) / 3 <= t
        linarith [hi.1]
      · change t <= (1 - u - v - w) / 2
        linarith [hi.2]
    · have hy2' : 2 <= (1 - u - v - w - t) / t := le_of_not_ge hy2
      by_cases hy3 : (1 - u - v - w - t) / t <= 3
      · have hm := (hranges.2.1).1 ⟨hy2', hy3⟩
        refine ⟨1, sigma, ?_⟩
        refine sectionSixFirstLowBelowI6FiberCell_mem_of_bounds
          hgap hgaplt htw ?_ ?_ hlow hhigh hwv hvu huv
        · change (1 - u - v - w) / 4 <= t
          linarith [hm.2]
        · change t <= (1 - u - v - w) / 3
          linarith [hm.1]
      · have ht3 : 3 <= (1 - u - v - w - t) / t := le_of_not_ge hy3
        have htail := hranges.1.1 ht3
        refine ⟨2, sigma, ?_⟩
        refine sectionSixFirstLowBelowI6FiberCell_mem_of_bounds
          hgap hgaplt htw ?_ ?_ hlow hhigh hwv hvu huv
        · change sectionSixThetaGap i6Delta <= t
          exact hgaplt.le
        · change t <= (1 - u - v - w) / 4
          linarith [htail]
  rcases hbase with hbase | hbase
  · exact ⟨false, Or.inl ⟨rfl, hbase⟩, hcell⟩
  · exact ⟨true, Or.inr ⟨rfl, hbase⟩, hcell⟩

theorem sectionSixFirstLowBelowI6Fiber_eq_empty_of_le_gap
    {u v w : Real}
    (hwGap : w <= sectionSixThetaGap i6Delta) :
    sectionSixFirstLowBelowI6Fiber u v w = ∅ := by
  ext t
  constructor
  · intro ht
    change (((u, v), w), t) ∈
      sectionSixFirstLowBelowQuadrupleRegion i6Delta at ht
    exact False.elim (not_lt_of_ge hwGap (lt_of_lt_of_le ht.1 ht.2.1))
  · simp

end

end PrimesRestrictedDigits
