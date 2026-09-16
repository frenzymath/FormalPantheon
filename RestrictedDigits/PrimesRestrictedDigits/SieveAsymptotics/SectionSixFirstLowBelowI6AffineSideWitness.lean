import PrimesRestrictedDigits.BasicEstimates.FiniteRationalGeometry
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6RationalBoxAdapter
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6ArgumentLowerBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6BranchRanges
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FiberCover
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Fixed-delta affine side witnesses for the I6 low-below region

This is the pointwise bridge from the exact eleven-conjunct region to the finite list of
rational affine constraints used by checked subdivisions. It does not build a tree, prove a
cover-validity Boolean, or make an analytic or numerical claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

def i6D690Delta : Real := 1 / 1000000

def i6D690ThetaOneRat : Rat := 180001 / 500000

def i6D690ThetaTwoRat : Rat := 212499 / 500000

def i6D690OneMinusThetaTwoRat : Rat := 287501 / 500000

def i6D690OneMinusThetaOneRat : Rat := 319999 / 500000

theorem i6D690_thetaOne_cast :
    (i6D690ThetaOneRat : Real) = sectionSixThetaOne i6D690Delta := by
  norm_num [i6D690ThetaOneRat, i6D690Delta, sectionSixThetaOne]

theorem i6D690_thetaTwo_cast :
    (i6D690ThetaTwoRat : Real) = sectionSixThetaTwo i6D690Delta := by
  norm_num [i6D690ThetaTwoRat, i6D690Delta, sectionSixThetaTwo]

theorem i6D690_reflectedLow_cast :
    (i6D690OneMinusThetaTwoRat : Real) =
      1 - sectionSixThetaTwo i6D690Delta := by
  norm_num [i6D690OneMinusThetaTwoRat, i6D690Delta, sectionSixThetaTwo]

theorem i6D690_reflectedHigh_cast :
    (i6D690OneMinusThetaOneRat : Real) =
      1 - sectionSixThetaOne i6D690Delta := by
  norm_num [i6D690OneMinusThetaOneRat, i6D690Delta, sectionSixThetaOne]

def i6D690Affine (coefficient : Fin 4 -> Rat) : RationalAffine 4 :=
  { constant := 0, coefficient := coefficient }

def i6D690Constraint (coefficient : Fin 4 -> Rat)
    (relation : RationalAffineRelation) (bound : Rat) :
    RationalAffineConstraint 4 :=
  { affine := i6D690Affine coefficient, relation := relation, bound := bound }

def i6D690BaseConstraint (rho : Bool) : RationalAffineConstraint 4 :=
  match rho with
  | false => i6D690Constraint ![1, 1, 1, 0] .upperOpen i6D690ThetaOneRat
  | true => i6D690Constraint ![1, 1, 1, 0] .lowerOpen i6D690ThetaTwoRat

def i6D690BranchConstraints (b : Fin 3) :
    List (RationalAffineConstraint 4) :=
  if b = (0 : Fin 3) then
    [ i6D690Constraint ![1, 1, 1, 2] .upperClosed 1,
      i6D690Constraint ![1, 1, 1, 3] .lowerClosed 1 ]
  else if b = (1 : Fin 3) then
    [ i6D690Constraint ![1, 1, 1, 3] .upperClosed 1,
      i6D690Constraint ![1, 1, 1, 4] .lowerClosed 1 ]
  else
    [i6D690Constraint ![1, 1, 1, 4] .upperClosed 1]

def i6D690BranchHolds (b : Fin 3) (z : AffinePoint 4) : Prop :=
  if b = (0 : Fin 3) then
    (i6D690Constraint ![1, 1, 1, 2] .upperClosed 1).holds z ∧
      (i6D690Constraint ![1, 1, 1, 3] .lowerClosed 1).holds z
  else if b = (1 : Fin 3) then
    (i6D690Constraint ![1, 1, 1, 3] .upperClosed 1).holds z ∧
      (i6D690Constraint ![1, 1, 1, 4] .lowerClosed 1).holds z
  else
    (i6D690Constraint ![1, 1, 1, 4] .upperClosed 1).holds z

def i6D690BandLowConstraint (i : Fin 5) :
    RationalAffineConstraint 4 :=
  if i = (0 : Fin 5) then
    i6D690Constraint ![1, 1, 0, 1] .upperOpen i6D690ThetaOneRat
  else if i = (1 : Fin 5) then
    i6D690Constraint ![1, 0, 1, 1] .upperOpen i6D690ThetaOneRat
  else if i = (2 : Fin 5) then
    i6D690Constraint ![0, 1, 1, 1] .upperOpen i6D690ThetaOneRat
  else if i = (3 : Fin 5) then
    i6D690Constraint ![1, 1, 1, 1] .upperOpen i6D690ThetaOneRat
  else
    i6D690Constraint ![1, 1, 1, 1] .upperOpen
      i6D690OneMinusThetaTwoRat

def i6D690BandHighConstraint (i : Fin 5) :
    RationalAffineConstraint 4 :=
  if i = (0 : Fin 5) then
    i6D690Constraint ![1, 1, 0, 1] .lowerOpen i6D690ThetaTwoRat
  else if i = (1 : Fin 5) then
    i6D690Constraint ![1, 0, 1, 1] .lowerOpen i6D690ThetaTwoRat
  else if i = (2 : Fin 5) then
    i6D690Constraint ![0, 1, 1, 1] .lowerOpen i6D690ThetaTwoRat
  else if i = (3 : Fin 5) then
    i6D690Constraint ![1, 1, 1, 1] .lowerOpen i6D690ThetaTwoRat
  else
    i6D690Constraint ![1, 1, 1, 1] .lowerOpen
      i6D690OneMinusThetaOneRat

def i6D690SelectedBandConstraint (sigma : Fin 5 → Bool) (i : Fin 5) :
    RationalAffineConstraint 4 :=
  if sigma i = false then i6D690BandLowConstraint i
  else i6D690BandHighConstraint i

def i6D690BandList (sigma : Fin 5 → Bool) :
    List (RationalAffineConstraint 4) :=
  [ i6D690SelectedBandConstraint sigma 0,
    i6D690SelectedBandConstraint sigma 1,
    i6D690SelectedBandConstraint sigma 2,
    i6D690SelectedBandConstraint sigma 3,
    i6D690SelectedBandConstraint sigma 4 ]

def i6D690BandHolds (sigma : Fin 5 → Bool) (z : AffinePoint 4) : Prop :=
  ∀ i, (i6D690SelectedBandConstraint sigma i).holds z

def i6D690ConstraintList (rho : Bool) (b : Fin 3)
    (sigma : Fin 5 → Bool) : List (RationalAffineConstraint 4) :=
  i6D690BaseConstraint rho :: i6D690BranchConstraints b ++ i6D690BandList sigma

def i6D690Holds (rho : Bool) (b : Fin 3) (sigma : Fin 5 → Bool)
    (z : AffinePoint 4) : Prop :=
  (i6D690BaseConstraint rho).holds z ∧
    i6D690BranchHolds b z ∧ i6D690BandHolds sigma z

theorem i6D690_branchHolds_iff_forall_mem (b : Fin 3) (z : AffinePoint 4) :
    i6D690BranchHolds b z ↔
      ∀ c ∈ i6D690BranchConstraints b, c.holds z := by
  fin_cases b <;>
    simp [i6D690BranchHolds, i6D690BranchConstraints]

theorem i6D690_bandHolds_iff_forall_mem
    (sigma : Fin 5 → Bool) (z : AffinePoint 4) :
    i6D690BandHolds sigma z ↔
      ∀ c ∈ i6D690BandList sigma, c.holds z := by
  constructor
  · intro h c hc
    have hc' : c = i6D690SelectedBandConstraint sigma 0 ∨
        c = i6D690SelectedBandConstraint sigma 1 ∨
        c = i6D690SelectedBandConstraint sigma 2 ∨
        c = i6D690SelectedBandConstraint sigma 3 ∨
        c = i6D690SelectedBandConstraint sigma 4 := by
      simpa [i6D690BandList] using hc
    rcases hc' with rfl | rfl | rfl | rfl | rfl
    · exact h 0
    · exact h 1
    · exact h 2
    · exact h 3
    · exact h 4
  · intro h i
    exact h _ (by
      fin_cases i <;> simp [i6D690BandList])

theorem i6D690Holds_iff_forall_mem
    (rho : Bool) (b : Fin 3) (sigma : Fin 5 → Bool)
    (z : AffinePoint 4) :
    i6D690Holds rho b sigma z ↔
      ∀ c ∈ i6D690ConstraintList rho b sigma, c.holds z := by
  rw [i6D690Holds]
  constructor
  · rintro ⟨hbase, hbranch, hband⟩ c hc
    have hc' : c = i6D690BaseConstraint rho ∨
        c ∈ i6D690BranchConstraints b ++ i6D690BandList sigma := by
      simpa [i6D690ConstraintList] using hc
    rcases hc' with hcb | hc
    · subst c
      exact hbase
    · have hc'' : c ∈ i6D690BranchConstraints b ∨
          c ∈ i6D690BandList sigma := by
        simpa using hc
      rcases hc'' with hbranchMem | hbandMem
      · exact (i6D690_branchHolds_iff_forall_mem b z).1 hbranch _
          hbranchMem
      · exact (i6D690_bandHolds_iff_forall_mem sigma z).1 hband _
          hbandMem
  · intro h
    refine ⟨h _ (by simp [i6D690ConstraintList]), ?_, ?_⟩
    · exact (i6D690_branchHolds_iff_forall_mem b z).2 (fun c hc =>
        h c (by simp [i6D690ConstraintList, hc]))
    · exact (i6D690_bandHolds_iff_forall_mem sigma z).2 (fun c hc =>
        h c (by simp [i6D690ConstraintList, hc]))

def i6D690BandLowerReal (u v w : Real) : Fin 5 → Real :=
  ![ sectionSixThetaOne i6D690Delta - u - v,
      sectionSixThetaOne i6D690Delta - u - w,
      sectionSixThetaOne i6D690Delta - v - w,
      sectionSixThetaOne i6D690Delta - u - v - w,
      1 - sectionSixThetaTwo i6D690Delta - u - v - w ]

def i6D690BandUpperReal (u v w : Real) : Fin 5 → Real :=
  ![ sectionSixThetaTwo i6D690Delta - u - v,
      sectionSixThetaTwo i6D690Delta - u - w,
      sectionSixThetaTwo i6D690Delta - v - w,
      sectionSixThetaTwo i6D690Delta - u - v - w,
      1 - sectionSixThetaOne i6D690Delta - u - v - w ]

private theorem i6D690_not_mem_Icc {a b y : Real} (_hab : a < b)
    (hy : y ∉ Icc a b) : y < a ∨ b < y := by
  by_cases hay : a <= y
  · right
    exact lt_of_not_ge (fun hby => hy ⟨hay, hby⟩)
  · exact Or.inl (lt_of_not_ge hay)

private theorem i6D690_base_false_holds
    {u v w t : Real} (h : u + v + w < sectionSixThetaOne i6D690Delta) :
    (i6D690BaseConstraint false).holds
      (i6D686Coordinates (((u, v), w), t)) := by
  simp [i6D690BaseConstraint, i6D690Constraint, i6D690Affine,
    RationalAffineConstraint.holds, RationalAffine.evalReal,
    i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaOne_cast]
  ring_nf
  linarith

private theorem i6D690_base_true_holds
    {u v w t : Real} (h : sectionSixThetaTwo i6D690Delta < u + v + w) :
    (i6D690BaseConstraint true).holds
      (i6D686Coordinates (((u, v), w), t)) := by
  simp [i6D690BaseConstraint, i6D690Constraint, i6D690Affine,
    RationalAffineConstraint.holds, RationalAffine.evalReal,
    i6D686Coordinates, Fin.sum_univ_succ, i6D690_thetaTwo_cast]
  ring_nf
  linarith

private theorem i6D690_branch_zero_holds
    {u v w t : Real} (hupper : u + v + w + 2 * t <= 1)
    (hlower : (1 : Real) <= u + v + w + 3 * t) :
    i6D690BranchHolds 0 (i6D686Coordinates (((u, v), w), t)) := by
  simp only [i6D690BranchHolds]
  constructor
  · simp [i6D690Constraint, i6D690Affine,
      RationalAffineConstraint.holds, RationalAffine.evalReal,
      i6D686Coordinates, Fin.sum_univ_succ]
    ring_nf
    linarith
  · simp [i6D690Constraint, i6D690Affine,
      RationalAffineConstraint.holds, RationalAffine.evalReal,
      i6D686Coordinates, Fin.sum_univ_succ]
    ring_nf
    linarith

private theorem i6D690_branch_one_holds
    {u v w t : Real} (hupper : u + v + w + 3 * t <= 1)
    (hlower : (1 : Real) <= u + v + w + 4 * t) :
    i6D690BranchHolds 1 (i6D686Coordinates (((u, v), w), t)) := by
  simp only [i6D690BranchHolds]
  constructor
  · simp [i6D690Constraint, i6D690Affine,
      RationalAffineConstraint.holds, RationalAffine.evalReal,
      i6D686Coordinates, Fin.sum_univ_succ]
    ring_nf
    linarith
  · simp [i6D690Constraint, i6D690Affine,
      RationalAffineConstraint.holds, RationalAffine.evalReal,
      i6D686Coordinates, Fin.sum_univ_succ]
    ring_nf
    linarith

private theorem i6D690_branch_two_holds
    {u v w t : Real} (hupper : u + v + w + 4 * t <= 1) :
    i6D690BranchHolds 2 (i6D686Coordinates (((u, v), w), t)) := by
  simp only [i6D690BranchHolds]
  simp [i6D690Constraint, i6D690Affine,
    RationalAffineConstraint.holds, RationalAffine.evalReal,
    i6D686Coordinates, Fin.sum_univ_succ]
  ring_nf
  linarith

private theorem i6D690_band_low_holds
    {u v w t : Real} (sigma : Fin 5 → Bool)
    (hsigma : ∀ i, sigma i = false ->
      t < i6D690BandLowerReal u v w i)
    (hhigh : ∀ i, sigma i = true ->
      i6D690BandUpperReal u v w i < t) :
    i6D690BandHolds sigma (i6D686Coordinates (((u, v), w), t)) := by
  intro i
  by_cases hi : sigma i = false
  · have h := hsigma i hi
    simp [i6D690SelectedBandConstraint, hi]
    fin_cases i <;>
      simp [i6D690BandLowConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, i6D690BandLowerReal, Fin.sum_univ_succ,
        i6D690_thetaOne_cast, i6D690_reflectedLow_cast] at h ⊢ <;>
      ring_nf at h ⊢ <;> linarith
  · have hi' : sigma i = true := by
      cases h : sigma i <;> simp_all
    have h := hhigh i hi'
    simp [i6D690SelectedBandConstraint, hi']
    fin_cases i <;>
      simp [i6D690BandHighConstraint, i6D690Constraint, i6D690Affine,
        RationalAffineConstraint.holds, RationalAffine.evalReal,
        i6D686Coordinates, i6D690BandUpperReal, Fin.sum_univ_succ,
        i6D690_thetaTwo_cast, i6D690_reflectedHigh_cast] at h ⊢ <;>
      ring_nf at h ⊢ <;> linarith

theorem i6D690_exists_affine_side_witness
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowBelowQuadrupleRegion
      (1 / 1000000 : Real)) :
    ∃ rho : Bool, ∃ b : Fin 3, ∃ sigma : Fin 5 → Bool,
      i6D690Holds rho b sigma (i6D686Coordinates x) := by
  rcases x with ⟨⟨⟨u, v⟩, w⟩, t⟩
  change sectionSixThetaGap i6D690Delta < t /\
    t <= w /\ w <= v /\ v <= u /\ u + v <
      sectionSixThetaOne i6D690Delta /\
    u + v + w ∉ Icc (sectionSixThetaOne i6D690Delta)
      (sectionSixThetaTwo i6D690Delta) /\
    u + v + t ∉ Icc (sectionSixThetaOne i6D690Delta)
      (sectionSixThetaTwo i6D690Delta) /\
    u + w + t ∉ Icc (sectionSixThetaOne i6D690Delta)
      (sectionSixThetaTwo i6D690Delta) /\
    v + w + t ∉ Icc (sectionSixThetaOne i6D690Delta)
      (sectionSixThetaTwo i6D690Delta) /\
    u + v + w + t ∉ Icc (sectionSixThetaOne i6D690Delta)
      (sectionSixThetaTwo i6D690Delta) /\
    u + v + w + t ∉ Icc (1 - sectionSixThetaTwo i6D690Delta)
      (1 - sectionSixThetaOne i6D690Delta) at hx
  rcases hx with ⟨hgaplt, htw, hwv, hvu, huv, hbaseNot,
    h0not, h1not, h2not, h3not, h4not⟩
  have hgap : 0 < sectionSixThetaGap i6D690Delta := by
    norm_num [i6D690Delta, sectionSixThetaGap, sectionSixThetaOne,
      sectionSixThetaTwo]
  have htheta : sectionSixThetaOne i6D690Delta <
      sectionSixThetaTwo i6D690Delta := by
    have hg : 0 < sectionSixThetaTwo i6D690Delta -
        sectionSixThetaOne i6D690Delta := by
      simpa [sectionSixThetaGap] using hgap
    exact sub_pos.mp hg
  have hy : 1 < (1 - u - v - w - t) / t := by
    apply sectionSixFirstLowBelowQuadruple_argument_gt_one
      (epsilon := i6D690Delta) (x := (((u, v), w), t))
    norm_num [i6D690Delta]
    exact ⟨hgaplt, htw, hwv, hvu, huv, hbaseNot, h0not, h1not,
      h2not, h3not, h4not⟩
  have hranges := sectionSixFirstLowBelowQuadruple_branch_ranges
    (epsilon := i6D690Delta) (x := (((u, v), w), t)) hgap
      ⟨hgaplt, htw, hwv, hvu, huv, hbaseNot, h0not, h1not, h2not,
        h3not, h4not⟩
  have hbase : u + v + w < sectionSixThetaOne i6D690Delta ∨
      sectionSixThetaTwo i6D690Delta < u + v + w := by
    exact i6D690_not_mem_Icc htheta hbaseNot
  let sigma : Fin 5 → Bool := fun i =>
    if i6D690BandUpperReal u v w i < t then true else false
  have hside : ∀ i : Fin 5,
      t < i6D690BandLowerReal u v w i ∨
        i6D690BandUpperReal u v w i < t := by
    intro i
    fin_cases i
    · rcases i6D690_not_mem_Icc htheta h0not with h | h
      · left
        change t < sectionSixThetaOne i6D690Delta - u - v
        linarith
      · right
        change sectionSixThetaTwo i6D690Delta - u - v < t
        linarith
    · rcases i6D690_not_mem_Icc htheta h1not with h | h
      · left
        change t < sectionSixThetaOne i6D690Delta - u - w
        linarith
      · right
        change sectionSixThetaTwo i6D690Delta - u - w < t
        linarith
    · rcases i6D690_not_mem_Icc htheta h2not with h | h
      · left
        change t < sectionSixThetaOne i6D690Delta - v - w
        linarith
      · right
        change sectionSixThetaTwo i6D690Delta - v - w < t
        linarith
    · rcases i6D690_not_mem_Icc htheta h3not with h | h
      · left
        change t < sectionSixThetaOne i6D690Delta - u - v - w
        linarith
      · right
        change sectionSixThetaTwo i6D690Delta - u - v - w < t
        linarith
    · have href : 1 - sectionSixThetaTwo i6D690Delta <
          1 - sectionSixThetaOne i6D690Delta := by linarith
      rcases i6D690_not_mem_Icc href h4not with h | h
      · left
        change t < 1 - sectionSixThetaTwo i6D690Delta - u - v - w
        linarith
      · right
        change 1 - sectionSixThetaOne i6D690Delta - u - v - w < t
        linarith
  have hlow : ∀ i, sigma i = false ->
      t < i6D690BandLowerReal u v w i := by
    intro i hi
    have hnot : ¬ i6D690BandUpperReal u v w i < t := by
      simpa [sigma] using hi
    exact (hside i).resolve_right hnot
  have hhigh : ∀ i, sigma i = true ->
      i6D690BandUpperReal u v w i < t := by
    intro i hi
    have hi' : i6D690BandUpperReal u v w i < t := by
      simpa [sigma] using hi
    exact hi'
  have hband := i6D690_band_low_holds sigma hlow hhigh
  rcases hbase with hbase | hbase
  · have hbaseHold := i6D690_base_false_holds hbase (t := t)
    by_cases hy2 : (1 - u - v - w - t) / t <= 2
    · have hi := (hranges.2.2).1 ⟨hy.le, hy2⟩
      refine ⟨false, 0, sigma, ?_⟩
      exact ⟨hbaseHold, i6D690_branch_zero_holds (by linarith [hi.2])
        (by linarith [hi.1]), hband⟩
    · have hy2' : 2 <= (1 - u - v - w - t) / t := le_of_not_ge hy2
      by_cases hy3 : (1 - u - v - w - t) / t <= 3
      · have hm := (hranges.2.1).1 ⟨hy2', hy3⟩
        refine ⟨false, 1, sigma, ?_⟩
        exact ⟨hbaseHold, i6D690_branch_one_holds (by linarith [hm.1])
          (by linarith [hm.2]), hband⟩
      · have ht3 : 3 <= (1 - u - v - w - t) / t := le_of_not_ge hy3
        have ht := hranges.1.1 ht3
        refine ⟨false, 2, sigma, ?_⟩
        exact ⟨hbaseHold, i6D690_branch_two_holds (by linarith [ht]), hband⟩
  · have hbaseHold := i6D690_base_true_holds hbase (t := t)
    by_cases hy2 : (1 - u - v - w - t) / t <= 2
    · have hi := (hranges.2.2).1 ⟨hy.le, hy2⟩
      refine ⟨true, 0, sigma, ?_⟩
      exact ⟨hbaseHold, i6D690_branch_zero_holds (by linarith [hi.2])
        (by linarith [hi.1]), hband⟩
    · have hy2' : 2 <= (1 - u - v - w - t) / t := le_of_not_ge hy2
      by_cases hy3 : (1 - u - v - w - t) / t <= 3
      · have hm := (hranges.2.1).1 ⟨hy2', hy3⟩
        refine ⟨true, 1, sigma, ?_⟩
        exact ⟨hbaseHold, i6D690_branch_one_holds (by linarith [hm.1])
          (by linarith [hm.2]), hband⟩
      · have ht3 : 3 <= (1 - u - v - w - t) / t := le_of_not_ge hy3
        have ht := hranges.1.1 ht3
        refine ⟨true, 2, sigma, ?_⟩
        exact ⟨hbaseHold, i6D690_branch_two_holds (by linarith [ht]), hband⟩

end

end PrimesRestrictedDigits
