import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6AffineEndpointRowsD1004
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6OrderedPairRootD999
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronRegionRegularityD924

/-!
# Exact closed affine chamber walls for I6

Inactive comparison rows are zero walls; inactive selected indices give empty chambers. Every
wall keeps its equality boundary. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq.
(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

def i6D1005BaseWall : Bool -> RationalAffine 3
  | false => ⟨180001 / 500000, ![-1, -1, -1]⟩
  | true => ⟨-212499 / 500000, ![1, 1, 1]⟩

def i6D1005ChamberWalls (label : i6D691Label) (l h : Fin 7) :
    Fin 16 -> RationalAffine 3 :=
  let sub (a b : RationalAffine 3) : RationalAffine 3 :=
    ⟨a.constant - b.constant, fun j => a.coefficient j - b.coefficient j⟩
  let lower (i : Fin 7) := if i6D1004LowerActive label i = true then
    sub (i6D1004LowerAffine label.2.1 l) (i6D1004LowerAffine label.2.1 i)
    else ⟨0, fun _ => 0⟩
  let upper (i : Fin 7) := if i6D1004UpperActive label i = true then
    sub (i6D1004UpperAffine label.2.1 i) (i6D1004UpperAffine label.2.1 h)
    else ⟨0, fun _ => 0⟩
  ![i6D1005BaseWall label.1,
    sub (i6D1004UpperAffine label.2.1 h) (i6D1004LowerAffine label.2.1 l),
    lower 0, lower 1, lower 2, lower 3, lower 4, lower 5, lower 6,
    upper 0, upper 1, upper 2, upper 3, upper 4, upper 5, upper 6]

def i6D1005Chamber (label : i6D691Label) (l h : Fin 7) : Set (Fin 3 -> Real) :=
  {x | i6D1004LowerActive label l = true ∧ i6D1004UpperActive label h = true ∧
    x ∈ i6D999OrderedPairRoot.region ∧ ∀ j, 0 ≤ (i6D1005ChamberWalls label l h j).evalReal x}

theorem i6D1005BaseWall_eval (rho : Bool) (x : Fin 3 -> Real) :
    (i6D1005BaseWall rho).evalReal x =
      if rho then x 0 + x 1 + x 2 - 212499 / 500000
      else 180001 / 500000 - x 0 - x 1 - x 2 := by
  cases rho <;>
    norm_num [i6D1005BaseWall, RationalAffine.evalReal, Fin.sum_univ_succ] <;> ring

theorem i6D1005ChamberWalls_nonneg_iff
    (label : i6D691Label) (l h : Fin 7) (x : Fin 3 -> Real) :
    (∀ j, 0 ≤ (i6D1005ChamberWalls label l h j).evalReal x) ↔
      0 ≤ (i6D1005BaseWall label.1).evalReal x ∧
      (i6D1004LowerAffine label.2.1 l).evalReal x ≤
        (i6D1004UpperAffine label.2.1 h).evalReal x ∧
      (∀ i, i6D1004LowerActive label i = true ->
        (i6D1004LowerAffine label.2.1 i).evalReal x ≤
          (i6D1004LowerAffine label.2.1 l).evalReal x) ∧
      (∀ i, i6D1004UpperActive label i = true ->
        (i6D1004UpperAffine label.2.1 h).evalReal x ≤
          (i6D1004UpperAffine label.2.1 i).evalReal x) := by
  have hsub (a b : RationalAffine 3) :
      (⟨a.constant - b.constant,
        fun j => a.coefficient j - b.coefficient j⟩ : RationalAffine 3).evalReal x =
          a.evalReal x - b.evalReal x := by
    simp only [RationalAffine.evalReal, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hrow (active : Bool) (a b : RationalAffine 3) :
      0 ≤ (if active = true then
        (⟨a.constant - b.constant, fun j => a.coefficient j - b.coefficient j⟩ :
          RationalAffine 3) else ⟨0, fun _ => 0⟩).evalReal x ↔
        (active = true -> b.evalReal x ≤ a.evalReal x) := by
    cases active
    · simp [RationalAffine.evalReal]
    · simp [hsub]
  simp [i6D1005ChamberWalls, hrow, hsub, sub_nonneg, Fin.forall_fin_succ, and_assoc]

theorem i6D1005Chamber_measurable (label : i6D691Label) (l h : Fin 7) :
    MeasurableSet (i6D1005Chamber label l h) := by
  have hwall (j : Fin 16) :
      MeasurableSet {x | 0 ≤ (i6D1005ChamberWalls label l h j).evalReal x} := by
    apply measurableSet_le measurable_const
    apply Continuous.measurable
    unfold RationalAffine.evalReal
    fun_prop
  have hwalls : MeasurableSet {x | ∀ j, 0 ≤ (i6D1005ChamberWalls label l h j).evalReal x} := by
    convert MeasurableSet.iInter hwall using 1
    ext x
    simp
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (i6D999OrderedPairRoot.region_measurable_D924.inter hwalls))

end PrimesRestrictedDigits
