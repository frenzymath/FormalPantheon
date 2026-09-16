import PrimesRestrictedDigits.LatticeEstimates.IntegralLattice
import Mathlib.Data.Pi.Interval
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

/-!
# Integer points generating the lattice branch

This is the canonical finite carrier in `MAYNARD-PRD-PUBLISHED`, Lemma 14.1, pp. 198--201.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- All integer lattice points satisfying the source norm and scalar-product
bounds. The surrounding integer cube makes the carrier finite. -/
noncomputable def latticeGeneratingIntegerPoints {X : Nat}
    (a1 a2 : Fin X) (Lambda : RankTwoIntegralLattice)
    (delta N : Real) : Finset (Fin 3 -> Int) := by
  classical
  exact (Fintype.piFinset fun _ : Fin 3 => integerCoordinateBox N).filter fun z =>
    And (intVectorToEuclidean z ∈ Lambda.carrier)
      (And (‖intVectorToEuclidean z‖ <= N)
        (|((intVectorDot z (angleCoefficientVector a1 a2) : Int) : Real)| <=
          delta * (X : Real)))

/-- Membership in the finite carrier is exactly the three source conditions. -/
@[simp] theorem mem_latticeGeneratingIntegerPoints {X : Nat}
    {a1 a2 : Fin X} {Lambda : RankTwoIntegralLattice} {delta N : Real}
    (hN : 0 <= N) {z : Fin 3 -> Int} :
    z ∈ latticeGeneratingIntegerPoints a1 a2 Lambda delta N <->
      And (intVectorToEuclidean z ∈ Lambda.carrier)
        (And (‖intVectorToEuclidean z‖ <= N)
          (|((intVectorDot z (angleCoefficientVector a1 a2) : Int) : Real)| <=
            delta * (X : Real))) := by
  classical
  rw [latticeGeneratingIntegerPoints, Finset.mem_filter]
  constructor
  · exact fun hz => hz.2
  · intro hz
    refine ⟨Fintype.mem_piFinset.mpr ?_, hz⟩
    intro i
    rw [mem_integerCoordinateBox_iff hN]
    have hi := PiLp.norm_apply_le (intVectorToEuclidean z) i
    have hiAbs : |((z i : Int) : Real)| <= ‖intVectorToEuclidean z‖ := by
      simpa [Real.norm_eq_abs] using hi
    exact hiAbs.trans hz.2.1

/-- The source carrier is not contained in any real line through the origin. -/
def LatticePointsNotContainedInLine (S : Finset (Fin 3 -> Int)) : Prop :=
  forall line : Submodule Real E, Module.finrank Real line = 1 ->
    exists z, z ∈ S ∧ intVectorToEuclidean z ∉ line

/-- Failure of line containment is equivalent to an independent pair. This
includes the empty, zero-only, singleton, and collinear boundary cases. -/
theorem latticePointsNotContainedInLine_iff_exists_linearIndependent
    (S : Finset (Fin 3 -> Int)) :
    LatticePointsNotContainedInLine S <->
      exists z, z ∈ S ∧ exists w, w ∈ S ∧
        LinearIndependent Real
          ![intVectorToEuclidean z, intVectorToEuclidean w] := by
  classical
  constructor
  · intro hnot
    by_contra hpair
    push Not at hpair
    by_cases hnonzero : exists z, z ∈ S ∧ intVectorToEuclidean z ≠ 0
    · obtain ⟨z, hz, hz0⟩ := hnonzero
      let line : Submodule Real E := Real ∙ intVectorToEuclidean z
      have hline : Module.finrank Real line = 1 :=
        finrank_span_singleton hz0
      obtain ⟨w, hw, hwLine⟩ := hnot line hline
      have hdependent : ¬LinearIndependent Real
          ![intVectorToEuclidean z, intVectorToEuclidean w] :=
        hpair z hz w hw
      rw [LinearIndependent.pair_iff' hz0] at hdependent
      push Not at hdependent
      obtain ⟨a, ha⟩ := hdependent
      apply hwLine
      change intVectorToEuclidean w ∈ Real ∙ intVectorToEuclidean z
      rw [Submodule.mem_span_singleton]
      exact ⟨a, ha⟩
    · push Not at hnonzero
      let e : E := intVectorToEuclidean ![(1 : Int), 0, 0]
      have he : e ≠ 0 := by
        intro heZero
        have hcoordinate := congrArg (fun v : E => v 0) heZero
        norm_num [e] at hcoordinate
      let line : Submodule Real E := Real ∙ e
      have hline : Module.finrank Real line = 1 :=
        finrank_span_singleton he
      obtain ⟨z, hz, hzLine⟩ := hnot line hline
      apply hzLine
      rw [hnonzero z hz]
      exact line.zero_mem
  · rintro ⟨z, hz, w, hw, hzw⟩ line hline
    by_contra hcontained
    push Not at hcontained
    let v : Fin 2 -> line :=
      ![⟨intVectorToEuclidean z, hcontained z hz⟩,
        ⟨intVectorToEuclidean w, hcontained w hw⟩]
    have hv : LinearIndependent Real v := by
      apply LinearIndependent.of_comp line.subtype
      have heq : line.subtype ∘ v =
          ![intVectorToEuclidean z, intVectorToEuclidean w] := by
        funext i
        fin_cases i <;> rfl
      rw [heq]
      exact hzw
    have hdim := hv.fintype_card_le_finrank
    rw [hline] at hdim
    norm_num at hdim

end PrimesRestrictedDigits
