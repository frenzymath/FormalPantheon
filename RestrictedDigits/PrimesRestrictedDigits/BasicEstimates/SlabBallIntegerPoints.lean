import PrimesRestrictedDigits.BasicEstimates.IntegerVectors
import Mathlib.Data.Pi.Interval

/-!
# Integer points in a closed slab-ball

This gives a canonical finite carrier for the region in
`MAYNARD-PRD-PUBLISHED`, Lemma 13.2, pp. 193--195.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Integer triples whose three standard coordinates have absolute value at
most `N`. -/
def integerTripleBox (N : Real) : Finset (Fin 3 -> Int) :=
  Fintype.piFinset fun _ => integerCoordinateBox N

theorem mem_integerTripleBox_iff {N : Real} (hN : 0 <= N)
    (z : Fin 3 -> Int) :
    z ∈ integerTripleBox N ↔ ∀ i, abs (z i : Real) <= N := by
  classical
  rw [integerTripleBox, Fintype.mem_piFinset]
  apply forall_congr'
  intro i
  exact mem_integerCoordinateBox_iff hN

/-- Every integer point in the closed Euclidean ball and closed slab. -/
def integerPointsInSlabBall (t : E) (N delta : Real) :
    Finset (Fin 3 -> Int) :=
  (integerTripleBox N).filter fun z =>
    ‖intVectorToEuclidean z‖ <= N ∧
      abs (inner Real t (intVectorToEuclidean z)) <= delta

theorem mem_integerPointsInSlabBall_iff (t : E) {N delta : Real}
    (hN : 0 <= N) (z : Fin 3 -> Int) :
    z ∈ integerPointsInSlabBall t N delta ↔
      ‖intVectorToEuclidean z‖ <= N ∧
        abs (inner Real t (intVectorToEuclidean z)) <= delta := by
  classical
  rw [integerPointsInSlabBall, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨(mem_integerTripleBox_iff hN z).2 ?_, h⟩
    intro i
    have hi := PiLp.norm_apply_le (intVectorToEuclidean z) i
    rw [Real.norm_eq_abs] at hi
    exact hi.trans h.1

end PrimesRestrictedDigits
