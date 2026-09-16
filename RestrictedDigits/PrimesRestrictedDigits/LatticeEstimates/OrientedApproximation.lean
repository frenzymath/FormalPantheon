import PrimesRestrictedDigits.LatticeEstimates.PrimitiveGeneratingApproximation
import PrimesRestrictedDigits.LatticeEstimates.RationalFactorization

/-!
# Oriented primitive approximations

The source says "by symmetry" before assuming the first coordinate gcd is no larger. The outer
proof must keep the two orientation branches separate; this module supplies only the
branchwise data.
-/

namespace PrimesRestrictedDigits

/-- The gcd between the first numerator and common denominator. -/
def LatticePrimitiveApproximation.firstGcd
    {X : Nat} {a1 a2 : Fin X} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) : Nat :=
  w.b1.gcd w.q

/-- The gcd between the second numerator and common denominator. -/
def LatticePrimitiveApproximation.secondGcd
    {X : Nat} {a1 a2 : Fin X} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) : Nat :=
  w.b2.gcd w.q

@[simp]
theorem LatticePrimitiveApproximation.swap_firstGcd
    {X : Nat} {a1 a2 : Fin X} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) :
    w.swap.firstGcd = w.secondGcd :=
  rfl

@[simp]
theorem LatticePrimitiveApproximation.swap_secondGcd
    {X : Nat} {a1 a2 : Fin X} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) :
    w.swap.secondGcd = w.firstGcd :=
  rfl

/-- An ordered primitive approximation has the exact denominator
factorization used in Lemma 14.3. -/
theorem LatticePrimitiveApproximation.exists_factorization
    {X : Nat} {a1 a2 : Fin X} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P)
    (hordered : w.firstGcd <= w.secondGcd) :
    Nonempty
      (LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) := by
  apply exists_latticeRationalFactorization w.q_pos
  · simpa only [Int.natAbs_natCast] using w.primitive
  · simpa only [LatticePrimitiveApproximation.firstGcd,
      LatticePrimitiveApproximation.secondGcd, Int.natAbs_natCast] using hordered

/-- A chosen factorization for one ordered branch. -/
noncomputable def LatticePrimitiveApproximation.factorization
    {X : Nat} {a1 a2 : Fin X} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P)
    (hordered : w.firstGcd <= w.secondGcd) :
    LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q :=
  Classical.choice (w.exists_factorization hordered)

end PrimesRestrictedDigits
