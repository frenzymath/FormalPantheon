import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCoprimeLinearFibers

/-!
# Prefix images for the small primitive-height count

These seven lossless finite encodings expose, in source order, the four divisor fibers and two
coprime linear fibers used in equation `(15.4)` of `MAYNARD-PRD-PUBLISHED`.
-/

namespace PrimesRestrictedDigits

/-- Outer source key fixed before the first divisor factorization. -/
@[ext]
structure LineSmallHeightKey (X : Nat) where
  /-- Fixed primed second member. -/
  a2Prime : Fin X
  /-- Fixed primed-member cross coefficient. -/
  b2 : Int
  /-- Fixed decimal-scale cross coefficient. -/
  b3 : Int
  /-- Fixed constant cross coefficient. -/
  b4 : Int
  deriving DecidableEq

/-- Add the determined cross factor pair `(b1,a2)`. -/
@[ext]
structure LineSmallHeightCrossFactor (X : Nat)
    extends LineSmallHeightKey X where
  /-- Determined unprimed-member cross coefficient. -/
  b1 : Int
  /-- Unprimed second member paired with `b1`. -/
  a2 : Fin X
  deriving DecidableEq

/-- Add the factor pair `(u',v2)` of `b1`. -/
@[ext]
structure LineSmallHeightFirstPrimitiveFactor (X : Nat)
    extends LineSmallHeightCrossFactor X where
  /-- First factor of `b1`. -/
  uPrime : Int
  /-- Second factor of `b1`. -/
  v2 : Int
  deriving DecidableEq

/-- Add the factor pair `(u,v2')` of `-b2`. -/
@[ext]
structure LineSmallHeightSecondPrimitiveFactor (X : Nat)
    extends LineSmallHeightFirstPrimitiveFactor X where
  /-- First factor of `-b2`. -/
  u : Int
  /-- Second factor of `-b2`. -/
  v2Prime : Int
  deriving DecidableEq

/-- Add the coprime linear pair solving the `b3` equation. -/
@[ext]
structure LineSmallHeightThirdPair (X : Nat)
    extends LineSmallHeightSecondPrimitiveFactor X where
  /-- Unprimed solution coordinate in the `b3` fiber. -/
  v3 : Int
  /-- Primed solution coordinate in the `b3` fiber. -/
  v3Prime : Int
  deriving DecidableEq

/-- Add the coprime linear pair solving the `b4` equation. -/
@[ext]
structure LineSmallHeightFourthPair (X : Nat)
    extends LineSmallHeightThirdPair X where
  /-- Unprimed solution coordinate in the `b4` fiber. -/
  v4 : Int
  /-- Primed solution coordinate in the `b4` fiber. -/
  v4Prime : Int
  deriving DecidableEq

/-- Complete code after adding the final gcd/member divisor pair. -/
@[ext]
structure LineSmallHeightCode (X : Nat)
    extends LineSmallHeightFourthPair X where
  /-- Positive common gcd of the raw first coefficients. -/
  d : Nat
  /-- Common first member paired with the fixed raw coefficient. -/
  a1 : Fin X
  deriving DecidableEq

/-- Project normalized data to its outer key. -/
def lineSmallHeightKeyOfData {X : Nat}
    (data : LineNormalizedSecondMomentData X) : LineSmallHeightKey X :=
  let cross := lineNormalizedCrossData data
  { a2Prime := data.a2Prime
    b2 := cross.b2
    b3 := cross.b3
    b4 := cross.b4 }

/-- Project normalized data through the first cross factorization. -/
def lineSmallHeightCrossFactorOfData {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LineSmallHeightCrossFactor X :=
  { toLineSmallHeightKey := lineSmallHeightKeyOfData data
    b1 := (lineNormalizedCrossData data).b1
    a2 := data.a2 }

/-- Project normalized data through the first primitive factorization. -/
def lineSmallHeightFirstPrimitiveFactorOfData {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LineSmallHeightFirstPrimitiveFactor X :=
  { toLineSmallHeightCrossFactor := lineSmallHeightCrossFactorOfData data
    uPrime := data.uPrime
    v2 := data.v2 }

/-- Project normalized data through the second primitive factorization. -/
def lineSmallHeightSecondPrimitiveFactorOfData {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LineSmallHeightSecondPrimitiveFactor X :=
  { toLineSmallHeightFirstPrimitiveFactor :=
      lineSmallHeightFirstPrimitiveFactorOfData data
    u := data.u
    v2Prime := data.v2Prime }

/-- Project normalized data through the `b3` linear pair. -/
def lineSmallHeightThirdPairOfData {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LineSmallHeightThirdPair X :=
  { toLineSmallHeightSecondPrimitiveFactor :=
      lineSmallHeightSecondPrimitiveFactorOfData data
    v3 := data.v3
    v3Prime := data.v3Prime }

/-- Project normalized data through the `b4` linear pair. -/
def lineSmallHeightFourthPairOfData {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LineSmallHeightFourthPair X :=
  { toLineSmallHeightThirdPair := lineSmallHeightThirdPairOfData data
    v4 := data.v4
    v4Prime := data.v4Prime }

/-- Encode every normalized datum field in the complete prefix code. -/
def lineSmallHeightCodeOfData {X : Nat}
    (data : LineNormalizedSecondMomentData X) : LineSmallHeightCode X :=
  { toLineSmallHeightFourthPair := lineSmallHeightFourthPairOfData data
    d := data.d
    a1 := data.a1 }

/-- Forget derived cross coefficients and rebuild the exact normalized datum. -/
def LineSmallHeightCode.toData {X : Nat}
    (code : LineSmallHeightCode X) : LineNormalizedSecondMomentData X :=
  { a2 := code.a2
    a2Prime := code.a2Prime
    a1 := code.a1
    d := code.d
    u := code.u
    uPrime := code.uPrime
    v2 := code.v2
    v3 := code.v3
    v4 := code.v4
    v2Prime := code.v2Prime
    v3Prime := code.v3Prime
    v4Prime := code.v4Prime }

@[simp]
theorem LineSmallHeightCode.toData_ofData {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    (lineSmallHeightCodeOfData data).toData = data := by
  cases data
  rfl

theorem lineSmallHeightCodeOfData_injective {X : Nat} :
    Function.Injective (lineSmallHeightCodeOfData (X := X)) := by
  exact Function.LeftInverse.injective
    (LineSmallHeightCode.toData_ofData (X := X))

@[simp]
theorem lineSmallHeightCrossFactorOfData_toKey {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    (lineSmallHeightCrossFactorOfData data).toLineSmallHeightKey =
      lineSmallHeightKeyOfData data := rfl

@[simp]
theorem lineSmallHeightFirstPrimitiveFactorOfData_toCrossFactor {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LineSmallHeightFirstPrimitiveFactor.toLineSmallHeightCrossFactor
        (lineSmallHeightFirstPrimitiveFactorOfData data) =
      lineSmallHeightCrossFactorOfData data := rfl

@[simp]
theorem lineSmallHeightSecondPrimitiveFactorOfData_toFirstPrimitive
    {X : Nat} (data : LineNormalizedSecondMomentData X) :
    LineSmallHeightSecondPrimitiveFactor.toLineSmallHeightFirstPrimitiveFactor
        (lineSmallHeightSecondPrimitiveFactorOfData data) =
      lineSmallHeightFirstPrimitiveFactorOfData data := rfl

@[simp]
theorem lineSmallHeightThirdPairOfData_toSecondPrimitive {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LineSmallHeightThirdPair.toLineSmallHeightSecondPrimitiveFactor
        (lineSmallHeightThirdPairOfData data) =
      lineSmallHeightSecondPrimitiveFactorOfData data := rfl

@[simp]
theorem lineSmallHeightFourthPairOfData_toThirdPair {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    (lineSmallHeightFourthPairOfData data).toLineSmallHeightThirdPair =
      lineSmallHeightThirdPairOfData data := rfl

@[simp]
theorem lineSmallHeightCodeOfData_toFourthPair {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    (lineSmallHeightCodeOfData data).toLineSmallHeightFourthPair =
      lineSmallHeightFourthPairOfData data := rfl

/-- Outer-key image of the oriented normalized class. -/
noncomputable def lineSmallHeightKeyClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) : Finset (LineSmallHeightKey (10 ^ length)) :=
  (orientedLineNormalizedSecondMomentClass length C D V j).image
    lineSmallHeightKeyOfData

/-- First cross-factor image of the oriented normalized class. -/
noncomputable def lineSmallHeightCrossFactorClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    Finset (LineSmallHeightCrossFactor (10 ^ length)) :=
  (orientedLineNormalizedSecondMomentClass length C D V j).image
    lineSmallHeightCrossFactorOfData

/-- First primitive-factor image of the oriented normalized class. -/
noncomputable def lineSmallHeightFirstPrimitiveFactorClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    Finset (LineSmallHeightFirstPrimitiveFactor (10 ^ length)) :=
  (orientedLineNormalizedSecondMomentClass length C D V j).image
    lineSmallHeightFirstPrimitiveFactorOfData

/-- Second primitive-factor image of the oriented normalized class. -/
noncomputable def lineSmallHeightSecondPrimitiveFactorClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    Finset (LineSmallHeightSecondPrimitiveFactor (10 ^ length)) :=
  (orientedLineNormalizedSecondMomentClass length C D V j).image
    lineSmallHeightSecondPrimitiveFactorOfData

/-- Third-coefficient pair image of the oriented normalized class. -/
noncomputable def lineSmallHeightThirdPairClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    Finset (LineSmallHeightThirdPair (10 ^ length)) :=
  (orientedLineNormalizedSecondMomentClass length C D V j).image
    lineSmallHeightThirdPairOfData

/-- Fourth-coefficient pair image of the oriented normalized class. -/
noncomputable def lineSmallHeightFourthPairClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    Finset (LineSmallHeightFourthPair (10 ^ length)) :=
  (orientedLineNormalizedSecondMomentClass length C D V j).image
    lineSmallHeightFourthPairOfData

/-- Complete-code image of the oriented normalized class. -/
noncomputable def lineSmallHeightCodeClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) : Finset (LineSmallHeightCode (10 ^ length)) :=
  (orientedLineNormalizedSecondMomentClass length C D V j).image
    lineSmallHeightCodeOfData

theorem card_lineSmallHeightCodeClass
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    (lineSmallHeightCodeClass length C D V j).card =
      (orientedLineNormalizedSecondMomentClass length C D V j).card := by
  classical
  exact Finset.card_image_of_injective _
    lineSmallHeightCodeOfData_injective

end PrimesRestrictedDigits
