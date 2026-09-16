import PrimesRestrictedDigits.LatticeEstimates.GeneratingPairs
import PrimesRestrictedDigits.LatticeEstimates.PrimitiveApproximation

/-!
# Selected primitive approximations for generating pairs

This packages one nonnegative, simultaneously primitive witness for a pair in `B_1`. The
selection is later made once per pair, as required by the repaired Lemma 14.3 proof.
-/

namespace PrimesRestrictedDigits

/-- A common primitive rational approximation to two grid frequencies. -/
structure LatticePrimitiveApproximation
    {X : Nat} (a1 a2 : Fin X) (P : Real) where
  q : Nat
  b1 : Nat
  b2 : Nat
  q_pos : 0 < q
  q_le : (q : Real) <= 1000000 * (X : Real) / P
  primitive : (b1.gcd b2).Coprime q
  first_error :
    |(a1.val : Real) / (X : Real) - (b1 : Real) / (q : Real)| <=
      1000000 / (P * (q : Real))
  second_error :
    |(a2.val : Real) / (X : Real) - (b2 : Real) / (q : Real)| <=
      1000000 / (P * (q : Real))

/--
An explicit generating lattice yields a primitive natural-numerator approximation with the
same constant as.
-/
theorem exists_latticePrimitiveApproximation
    {X : Nat} (a1 a2 : Fin X) (N K delta : Real)
    (Lambda : RankTwoIntegralLattice)
    (hX : 1 <= X) (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / (X : Real) <= delta)
    (hcard : delta * K * N ^ 2 <=
      ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real))
    (hnonlinear : LatticePointsNotContainedInLine
      (latticeGeneratingIntegerPoints a1 a2 Lambda delta N)) :
    Nonempty (LatticePrimitiveApproximation a1 a2 (N * K)) := by
  obtain ⟨q, hq, hqBound, b1, b2, hb1Error, hb2Error⟩ :=
    exists_latticeSimultaneousApproximation_nonnegative
      a1 a2 N K delta Lambda hX hN hK hdelta hdeltaLower hcard hnonlinear
  obtain ⟨b1', b2', q', hq', hq'Le, hprimitive, hb1Ratio, hb2Ratio⟩ :=
    exists_primitiveSimultaneousFraction_nat b1 b2 q hq
  have hP : 0 < N * K :=
    mul_pos (Real.zero_lt_one.trans_le hN) (Real.zero_lt_one.trans_le hK)
  have hdenominator : N * K * (q' : Real) <= N * K * (q : Real) := by
    gcongr
  have herrorWeaken :
      1000000 / (N * K * (q : Real)) <=
        1000000 / (N * K * (q' : Real)) := by
    exact div_le_div_of_nonneg_left (by norm_num)
      (mul_pos hP (by exact_mod_cast hq')) hdenominator
  refine ⟨{
    q := q'
    b1 := b1'
    b2 := b2'
    q_pos := hq'
    q_le := by
      have hqReal : (q' : Real) <= q := by exact_mod_cast hq'Le
      exact hqReal.trans hqBound
    primitive := hprimitive
    first_error := ?_
    second_error := ?_ }⟩
  · rw [hb1Ratio]
    exact hb1Error.trans herrorWeaken
  · rw [hb2Ratio]
    exact hb2Error.trans herrorWeaken

/-- Membership in the finite `B_1` carrier supplies the selected primitive
approximation without retaining a lattice as downstream data. -/
theorem exists_latticePrimitiveApproximation_of_mem
    {X : Nat} {a : Fin X × Fin X} {N K delta : Real}
    (ha : a ∈ latticeGeneratingPairs N K delta)
    (hX : 1 <= X) (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / (X : Real) <= delta) :
    Nonempty (LatticePrimitiveApproximation a.1 a.2 (N * K)) := by
  obtain ⟨Lambda, hcard, hnonlinear⟩ :=
    mem_latticeGeneratingPairs_iff.mp ha
  exact exists_latticePrimitiveApproximation
    a.1 a.2 N K delta Lambda hX hN hK hdelta hdeltaLower hcard hnonlinear

/-- Swapping coordinates preserves simultaneous primitivity and every
quantitative bound. -/
def LatticePrimitiveApproximation.swap
    {X : Nat} {a1 a2 : Fin X} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) :
    LatticePrimitiveApproximation a2 a1 P where
  q := w.q
  b1 := w.b2
  b2 := w.b1
  q_pos := w.q_pos
  q_le := w.q_le
  primitive := by simpa only [Nat.gcd_comm] using w.primitive
  first_error := w.second_error
  second_error := w.first_error

end PrimesRestrictedDigits
