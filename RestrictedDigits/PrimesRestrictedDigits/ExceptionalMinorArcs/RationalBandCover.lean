import PrimesRestrictedDigits.ExceptionalMinorArcs.DirichletBandScales
import PrimesRestrictedDigits.MajorArcs.Partition

/-!
# Finite canonical rational-band cover

This replaces the overlapping phrase "divide into sets `F(Q,E)`" in the proof of published
Proposition 9.3 by a canonical finite key assignment. Each fiber is disjoint by definition,
lies in the corresponding repaired rational band, and frequencies outside the weak major arcs
satisfy the strict source scale inequality.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The canonical denominator/error index pair of a grid frequency. -/
noncomputable def exceptionalDirichletBandKey
    (X : Nat) (a : Fin X) : Nat × Nat :=
  (exceptionalDirichletDenominatorIndex X a,
    exceptionalDirichletErrorIndex X a)

/-- All canonical keys at decimal length `length`. -/
def exceptionalDirichletBandKeys (length : Nat) : Finset (Nat × Nat) :=
  (Finset.range (length + 1)).product
    (Finset.range (2 * length + 2))

/-- The canonical fiber of a frequency carrier at one rational-band key. -/
noncomputable def exceptionalDirichletBandFiber
    {X : Nat} (S : Finset (Fin X)) (key : Nat × Nat) : Finset (Fin X) :=
  S.filter fun a => exceptionalDirichletBandKey X a = key

@[simp]
theorem mem_exceptionalDirichletBandFiber_iff
    {X : Nat} {S : Finset (Fin X)} {key : Nat × Nat} {a : Fin X} :
    a ∈ exceptionalDirichletBandFiber S key ↔
      a ∈ S ∧ exceptionalDirichletBandKey X a = key := by
  simp [exceptionalDirichletBandFiber]

/-- The canonical denominator index is one of the first `length+1` decimal
indices at ambient scale `10^length`. -/
theorem exceptionalDirichletDenominatorIndex_le
    (length : Nat) (a : Fin (10 ^ length)) :
    exceptionalDirichletDenominatorIndex (10 ^ length) a <= length := by
  apply factorTenIndex_le_of_le_ten_pow
  have hspec := (exceptionalDirichletApproximation_spec
    (X := 10 ^ length) (Nat.one_le_pow length 10 (by norm_num)) a).2
  exact hspec.trans (Nat.sqrt_le_self _)

/-- The exact-zero code and all positive shifted-error codes fit in the first
`2*length+2` indices. -/
theorem exceptionalDirichletErrorIndex_lt
    {length : Nat} (_hlength : 0 < length) (a : Fin (10 ^ length)) :
    exceptionalDirichletErrorIndex (10 ^ length) a <
      2 * length + 2 := by
  by_cases herror : exceptionalDirichletError (10 ^ length) a = 0
  · simp [exceptionalDirichletErrorIndex, herror]
  · have htarget : exceptionalDirichletErrorTarget (10 ^ length) a <=
        (((10 ^ (2 * length) : Nat) : Real)) := by
      calc
        exceptionalDirichletErrorTarget (10 ^ length) a <=
            (((10 ^ length : Nat) : Real) ^ 2) :=
          exceptionalDirichletErrorTarget_le_sq
            (Nat.one_le_pow length 10 (by norm_num)) a
        _ = (((10 ^ (2 * length) : Nat) : Real)) := by
          norm_num only [Nat.cast_pow, Nat.cast_ofNat]
          rw [← pow_mul]
          congr 1
          omega
    have hexponent : latticePositiveRealFactorTenExponent
        (exceptionalDirichletErrorTarget (10 ^ length) a) <=
        2 * length :=
      latticePositiveRealFactorTenExponent_le htarget
    unfold exceptionalDirichletErrorIndex
    rw [if_neg herror]
    omega

/-- Every frequency's canonical key belongs to the finite key carrier. -/
theorem exceptionalDirichletBandKey_mem
    {length : Nat} (hlength : 0 < length)
    (a : Fin (10 ^ length)) :
    exceptionalDirichletBandKey (10 ^ length) a ∈
      exceptionalDirichletBandKeys length := by
  rw [exceptionalDirichletBandKeys]
  apply Finset.mem_product.mpr
  constructor
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le
      (exceptionalDirichletDenominatorIndex_le length a)
  · rw [Finset.mem_range]
    exact exceptionalDirichletErrorIndex_lt hlength a

/-- Exact disjoint decomposition of any frequency sum by canonical keys. -/
theorem sum_exceptionalDirichletBandFibers
    {M : Type*} [AddCommMonoid M]
    {length : Nat} (hlength : 0 < length)
    (S : Finset (Fin (10 ^ length)))
    (f : Fin (10 ^ length) -> M) :
    (∑ key ∈ exceptionalDirichletBandKeys length,
      ∑ a ∈ exceptionalDirichletBandFiber S key, f a) =
      ∑ a ∈ S, f a := by
  classical
  unfold exceptionalDirichletBandFiber
  apply Finset.sum_fiberwise_of_maps_to
  intro a ha
  exact exceptionalDirichletBandKey_mem hlength a

/-- The number of canonical rational-band keys is explicit and quadratic in
the decimal length. -/
@[simp]
theorem card_exceptionalDirichletBandKeys (length : Nat) :
    (exceptionalDirichletBandKeys length).card =
      (length + 1) * (2 * length + 2) := by
  simp [exceptionalDirichletBandKeys]

/-- A canonical fiber is contained in the rational band represented by its
key. -/
theorem mem_latticeRationalApproximationBand_of_mem_fiber
    {length : Nat} (hlength : 0 < length)
    {S : Finset (Fin (10 ^ length))} {key : Nat × Nat}
    {a : Fin (10 ^ length)}
    (ha : a ∈ exceptionalDirichletBandFiber S key) :
    a ∈ latticeRationalApproximationBand
      (exceptionalDirichletDenominatorScaleAt (10 ^ length) key.1)
      (exceptionalDirichletErrorScaleAt (10 ^ length) key.2) := by
  have hkey := (mem_exceptionalDirichletBandFiber_iff.mp ha).2
  have hden : exceptionalDirichletDenominatorIndex (10 ^ length) a =
      key.1 := by
    simpa only [exceptionalDirichletBandKey] using congrArg Prod.fst hkey
  have herror : exceptionalDirichletErrorIndex (10 ^ length) a =
      key.2 := by
    simpa only [exceptionalDirichletBandKey] using congrArg Prod.snd hkey
  rw [← hden, ← herror,
    exceptionalDirichletDenominatorScaleAt_index,
    exceptionalDirichletErrorScaleAt_index]
  exact mem_latticeRationalApproximationBand_canonical
    (show 4 <= 10 ^ length by
      have : 10 <= 10 ^ length := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 10)
            (by omega : 1 <= length))
      omega) a

/-- Membership in a repaired rational band below `Q+E` supplies a weak
major-arc witness. -/
theorem majorArcRawApproximation_of_mem_latticeBand
    {X : Nat} (hX : 0 < X) {a : Fin X} {Q E H : Real}
    (hQ : 0 <= Q) (hE : 0 <= E) (hadd : Q + E <= H)
    (ha : a ∈ latticeRationalApproximationBand Q E) :
    majorArcRawApproximation X a.val H := by
  classical
  rw [latticeRationalApproximationBand, Finset.mem_filter] at ha
  rcases ha.2 with ⟨r, hrQ, _, herror⟩
  refine ⟨r, ?_, ?_⟩
  · exact (latticeRationalErrorInBand_abs_le herror).trans
      (div_le_div_of_nonneg_right
        ((le_add_of_nonneg_left hQ).trans hadd)
        (by positivity))
  · exact hrQ.trans ((le_add_of_nonneg_right hE).trans hadd)

/-- Outside the weak major arcs, every repaired rational band satisfies the
strict lower scale inequality used for logarithmic absorption. -/
theorem majorArcCutoff_lt_add_of_mem_latticeBand
    {X : Nat} (hX : 0 < X) {a : Fin X} {Q E H : Real}
    (hQ : 0 <= Q) (hE : 0 <= E)
    (ha : a ∈ latticeRationalApproximationBand Q E)
    (hminor : a.val ∉ majorArcRawFrequencies X H) :
    H < Q + E := by
  classical
  by_contra hnot
  have hmajor := majorArcRawApproximation_of_mem_latticeBand hX hQ hE
    (le_of_not_gt hnot) ha
  apply hminor
  rw [majorArcRawFrequencies, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr a.isLt, hmajor⟩

/-- Canonical form of the strict scale inequality, before replacing scales by
their finite key representatives. -/
theorem exceptionalMajorArcCutoff_lt_add
    {X : Nat} (hX : 4 <= X) (a : Fin X) {H : Real}
    (hminor : a.val ∉ majorArcRawFrequencies X H) :
    H < exceptionalDirichletDenominatorScale X a +
      exceptionalDirichletErrorScale X a := by
  have hscales := exceptionalDirichletScales_bounds hX a
  exact majorArcCutoff_lt_add_of_mem_latticeBand (by omega)
    (by nlinarith [hscales.1]) hscales.2.2.1
    (mem_latticeRationalApproximationBand_canonical hX a) hminor

/-- Fiber-indexed form of the strict scale inequality. -/
theorem exceptionalMajorArcCutoff_lt_add_of_mem_fiber
    {length : Nat} (hlength : 0 < length)
    {S : Finset (Fin (10 ^ length))} {key : Nat × Nat}
    {a : Fin (10 ^ length)} {H : Real}
    (ha : a ∈ exceptionalDirichletBandFiber S key)
    (hminor : a.val ∉ majorArcRawFrequencies (10 ^ length) H) :
    H < exceptionalDirichletDenominatorScaleAt (10 ^ length) key.1 +
      exceptionalDirichletErrorScaleAt (10 ^ length) key.2 := by
  have hkey := (mem_exceptionalDirichletBandFiber_iff.mp ha).2
  have hden : exceptionalDirichletDenominatorIndex (10 ^ length) a =
      key.1 := by
    simpa only [exceptionalDirichletBandKey] using congrArg Prod.fst hkey
  have herror : exceptionalDirichletErrorIndex (10 ^ length) a =
      key.2 := by
    simpa only [exceptionalDirichletBandKey] using congrArg Prod.snd hkey
  rw [← hden, ← herror,
    exceptionalDirichletDenominatorScaleAt_index,
    exceptionalDirichletErrorScaleAt_index]
  exact exceptionalMajorArcCutoff_lt_add
    (show 4 <= 10 ^ length by
      have : 10 <= 10 ^ length := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 10)
            (by omega : 1 <= length))
      omega) a hminor

end

end PrimesRestrictedDigits
