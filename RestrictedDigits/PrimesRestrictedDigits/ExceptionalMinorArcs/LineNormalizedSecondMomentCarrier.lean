import PrimesRestrictedDigits.ExceptionalMinorArcs.LineNormalizedSecondMomentData
import Mathlib.Data.Finset.Card

/-!
# Finite normalized second-moment classes

This realizes the corrected `N_3` carrier following `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp.
210--212, as an injective image of the exact witness classes. Symmetry is an explicit
two-orientation cover.
-/

namespace PrimesRestrictedDigits

/-- The normalized tuple image of one primitive-height witness class. -/
noncomputable def lineNormalizedSecondMomentClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    Finset (LineNormalizedSecondMomentData (10 ^ length)) :=
  (linePrimitiveHeightWitnessClass length C D V j).image
    lineNormalizedSecondMomentDataOfPair

@[simp]
theorem mem_lineNormalizedSecondMomentClass
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)} :
    data ∈ lineNormalizedSecondMomentClass length C D V j ↔
      Exists fun pair => And
        (pair ∈ linePrimitiveHeightWitnessClass length C D V j)
        (lineNormalizedSecondMomentDataOfPair pair = data) := by
  classical
  rw [lineNormalizedSecondMomentClass, Finset.mem_image]

theorem card_lineNormalizedSecondMomentClass
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    (lineNormalizedSecondMomentClass length C D V j).card =
      (linePrimitiveHeightWitnessClass length C D V j).card := by
  classical
  exact Finset.card_image_of_injOn
    lineNormalizedSecondMomentDataOfPair_injOn_heightClass

/-- A normalized image member satisfies every corrected source condition. -/
theorem lineNormalizedSecondMomentDataOfPair_isValid
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)}
    (hpair : pair ∈ linePrimitiveHeightWitnessClass length C D V j) :
    (lineNormalizedSecondMomentDataOfPair pair).IsValid C D V := by
  have hp := mem_linePrimitiveHeightWitnessClass.mp hpair
  have hpairData := mem_lineSecondMomentWitnessPairs.mp hp.1
  have hw := mem_positiveAllNonzeroPlaneWitnesses.mp hpairData.1
  have hw' := mem_positiveAllNonzeroPlaneWitnesses.mp hpairData.2.1
  have hc := mem_positivePlaneWitnessCandidates.mp hw.1
  have hc' := mem_positivePlaneWitnessCandidates.mp hw'.1
  refine
    { a2_mem := hpairData.2.2.2.1
      a2Prime_mem := hpairData.2.2.2.2
      a1_mem := hc.1
      a2_pos := hc.2.2.2.1
      a2Prime_pos := hc'.2.2.2.1
      a1_pos := hc.2.1
      d_pos := linePrimitiveFirstCoefficients_gcd_pos (hw.2.2.1 0)
      u_ne := linePrimitiveFirstCoefficients_fst_ne_zero (hw.2.2.1 0)
      uPrime_ne := linePrimitiveFirstCoefficients_snd_ne_zero (hw'.2.2.1 0)
      primitive_gcd :=
        linePrimitiveFirstCoefficients_gcd_eq_one (hw.2.2.1 0)
      canonical_gcd := ?_
      v2_ne := hw.2.2.1 1
      v3_ne := hw.2.2.1 2
      v4_ne := hw.2.2.2
      v2Prime_ne := hw'.2.2.1 1
      v3Prime_ne := hw'.2.2.1 2
      v4Prime_ne := hw'.2.2.2
      u_abs_le := ?_
      uPrime_abs_le := ?_
      first_abs_le := ?_
      firstPrime_abs_le := ?_
      v2_abs_le := hw.2.1.2.1 1
      v3_abs_le := hw.2.1.2.1 2
      v4_abs_le := hw.2.1.2.2.1
      v2Prime_abs_le := hw'.2.1.2.1 1
      v3Prime_abs_le := hw'.2.1.2.1 2
      v4Prime_abs_le := hw'.2.1.2.2.1
      relation := ?_
      relationPrime := ?_ }
  · dsimp only [lineNormalizedSecondMomentDataOfPair]
    rw [gcd_mul_linePrimitiveFirstCoefficients_fst,
      gcd_mul_linePrimitiveFirstCoefficients_snd]
  · exact (linePrimitiveFirstCoefficients_fst_abs_le_height
      (pair.1.v 0) (pair.2.v 0)).trans
        (lineSecondMomentPrimitiveHeight_real_le hp.1)
  · exact (linePrimitiveFirstCoefficients_snd_abs_le_height
      (pair.1.v 0) (pair.2.v 0)).trans
        (lineSecondMomentPrimitiveHeight_real_le hp.1)
  · dsimp only [lineNormalizedSecondMomentDataOfPair]
    rw [gcd_mul_linePrimitiveFirstCoefficients_fst]
    exact hw.2.1.2.1 0
  · dsimp only [lineNormalizedSecondMomentDataOfPair]
    rw [gcd_mul_linePrimitiveFirstCoefficients_snd]
    exact hw'.2.1.2.1 0
  · dsimp only [lineNormalizedSecondMomentDataOfPair]
    rw [gcd_mul_linePrimitiveFirstCoefficients_fst]
    exact LowHeightPlaneWitness.relation_eq hw.2.1
  · have hrelation := LowHeightPlaneWitness.relation_eq hw'.2.1
    rw [← hpairData.2.2.1] at hrelation
    dsimp only [lineNormalizedSecondMomentDataOfPair]
    rw [gcd_mul_linePrimitiveFirstCoefficients_snd]
    exact hrelation

theorem mem_lineNormalizedSecondMomentClass_isValid
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)}
    (hdata : data ∈ lineNormalizedSecondMomentClass length C D V j) :
    data.IsValid C D V := by
  obtain ⟨pair, hpair, rfl⟩ := mem_lineNormalizedSecondMomentClass.mp hdata
  exact lineNormalizedSecondMomentDataOfPair_isValid hpair

theorem mem_lineNormalizedSecondMomentClass_clog
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)}
    (hdata : data ∈ lineNormalizedSecondMomentClass length C D V j) :
    Nat.clog 10 data.primitiveHeight = j.val := by
  obtain ⟨pair, hpair, rfl⟩ := mem_lineNormalizedSecondMomentClass.mp hdata
  exact (mem_linePrimitiveHeightWitnessClass.mp hpair).2

theorem mem_lineNormalizedSecondMomentClass_band
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)}
    (hdata : data ∈ lineNormalizedSecondMomentClass length C D V j) :
    And (((10 ^ j.val : Nat) : Real) / 10 <
        (data.primitiveHeight : Real))
      (And ((data.primitiveHeight : Real) ≤
          ((10 ^ j.val : Nat) : Real))
        (10 ^ j.val ≤ 10 ^ length)) := by
  obtain ⟨pair, hpair, rfl⟩ := mem_lineNormalizedSecondMomentClass.mp hdata
  exact mem_linePrimitiveHeightWitnessClass_band hpair

theorem mem_lineNormalizedSecondMomentClass_gcd_scale_lt
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)}
    (hdata : data ∈ lineNormalizedSecondMomentClass length C D V j) :
    (data.d : Real) * ((10 ^ j.val : Nat) : Real) < 10 * V := by
  obtain ⟨pair, hpair, rfl⟩ := mem_lineNormalizedSecondMomentClass.mp hdata
  exact mem_linePrimitiveHeightWitnessClass_gcd_scale_lt hpair

theorem lineNormalizedSecondMomentClass_swap_mem
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)}
    (hdata : data ∈ lineNormalizedSecondMomentClass length C D V j) :
    data.swap ∈ lineNormalizedSecondMomentClass length C D V j := by
  obtain ⟨pair, hpair, rfl⟩ := mem_lineNormalizedSecondMomentClass.mp hdata
  apply mem_lineNormalizedSecondMomentClass.mpr
  refine ⟨pair.swap, linePrimitiveHeightWitnessClass_swap_mem hpair, ?_⟩
  exact lineNormalizedSecondMomentDataOfPair_swap pair
    (mem_lineSecondMomentWitnessPairs.mp
      (mem_linePrimitiveHeightWitnessClass.mp hpair).1).2.2.1

theorem swap_mem_lineNormalizedSecondMomentClass_iff
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)} :
    data.swap ∈ lineNormalizedSecondMomentClass length C D V j ↔
      data ∈ lineNormalizedSecondMomentClass length C D V j := by
  constructor
  · intro hdata
    have := lineNormalizedSecondMomentClass_swap_mem hdata
    simpa using this
  · exact lineNormalizedSecondMomentClass_swap_mem

/-- The source orientation `|u| >= |u'|`, with equality retained. -/
noncomputable def orientedLineNormalizedSecondMomentClass
    (length : Nat) (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    Finset (LineNormalizedSecondMomentData (10 ^ length)) :=
  (lineNormalizedSecondMomentClass length C D V j).filter fun data =>
    data.uPrime.natAbs ≤ data.u.natAbs

@[simp]
theorem mem_orientedLineNormalizedSecondMomentClass
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)} :
    data ∈ orientedLineNormalizedSecondMomentClass length C D V j ↔
      And (data ∈ lineNormalizedSecondMomentClass length C D V j)
        (data.uPrime.natAbs ≤ data.u.natAbs) := by
  classical
  simp [orientedLineNormalizedSecondMomentClass]

theorem lineNormalizedSecondMomentClass_subset_oriented_union_swap
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)} :
    lineNormalizedSecondMomentClass length C D V j ⊆
      orientedLineNormalizedSecondMomentClass length C D V j ∪
        (orientedLineNormalizedSecondMomentClass length C D V j).image
          LineNormalizedSecondMomentData.swap := by
  classical
  intro data hdata
  rcases Nat.le_total data.uPrime.natAbs data.u.natAbs with hle | hle
  · exact Finset.mem_union_left _
      (mem_orientedLineNormalizedSecondMomentClass.mpr ⟨hdata, hle⟩)
  · apply Finset.mem_union_right _
    apply Finset.mem_image.mpr
    refine ⟨data.swap, ?_, by simp⟩
    apply mem_orientedLineNormalizedSecondMomentClass.mpr
    exact ⟨lineNormalizedSecondMomentClass_swap_mem hdata, hle⟩

theorem card_lineNormalizedSecondMomentClass_le_two_mul_oriented
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) :
    (lineNormalizedSecondMomentClass length C D V j).card ≤
      2 * (orientedLineNormalizedSecondMomentClass
        length C D V j).card := by
  classical
  let oriented := orientedLineNormalizedSecondMomentClass length C D V j
  calc
    (lineNormalizedSecondMomentClass length C D V j).card ≤
        (oriented ∪ oriented.image
          LineNormalizedSecondMomentData.swap).card :=
      Finset.card_le_card
        lineNormalizedSecondMomentClass_subset_oriented_union_swap
    _ ≤ oriented.card +
        (oriented.image LineNormalizedSecondMomentData.swap).card :=
      Finset.card_union_le _ _
    _ ≤ oriented.card + oriented.card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * oriented.card := by omega

theorem card_lineSecondMomentWitnessPairs_eq_sum_normalizedClasses
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (hVX : V < ((10 ^ length : Nat) : Real)) :
    (lineSecondMomentWitnessPairs C D V).card =
      ∑ j : Fin (length + 1),
        (lineNormalizedSecondMomentClass length C D V j).card := by
  simpa only [card_lineNormalizedSecondMomentClass] using
    card_lineSecondMomentWitnessPairs_eq_sum_heightClasses C D V hVX

theorem card_lineSecondMomentWitnessPairs_le_sum_two_mul_oriented
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (hVX : V < ((10 ^ length : Nat) : Real)) :
    (lineSecondMomentWitnessPairs C D V).card ≤
      ∑ j : Fin (length + 1),
        2 * (orientedLineNormalizedSecondMomentClass
          length C D V j).card := by
  rw [card_lineSecondMomentWitnessPairs_eq_sum_normalizedClasses C D V hVX]
  apply Finset.sum_le_sum
  intro j _hj
  exact card_lineNormalizedSecondMomentClass_le_two_mul_oriented C D V j

theorem card_residualLineSecondMomentTriples_le_sum_two_mul_oriented
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (hV : 0 ≤ V) (hVX : V < ((10 ^ length : Nat) : Real)) :
    (residualLineSecondMomentTriples C D V).card ≤
      ∑ j : Fin (length + 1),
        2 * (orientedLineNormalizedSecondMomentClass
          length C D V j).card :=
  (card_residualLineSecondMomentTriples_le_witnessPairs hV).trans
    (card_lineSecondMomentWitnessPairs_le_sum_two_mul_oriented C D V hVX)

end PrimesRestrictedDigits
