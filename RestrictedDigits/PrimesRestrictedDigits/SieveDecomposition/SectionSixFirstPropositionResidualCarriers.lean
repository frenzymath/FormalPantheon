import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOne
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwo
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixOneCoordinateRegions
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLedger
import Mathlib.Tactic.Linarith

/-!
# Finite carriers for the first Section 6 proposition residual

This file identifies the first four terms in the corrected Eq. (6.5) ledger with five
Proposition 6.1 sums and one Proposition 6.2 sum. All endpoint subtractions are exact finite
identities.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The signed group removed directly by Propositions 6.1 and 6.2. -/
def sectionSixFirstPropositionResidual
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  sectionSixSiftedSum digit length 1 z1 -
      sectionSixFirstOuterStrictSum digit length z2 z3 -
      sectionSixFirstOuterBaseSum digit length z1 z1 z2 -
      sectionSixFirstOuterBaseSum digit length z1 z3 z4

/-- Proposition 6.1 sums respect an exact set difference whenever the second
region is contained in the first. -/
theorem propositionSixOneSum_sdiff
    (epsilon : Real) (ell : Nat)
    {region subregion : Set (Fin ell -> Real)}
    (hsub : subregion ⊆ region)
    (digit : Fin 10) (length : Nat) :
    propositionSixOneSum epsilon ell (region \ subregion) digit length =
      propositionSixOneSum epsilon ell region digit length -
        propositionSixOneSum epsilon ell subregion digit length := by
  classical
  let carrier := propositionSixOnePrimeTuples epsilon ell region length
  let subcarrier := propositionSixOnePrimeTuples epsilon ell subregion length
  have hsubset : subcarrier ⊆ carrier := by
    intro p hp
    rw [mem_propositionSixOnePrimeTuples] at hp ⊢
    refine ⟨hp.1, ?_⟩
    dsimp [IsPropositionSixOnePrimeTuple] at hp ⊢
    exact ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
      hsub hp.2.2.2.2.2⟩
  have hcarrier :
      propositionSixOnePrimeTuples epsilon ell (region \ subregion) length =
        carrier \ subcarrier := by
    ext p
    dsimp only [carrier, subcarrier]
    simp only [Finset.mem_sdiff, mem_propositionSixOnePrimeTuples]
    dsimp [IsPropositionSixOnePrimeTuple]
    constructor
    · rintro ⟨hpBound, hpPrime, hpMono, hpLower, hpProduct,
          hpRegion, hpNotSubregion⟩
      refine ⟨⟨hpBound, hpPrime, hpMono, hpLower, hpProduct, hpRegion⟩, ?_⟩
      rintro ⟨_, _, _, _, _, hpSubregion⟩
      exact hpNotSubregion hpSubregion
    · rintro ⟨⟨hpBound, hpPrime, hpMono, hpLower, hpProduct, hpRegion⟩,
          hpNotSubcarrier⟩
      refine ⟨hpBound, hpPrime, hpMono, hpLower, hpProduct, hpRegion, ?_⟩
      intro hpSubregion
      exact hpNotSubcarrier
        ⟨hpBound, hpPrime, hpMono, hpLower, hpProduct, hpSubregion⟩
  unfold propositionSixOneSum
  dsimp only
  rw [hcarrier]
  let term : (Fin ell -> Nat) -> Real := fun p =>
    sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
      (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)
  have hsum :
      (∑ p ∈ carrier \ subcarrier, term p) +
          (∑ p ∈ subcarrier, term p) = ∑ p ∈ carrier, term p :=
    Finset.sum_sdiff hsubset
  dsimp only [carrier, subcarrier] at hsum ⊢
  change (∑ p ∈ propositionSixOnePrimeTuples epsilon ell region length \
        propositionSixOnePrimeTuples epsilon ell subregion length, term p) = _
  change (∑ p ∈ propositionSixOnePrimeTuples epsilon ell region length \
        propositionSixOnePrimeTuples epsilon ell subregion length, term p) +
      (∑ p ∈ propositionSixOnePrimeTuples epsilon ell subregion length,
        term p) =
      ∑ p ∈ propositionSixOnePrimeTuples epsilon ell region length, term p
    at hsum
  linarith

/-- A one-prime base sum over `(X^lower,X^upper]` is exactly the
Proposition 6.1 sum over the corresponding normalized-log interval. -/
theorem sectionSixFirstOuterBaseSum_eq_propositionSixOneSum_ioc
    (epsilon lower upper : Real) (hepsilon : 0 < epsilon)
    (hlower : sectionSixThetaGap epsilon <= lower)
    (hupper : upper <= 1 - sectionSixThetaOne epsilon)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    sectionSixFirstOuterBaseSum digit length z1
        (X ^ lower) (X ^ upper) =
      propositionSixOneSum epsilon 1
        (sectionSixOneCoordinateIocRegion lower upper) digit length := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let z1 : Real := sectionSixZOne epsilon X
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  change sectionSixFirstOuterBaseSum digit length z1
      (X ^ lower) (X ^ upper) =
    propositionSixOneSum epsilon 1
      (sectionSixOneCoordinateIocRegion lower upper) digit length
  unfold sectionSixFirstOuterBaseSum propositionSixOneSum
  dsimp only
  apply Finset.sum_bij (fun p _ => fun _ : Fin 1 => p)
  · intro p hp
    rw [mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength]
    have hpData := mem_sievePrimeInterval.mp hp
    have hpLower : X ^ sectionSixThetaGap epsilon <= (p : Real) :=
      (Real.rpow_le_rpow_of_exponent_le hX.le hlower).trans hpData.2.1.le
    have hpUpper : (p : Real) <= X ^ (1 - sectionSixThetaOne epsilon) :=
      hpData.2.2.trans
        (Real.rpow_le_rpow_of_exponent_le hX.le hupper)
    refine ⟨fun _ => hpData.1, monotone_const, fun _ => hpLower, ?_, ?_⟩
    · simpa [primeTupleProduct, X, XNat] using hpUpper
    · change normalizedPrimeLog XNat p ∈ Set.Ioc lower upper
      exact (normalizedPrimeLog_mem_Ioc_iff_rpow hXNat hpData.1 lower upper).2
        ⟨hpData.2.1, hpData.2.2⟩
  · intro p hp q hq hpq
    exact congrFun hpq 0
  · intro q hq
    rw [mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength] at hq
    dsimp [IsPropositionSixOnePrimeTuple] at hq
    let p : Nat := q 0
    have hpRange : X ^ lower < (p : Real) ∧
        (p : Real) <= X ^ upper := by
      apply (normalizedPrimeLog_mem_Ioc_iff_rpow
        hXNat (hq.1 0) lower upper).1
      exact hq.2.2.2.2
    have hp : p ∈ sievePrimeInterval (X ^ lower) (X ^ upper) :=
      mem_sievePrimeInterval.mpr ⟨hq.1 0, hpRange⟩
    refine ⟨p, hp, ?_⟩
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    rfl
  · intro p hp
    simp [primeTupleProduct, z1, X, XNat, sectionSixZOne]

/-- The arity-zero Proposition 6.1 sum is the initial `z1` sifted sum. -/
theorem sectionSixFirstSiftedZOne_eq_propositionSixOne
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixSiftedSum digit length 1
        (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) =
      propositionSixOneSum epsilon 0 Set.univ digit length := by
  simpa only [sectionSixZOne] using
    (propositionSixOneSum_zero_univ
      hepsilon hepsilonSmall digit hlength).symm

/-- The low base interval `(z1,z2]` is the difference of two cumulative
Proposition 6.1 sums. -/
theorem sectionSixFirstLowBase_eq_propositionSixOneUpper_sub
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z2 : Real := sectionSixZTwo epsilon X
    sectionSixFirstOuterBaseSum digit length z1 z1 z2 =
      propositionSixOneSum epsilon 1
          (sectionSixOneCoordinateUpperRegion
            (sectionSixThetaOne epsilon)) digit length -
        propositionSixOneSum epsilon 1
          (sectionSixOneCoordinateUpperRegion
            (sectionSixThetaGap epsilon)) digit length := by
  have hgapOne : sectionSixThetaGap epsilon <=
      sectionSixThetaOne epsilon := by
    rw [sectionSixThetaGap_eq, sectionSixThetaOne]
    linarith
  have honeHalf : sectionSixThetaOne epsilon <=
      1 - sectionSixThetaOne epsilon := by
    simp only [sectionSixThetaOne]
    linarith
  have hgeneric := sectionSixFirstOuterBaseSum_eq_propositionSixOneSum_ioc
    epsilon (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon)
      hepsilon le_rfl honeHalf digit hlength
  have hsub :
      sectionSixOneCoordinateUpperRegion (sectionSixThetaGap epsilon) ⊆
        sectionSixOneCoordinateUpperRegion
          (sectionSixThetaOne epsilon) := by
    intro x hx
    exact hx.trans hgapOne
  rw [sectionSixOneCoordinateIocRegion_eq_sdiff,
    propositionSixOneSum_sdiff epsilon 1 hsub digit length] at hgeneric
  simpa only [sectionSixZOne, sectionSixZTwo] using hgeneric

/-- The high base interval `(z3,z4]` is the difference of two cumulative
Proposition 6.1 sums. -/
theorem sectionSixFirstHighBase_eq_propositionSixOneUpper_sub
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z3 : Real := sectionSixZThree epsilon X
    let z4 : Real := sectionSixZFour X
    sectionSixFirstOuterBaseSum digit length z1 z3 z4 =
      propositionSixOneSum epsilon 1
          (sectionSixOneCoordinateUpperRegion (1 / 2)) digit length -
        propositionSixOneSum epsilon 1
          (sectionSixOneCoordinateUpperRegion
            (sectionSixThetaTwo epsilon)) digit length := by
  have hgapTwo : sectionSixThetaGap epsilon <=
      sectionSixThetaTwo epsilon := by
    rw [sectionSixThetaGap_eq, sectionSixThetaTwo]
    linarith
  have htwoHalf : sectionSixThetaTwo epsilon <= (1 / 2 : Real) := by
    simp only [sectionSixThetaTwo]
    linarith
  have hhalfUpper : (1 / 2 : Real) <=
      1 - sectionSixThetaOne epsilon := by
    simp only [sectionSixThetaOne]
    linarith
  have hgeneric := sectionSixFirstOuterBaseSum_eq_propositionSixOneSum_ioc
    epsilon (sectionSixThetaTwo epsilon) (1 / 2 : Real)
      hepsilon hgapTwo hhalfUpper digit hlength
  have hsub :
      sectionSixOneCoordinateUpperRegion (sectionSixThetaTwo epsilon) ⊆
        sectionSixOneCoordinateUpperRegion (1 / 2 : Real) := by
    intro x hx
    exact hx.trans htwoHalf
  rw [sectionSixOneCoordinateIocRegion_eq_sdiff,
    propositionSixOneSum_sdiff epsilon 1 hsub digit length] at hgeneric
  simpa only [sectionSixZOne, sectionSixZThree,
    sectionSixZFour_eq_rpow] using hgeneric

/-- The strict middle interval `(z2,z3]` is exactly Proposition 6.2's first
direct band with one strict lower wall. -/
theorem sectionSixFirstMiddleStrict_eq_propositionSixTwo
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z2 : Real := sectionSixZTwo epsilon X
    let z3 : Real := sectionSixZThree epsilon X
    sectionSixFirstOuterStrictSum digit length z2 z3 =
      propositionSixTwoBandSum epsilon 1 Finset.univ (0 : Fin 1)
        (sectionSixOneCoordinateStrictLowerRegion
          (sectionSixThetaOne epsilon)) digit length .first := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  change sectionSixFirstOuterStrictSum digit length z2 z3 =
    propositionSixTwoBandSum epsilon 1 Finset.univ (0 : Fin 1)
      (sectionSixOneCoordinateStrictLowerRegion
        (sectionSixThetaOne epsilon)) digit length .first
  unfold sectionSixFirstOuterStrictSum propositionSixTwoBandSum
  apply Finset.sum_bij (fun p _ => fun _ : Fin 1 => p)
  · intro p hp
    rw [mem_propositionSixTwoPrimeTuples_iff_source]
    have hpData := mem_sievePrimeInterval.mp hp
    have hpPos : (0 : Real) < (p : Real) := by
      exact_mod_cast hpData.1.pos
    have hpZOne : sectionSixZOne epsilon X <= (p : Real) :=
      (horder.1.trans hpData.2.1).le
    have hpZFour : (p : Real) < Real.sqrt X := by
      simpa only [sectionSixZFour] using
        hpData.2.2.trans_lt horder.2.2.1
    have hpSquareReal : (p : Real) * (p : Real) <= X := by
      have hsqrtNonneg := Real.sqrt_nonneg X
      have hXnonneg : 0 <= X := le_trans (by norm_num) hX.le
      have hsqrtSquare := Real.mul_self_sqrt hXnonneg
      nlinarith
    have hpSquareNat : p * p <= XNat := by
      change (p * p : Real) <= (XNat : Real) at hpSquareReal
      exact_mod_cast hpSquareReal
    refine ⟨fun _ => hpData.1, monotone_const, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa only [sectionSixZOne] using hpZOne
    · simpa [sectionSixDirectRangeMembership, primeTupleSubproduct,
        primeTupleProduct, z2, z3, sectionSixZTwo, sectionSixZThree, X, XNat]
        using And.intro hpData.2.1.le hpData.2.2
    · simpa [primeTupleProduct] using hpSquareNat
    · change sectionSixThetaOne epsilon < normalizedPrimeLog XNat p
      change sectionSixThetaOne epsilon < Real.logb X (p : Real)
      exact (Real.lt_logb_iff_rpow_lt hX hpPos).2
        (by simpa only [z2, sectionSixZTwo] using hpData.2.1)
  · intro p hp q hq hpq
    exact congrFun hpq 0
  · intro q hq
    rw [mem_propositionSixTwoPrimeTuples_iff_source] at hq
    dsimp [IsPropositionSixTwoPrimeTuple] at hq
    let p : Nat := q 0
    have hpPrime : p.Prime := hq.1 0
    have hpPos : (0 : Real) < (p : Real) := by
      exact_mod_cast hpPrime.pos
    have hpDirect := hq.2.2.2.1
    have hpBounds : X ^ sectionSixThetaOne epsilon <= (p : Real) ∧
        (p : Real) <= X ^ sectionSixThetaTwo epsilon := by
      simpa [sectionSixDirectRangeMembership, primeTupleSubproduct,
        primeTupleProduct, X, XNat, p] using hpDirect
    have hpStrictNormalized :
        sectionSixThetaOne epsilon < normalizedPrimeLog XNat p := by
      simpa only [sectionSixOneCoordinateStrictLowerRegion,
        Set.mem_setOf_eq, p] using
          hq.2.2.2.2.2
    have hpStrictLog :
        sectionSixThetaOne epsilon < Real.logb X (p : Real) := by
      simpa only [normalizedPrimeLog, Real.logb, X, XNat] using
        hpStrictNormalized
    have hpStrict : X ^ sectionSixThetaOne epsilon < (p : Real) :=
      (Real.lt_logb_iff_rpow_lt hX hpPos).1 hpStrictLog
    have hp : p ∈ sievePrimeInterval z2 z3 := by
      apply mem_sievePrimeInterval.mpr
      simpa only [z2, z3, sectionSixZTwo, sectionSixZThree] using
        And.intro hpPrime (And.intro hpStrict hpBounds.2)
    refine ⟨p, hp, ?_⟩
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    rfl
  · intro p hp
    have hpPrime := (mem_sievePrimeInterval.mp hp).1
    rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length 1 hpPrime]
    simp [primeTupleProduct]

/-- Exact six-term expansion of the first proposition residual. The signs
freeze both strict endpoint subtractions. -/
theorem sectionSixFirstPropositionResidual_eq_propositionSums
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstPropositionResidual epsilon digit length =
      propositionSixOneSum epsilon 0 Set.univ digit length -
      propositionSixTwoBandSum epsilon 1 Finset.univ (0 : Fin 1)
        (sectionSixOneCoordinateStrictLowerRegion
          (sectionSixThetaOne epsilon)) digit length .first -
      propositionSixOneSum epsilon 1
        (sectionSixOneCoordinateUpperRegion
          (sectionSixThetaOne epsilon)) digit length +
      propositionSixOneSum epsilon 1
        (sectionSixOneCoordinateUpperRegion
          (sectionSixThetaGap epsilon)) digit length -
      propositionSixOneSum epsilon 1
        (sectionSixOneCoordinateUpperRegion (1 / 2)) digit length +
      propositionSixOneSum epsilon 1
        (sectionSixOneCoordinateUpperRegion
          (sectionSixThetaTwo epsilon)) digit length := by
  unfold sectionSixFirstPropositionResidual
  dsimp only
  rw [sectionSixFirstSiftedZOne_eq_propositionSixOne
      hepsilon hepsilonSmall digit hlength,
    sectionSixFirstMiddleStrict_eq_propositionSixTwo
      hepsilon hepsilonSmall digit hlength,
    sectionSixFirstLowBase_eq_propositionSixOneUpper_sub
      hepsilon hepsilonSmall digit hlength,
    sectionSixFirstHighBase_eq_propositionSixOneUpper_sub
      hepsilon hepsilonSmall digit hlength]
  ring

end

end PrimesRestrictedDigits
