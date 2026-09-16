import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeIndices
/-!
# High central-small continuation indices
Recurrence-native carriers and source geometry for the high central-small pair
piece. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 145--146, Eq. (6.16).
-/
namespace PrimesRestrictedDigits
noncomputable section
local instance sectionSixFirstHighCentralSmallPairMemDecidable
    (epsilon : Real) (length : Nat) (piece : SectionSixFirstPairPiece)
    (index : SectionSixFirstStrictIndex) :
    Decidable (sectionSixFirstPairMem epsilon length piece index) :=
  Classical.propDecidable _
abbrev SectionSixFirstHighCentralSmallTripleIndex :=
  Sigma fun _ : SectionSixFirstStrictIndex => Nat
noncomputable def sectionSixFirstHighCentralSmallTripleIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstHighCentralSmallTripleIndex :=
  let X : Real := ((10 ^ length : Nat) : Real)
  (sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall).sigma fun index =>
    sievePrimeInterval (sectionSixZOne epsilon X) (index.2 : Real)
@[simp] theorem mem_sectionSixFirstHighCentralSmallTripleIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstHighCentralSmallTripleIndex} :
    index ∈ sectionSixFirstHighCentralSmallTripleIndices epsilon length ↔
      index.1 ∈ sectionSixFirstPairPieceIndices epsilon length
        .highCentralSmall /\
      index.2 ∈ sievePrimeInterval
        (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
        (index.1.2 : Real) := by
  classical
  simp [sectionSixFirstHighCentralSmallTripleIndices]
def sectionSixFirstHighCentralSmallTripleProduct
    (index : SectionSixFirstHighCentralSmallTripleIndex) : Nat :=
  sectionSixFirstPairProduct index.1 * index.2
def sectionSixFirstHighCentralSmallTripleModulus
    (index : SectionSixFirstHighCentralSmallTripleIndex) : PNat :=
  sectionSixFirstPairModulus index.1 * Nat.toPNat' index.2
theorem sectionSixFirstHighCentralSmallTripleModulus_coe
    {index : SectionSixFirstHighCentralSmallTripleIndex}
    (hp : index.1.1.Prime) (hq : index.1.2.Prime)
    (hr : index.2.Prime) :
    (sectionSixFirstHighCentralSmallTripleModulus index : Nat) =
      sectionSixFirstHighCentralSmallTripleProduct index := by
  simp only [sectionSixFirstHighCentralSmallTripleModulus,
    sectionSixFirstHighCentralSmallTripleProduct, PNat.mul_coe]
  rw [sectionSixFirstPairModulus_coe hp hq, Nat.toPNat'_coe,
    if_pos hr.pos]
def sectionSixFirstHighCentralSmallTripleTerminalThreshold
    (length : Nat) (index : SectionSixFirstHighCentralSmallTripleIndex) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  Real.sqrt (X /
    (sectionSixFirstHighCentralSmallTripleProduct index : Real))
def sectionSixFirstHighCentralSmallTripleReducedThreshold
    (length : Nat) (index : SectionSixFirstHighCentralSmallTripleIndex) : Real :=
  min (index.2 : Real)
    (sectionSixFirstHighCentralSmallTripleTerminalThreshold length index)
theorem sectionSixFirstHighCentralSmall_le_tripleTerminalThreshold_iff
    {length : Nat} {index : SectionSixFirstHighCentralSmallTripleIndex}
    {s : Nat} (hp : index.1.1.Prime) (hq : index.1.2.Prime)
    (hr : index.2.Prime) (hs : s.Prime) :
    (s : Real) <=
        sectionSixFirstHighCentralSmallTripleTerminalThreshold length index ↔
      sectionSixFirstHighCentralSmallTripleProduct index * s * s <=
        10 ^ length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let d : Real :=
    (sectionSixFirstHighCentralSmallTripleProduct index : Real)
  have hdNatPos :
      0 < sectionSixFirstHighCentralSmallTripleProduct index := by
    exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hdPos : 0 < d := by
    dsimp only [d]
    exact_mod_cast hdNatPos
  have hsPos : (0 : Real) < s := by exact_mod_cast hs.pos
  unfold sectionSixFirstHighCentralSmallTripleTerminalThreshold
  change (s : Real) <= Real.sqrt (X / d) ↔ _
  rw [Real.le_sqrt' hsPos]
  constructor
  · intro h
    have hreal : d * (s : Real) * (s : Real) <= X := by
      apply (le_div_iff₀ hdPos).1 at h
      nlinarith
    dsimp only [d, X] at hreal
    exact_mod_cast hreal
  · intro h
    apply (le_div_iff₀ hdPos).2
    have hreal :
        (((sectionSixFirstHighCentralSmallTripleProduct index * s * s : Nat) :
          Real)) <= ((10 ^ length : Nat) : Real) := by
      exact_mod_cast h
    norm_num only [Nat.cast_mul] at hreal
    dsimp only [d, X]
    nlinarith
abbrev SectionSixFirstHighCentralSmallQuadrupleIndex :=
  Sigma fun _ : SectionSixFirstHighCentralSmallTripleIndex => Nat
noncomputable def sectionSixFirstHighCentralSmallQuadrupleIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstHighCentralSmallQuadrupleIndex :=
  let X : Real := ((10 ^ length : Nat) : Real)
  (sectionSixFirstHighCentralSmallTripleIndices epsilon length).sigma
    fun index => sievePrimeInterval
      (sectionSixZOne epsilon X) (index.2 : Real)
@[simp] theorem mem_sectionSixFirstHighCentralSmallQuadrupleIndices
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstHighCentralSmallQuadrupleIndex} :
    index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices epsilon length ↔
      index.1 ∈ sectionSixFirstHighCentralSmallTripleIndices epsilon length /\
      index.2 ∈ sievePrimeInterval
        (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
        (index.1.2 : Real) := by
  classical
  simp [sectionSixFirstHighCentralSmallQuadrupleIndices]
private theorem sectionSixFirstHighCentralSmall_zSix_lt_zThree_mul_zTwo
    {epsilon X : Real} (hepsilon : 0 < epsilon) (hX : 1 < X) :
    sectionSixZSix epsilon X <
      sectionSixZThree epsilon X * sectionSixZTwo epsilon X := by
  rw [sectionSixZSix, sectionSixZThree, sectionSixZTwo,
    ← Real.rpow_add (zero_lt_one.trans hX)]
  apply Real.rpow_lt_rpow_of_exponent_lt hX
  simp only [sectionSixThetaOne, sectionSixThetaTwo]
  linarith
private theorem sectionSixFirstHighCentralSmall_zSix_mul_zTwo
    {epsilon X : Real} (hX : 0 < X) :
    sectionSixZSix epsilon X * sectionSixZTwo epsilon X = X := by
  rw [sectionSixZSix, sectionSixZTwo, ← Real.rpow_add hX]
  have hexponent :
      (1 - sectionSixThetaOne epsilon) + sectionSixThetaOne epsilon = 1 := by
    ring
  rw [hexponent, Real.rpow_one]
private theorem sectionSixFirstHighCentralSmall_pairData
    {epsilon : Real} {length : Nat} {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall) :
    index ∈ sectionSixFirstHighStrictIndices epsilon length /\
      sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
        (sectionSixFirstPairProduct index : Real) /\
      (sectionSixFirstPairProduct index : Real) <
        sectionSixZFive epsilon ((10 ^ length : Nat) : Real) /\
      (sectionSixFirstPairSquareProduct index : Real) <
        sectionSixZSix epsilon ((10 ^ length : Nat) : Real) := by
  have hpiece := (Finset.mem_filter.mp hindex).2
  simpa only [sectionSixFirstPairMem] using hpiece
private theorem sectionSixFirstHighCentralSmall_lt_sqrt_div
    {X d r : Nat} (hd : 0 < d) (hcap : d * r * r < X) :
    (r : Real) < Real.sqrt ((X : Real) / (d : Real)) := by
  apply Real.lt_sqrt_of_sq_lt
  apply (lt_div_iff₀ (by exact_mod_cast hd)).2
  have hcapReal : (((d * r * r : Nat) : Real)) < (X : Real) := by
    exact_mod_cast hcap
  simpa only [Nat.cast_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]
    using hcapReal
theorem sectionSixFirstHighCentralSmall_qSquare_lt_zTwo
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall) :
    ((index.2 * index.2 : Nat) : Real) <
      sectionSixZTwo epsilon ((10 ^ length : Nat) : Real) := by
  have _hepsilonSmall : epsilon <= 1 / 64 := hepsilonSmall
  let X : Real := ((10 ^ length : Nat) : Real)
  let p : Nat := index.1
  let q : Nat := index.2
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hpiece := sectionSixFirstHighCentralSmall_pairData hindex
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hpData := mem_sievePrimeInterval.mp hpqData.1
  have hpLower : sectionSixZThree epsilon X < (p : Real) := by
    simpa only [X, p] using hpData.2.1
  have hsquare :
      (p : Real) * ((q * q : Nat) : Real) <
        sectionSixZSix epsilon X := by
    simpa [sectionSixFirstPairSquareProduct, X, p, q, Nat.cast_mul,
      Nat.mul_assoc] using hpiece.2.2.2
  have hzTwoPos : 0 < sectionSixZTwo epsilon X :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hX) _
  have hpPos : (0 : Real) < p := by exact_mod_cast hpData.1.pos
  have hmul :
      (p : Real) * ((q * q : Nat) : Real) <
        (p : Real) * sectionSixZTwo epsilon X := by
    calc
      _ < sectionSixZSix epsilon X := hsquare
      _ < sectionSixZThree epsilon X * sectionSixZTwo epsilon X :=
        sectionSixFirstHighCentralSmall_zSix_lt_zThree_mul_zTwo
          hepsilon hX
      _ < (p : Real) * sectionSixZTwo epsilon X :=
        mul_lt_mul_of_pos_right hpLower hzTwoPos
  have hresult :
      ((q * q : Nat) : Real) < sectionSixZTwo epsilon X :=
    lt_of_mul_lt_mul_left hmul hpPos.le
  simpa only [X, q] using hresult
private theorem sectionSixFirstHighCentralSmall_pairFourthPower_lt
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall) :
    sectionSixFirstPairSquareProduct index * index.2 * index.2 <
      10 ^ length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by
    dsimp only [X]
    positivity
  have hsquare :=
    (sectionSixFirstHighCentralSmall_pairData hindex).2.2.2
  have hqSquare := sectionSixFirstHighCentralSmall_qSquare_lt_zTwo
    hepsilon hepsilonSmall hlength hindex
  have hhigh := (sectionSixFirstHighCentralSmall_pairData hindex).1
  have hqPrime := (mem_sievePrimeInterval.mp
    (mem_sectionSixFirstSecondRepeatedIndices.mp hhigh).2).1
  have hqSquarePos : (0 : Real) < ((index.2 * index.2 : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos hqPrime.pos hqPrime.pos
  have hzSixNonneg : 0 <= sectionSixZSix epsilon X :=
    (Real.rpow_pos_of_pos hX _).le
  have hreal :
      (sectionSixFirstPairSquareProduct index : Real) *
          ((index.2 * index.2 : Nat) : Real) <
        sectionSixZSix epsilon X * sectionSixZTwo epsilon X := by
    apply mul_lt_mul
    · simpa only [X] using hsquare
    · exact (by simpa only [X] using hqSquare.le)
    · exact hqSquarePos
    · exact hzSixNonneg
  rw [sectionSixFirstHighCentralSmall_zSix_mul_zTwo hX] at hreal
  have hcast :
      (((sectionSixFirstPairSquareProduct index * index.2 * index.2 : Nat) :
        Real)) < X := by
    simpa only [Nat.cast_mul, mul_assoc] using hreal
  dsimp only [X] at hcast
  exact_mod_cast hcast
private theorem sectionSixFirstHighCentralSmall_pairCube_lt
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall) :
    sectionSixFirstPairProduct index * index.2 * index.2 < 10 ^ length := by
  have hhigh := (sectionSixFirstHighCentralSmall_pairData hindex).1
  have hqPrime := (mem_sievePrimeInterval.mp
    (mem_sectionSixFirstSecondRepeatedIndices.mp hhigh).2).1
  have hqLeSquare : index.2 <= index.2 * index.2 := by
    simpa only [mul_one] using
      Nat.mul_le_mul_left index.2 hqPrime.one_le
  calc
    sectionSixFirstPairProduct index * index.2 * index.2 =
        sectionSixFirstPairSquareProduct index * index.2 := by
      simp [sectionSixFirstPairProduct, sectionSixFirstPairSquareProduct,
        Nat.mul_assoc]
    _ <= sectionSixFirstPairSquareProduct index * (index.2 * index.2) :=
      Nat.mul_le_mul_left _ hqLeSquare
    _ = sectionSixFirstPairSquareProduct index * index.2 * index.2 := by
      simp only [Nat.mul_assoc]
    _ < 10 ^ length :=
      sectionSixFirstHighCentralSmall_pairFourthPower_lt
        hepsilon hepsilonSmall hlength hindex
theorem sectionSixFirstHighCentralSmall_q_lt_pairTerminalThreshold
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall) :
    (index.2 : Real) < sectionSixFirstPairTerminalThreshold length index := by
  have hhigh := (sectionSixFirstHighCentralSmall_pairData hindex).1
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hhigh
  have hp := (mem_sievePrimeInterval.mp hpqData.1).1
  have hq := (mem_sievePrimeInterval.mp hpqData.2).1
  have hcap := sectionSixFirstHighCentralSmall_pairCube_lt
    hepsilon hepsilonSmall hlength hindex
  unfold sectionSixFirstPairTerminalThreshold
  exact sectionSixFirstHighCentralSmall_lt_sqrt_div
    (Nat.mul_pos hp.pos hq.pos) hcap
theorem sectionSixFirstHighCentralSmall_pairReducedThreshold_eq
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall) :
    sectionSixFirstPairReducedThreshold length index = (index.2 : Real) := by
  unfold sectionSixFirstPairReducedThreshold
  rw [min_eq_left]
  exact (sectionSixFirstHighCentralSmall_q_lt_pairTerminalThreshold
    hepsilon hepsilonSmall hlength hindex).le
theorem sectionSixFirstHighCentralSmall_r_lt_tripleTerminalThreshold
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstHighCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstHighCentralSmallTripleIndices
      epsilon length) :
    (index.2 : Real) <
      sectionSixFirstHighCentralSmallTripleTerminalThreshold length index := by
  have hdata := mem_sectionSixFirstHighCentralSmallTripleIndices.mp hindex
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp
    (sectionSixFirstHighCentralSmall_pairData hdata.1).1
  have hp := (mem_sievePrimeInterval.mp hpqData.1).1
  have hq := (mem_sievePrimeInterval.mp hpqData.2).1
  have hrData := mem_sievePrimeInterval.mp hdata.2
  have hr := hrData.1
  have hrq : index.2 <= index.1.2 := by exact_mod_cast hrData.2.2
  have hcap :
      sectionSixFirstHighCentralSmallTripleProduct index * index.2 * index.2 <
        10 ^ length := by
    calc
      _ <= sectionSixFirstPairSquareProduct index.1 * index.1.2 *
          index.1.2 := by
        simp only [sectionSixFirstHighCentralSmallTripleProduct,
          sectionSixFirstPairSquareProduct, sectionSixFirstPairProduct]
        gcongr
      _ < 10 ^ length :=
        sectionSixFirstHighCentralSmall_pairFourthPower_lt
          hepsilon hepsilonSmall hlength hdata.1
  have hle :=
    sectionSixFirstHighCentralSmall_lt_sqrt_div
      (Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos) hcap
  unfold sectionSixFirstHighCentralSmallTripleTerminalThreshold
  exact hle
theorem sectionSixFirstHighCentralSmall_tripleReducedThreshold_eq
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstHighCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstHighCentralSmallTripleIndices
      epsilon length) :
    sectionSixFirstHighCentralSmallTripleReducedThreshold length index =
      (index.2 : Real) := by
  unfold sectionSixFirstHighCentralSmallTripleReducedThreshold
  rw [min_eq_left]
  exact (sectionSixFirstHighCentralSmall_r_lt_tripleTerminalThreshold
    hepsilon hepsilonSmall hlength hindex).le
theorem sectionSixFirstHighCentralSmall_tripleProduct_lt_zSix
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstHighCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstHighCentralSmallTripleIndices
      epsilon length) :
    (sectionSixFirstHighCentralSmallTripleProduct index : Real) <
      sectionSixZSix epsilon ((10 ^ length : Nat) : Real) := by
  have hdata := mem_sectionSixFirstHighCentralSmallTripleIndices.mp hindex
  have _hqSquare := sectionSixFirstHighCentralSmall_qSquare_lt_zTwo
    hepsilon hepsilonSmall hlength hdata.1
  have hrq : index.2 <= index.1.2 := by
    exact_mod_cast (mem_sievePrimeInterval.mp hdata.2).2.2
  have hle : sectionSixFirstHighCentralSmallTripleProduct index <=
      sectionSixFirstPairSquareProduct index.1 := by
    simp only [sectionSixFirstHighCentralSmallTripleProduct,
      sectionSixFirstPairSquareProduct]
    exact Nat.mul_le_mul_left _ hrq
  have hleReal : (sectionSixFirstHighCentralSmallTripleProduct index : Real) <=
      (sectionSixFirstPairSquareProduct index.1 : Real) := by
    exact_mod_cast hle
  exact hleReal.trans_lt
    (sectionSixFirstHighCentralSmall_pairData hdata.1).2.2.2
theorem sectionSixFirstHighCentralSmall_quadruple_order_and_caps
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstHighCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices
      epsilon length) :
    let p := index.1.1.1
    let q := index.1.1.2
    let r := index.1.2
    let s := index.2
    s <= r /\ r <= q /\ q < p /\
      p * q * r * r < 10 ^ length /\
      p * q * r * s * s < 10 ^ length := by
  dsimp only
  have hquad := mem_sectionSixFirstHighCentralSmallQuadrupleIndices.mp hindex
  have htriple := mem_sectionSixFirstHighCentralSmallTripleIndices.mp hquad.1
  have hsData := mem_sievePrimeInterval.mp hquad.2
  have hrData := mem_sievePrimeInterval.mp htriple.2
  have hpairData := sectionSixFirstHighCentralSmall_pairData htriple.1
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpairData.1
  have hpData := mem_sievePrimeInterval.mp hpqData.1
  have hqData := mem_sievePrimeInterval.mp hpqData.2
  have hsr : index.2 <= index.1.2 := by exact_mod_cast hsData.2.2
  have hrq : index.1.2 <= index.1.1.2 := by
    exact_mod_cast hrData.2.2
  have hsq : index.2 <= index.1.1.2 := hsr.trans hrq
  have hqSquare := sectionSixFirstHighCentralSmall_qSquare_lt_zTwo
    hepsilon hepsilonSmall hlength htriple.1
  have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hzTwoThree :=
    (sectionSix_cutoffs_strict hepsilon hepsilonSmall hX).2.1
  have hqSqNat : index.1.1.2 < index.1.1.1 := by
    have hqLeSq : (index.1.1.2 : Real) <=
        ((index.1.1.2 * index.1.1.2 : Nat) : Real) := by
      exact_mod_cast (by
        simpa only [mul_one] using
          Nat.mul_le_mul_left index.1.1.2 hqData.1.one_le)
    have hpLower := hpData.2.1
    exact_mod_cast hqLeSq.trans_lt (hqSquare.trans hzTwoThree |>.trans hpLower)
  have hfirstCap :
      index.1.1.1 * index.1.1.2 * index.1.2 * index.1.2 <
        10 ^ length := by
    calc
      _ <= sectionSixFirstPairProduct index.1.1 * index.1.1.2 *
          index.1.1.2 := by
        simp only [sectionSixFirstPairProduct]
        gcongr
      _ < 10 ^ length := sectionSixFirstHighCentralSmall_pairCube_lt
        hepsilon hepsilonSmall hlength htriple.1
  have hsecondCap :
      index.1.1.1 * index.1.1.2 * index.1.2 * index.2 * index.2 <
        10 ^ length := by
    calc
      _ <= sectionSixFirstPairSquareProduct index.1.1 * index.1.1.2 *
          index.1.1.2 := by
        simp only [sectionSixFirstPairSquareProduct]
        gcongr
      _ < 10 ^ length :=
        sectionSixFirstHighCentralSmall_pairFourthPower_lt
          hepsilon hepsilonSmall hlength htriple.1
  exact /- order followed by the two automatic source caps -/
    ⟨hsr, hrq, hqSqNat, hfirstCap, hsecondCap⟩
theorem sectionSixFirstHighCentralSmall_quadruple_pairProduct_ranges
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstHighCentralSmallQuadrupleIndex}
    (hindex : index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices
      epsilon length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let p := index.1.1.1
    let q := index.1.1.2
    let r := index.1.2
    let s := index.2
    sectionSixZThree epsilon X < ((p*q : Nat) : Real) /\
    ((p*q : Nat) : Real) < sectionSixZFive epsilon X /\
    sectionSixZThree epsilon X < ((p*r : Nat) : Real) /\
    ((p*r : Nat) : Real) < sectionSixZFive epsilon X /\
    sectionSixZThree epsilon X < ((p*s : Nat) : Real) /\
    ((p*s : Nat) : Real) < sectionSixZFive epsilon X /\
    ((q*r : Nat) : Real) < sectionSixZTwo epsilon X /\
    ((q*s : Nat) : Real) < sectionSixZTwo epsilon X /\
    ((r*s : Nat) : Real) < sectionSixZTwo epsilon X := by
  dsimp only
  have hquad := mem_sectionSixFirstHighCentralSmallQuadrupleIndices.mp hindex
  have htriple := mem_sectionSixFirstHighCentralSmallTripleIndices.mp hquad.1
  have hsData := mem_sievePrimeInterval.mp hquad.2
  have hrData := mem_sievePrimeInterval.mp htriple.2
  have hpairData := sectionSixFirstHighCentralSmall_pairData htriple.1
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpairData.1
  have hpData := mem_sievePrimeInterval.mp hpqData.1
  have hsr : index.2 <= index.1.2 := by exact_mod_cast hsData.2.2
  have hrq : index.1.2 <= index.1.1.2 := by
    exact_mod_cast hrData.2.2
  have hrOne : 1 <= index.1.2 := hrData.1.one_le
  have hsOne : 1 <= index.2 := hsData.1.one_le
  have hqSquare := sectionSixFirstHighCentralSmall_qSquare_lt_zTwo
    hepsilon hepsilonSmall hlength htriple.1
  have hprLower :
      sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
        ((index.1.1.1 * index.1.2 : Nat) : Real) := by
    have hpLe : index.1.1.1 <= index.1.1.1 * index.1.2 := by
      simpa only [mul_one] using Nat.mul_le_mul_left index.1.1.1 hrOne
    exact hpData.2.1.trans_le (Nat.cast_le.2 hpLe)
  have hpsLower :
      sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
        ((index.1.1.1 * index.2 : Nat) : Real) := by
    have hpLe : index.1.1.1 <= index.1.1.1 * index.2 := by
      simpa only [mul_one] using Nat.mul_le_mul_left index.1.1.1 hsOne
    exact hpData.2.1.trans_le (Nat.cast_le.2 hpLe)
  have hprUpperNat : index.1.1.1 * index.1.2 <=
      sectionSixFirstPairProduct index.1.1 := by
    simp only [sectionSixFirstPairProduct]
    exact Nat.mul_le_mul_left _ hrq
  have hpsUpperNat : index.1.1.1 * index.2 <=
      sectionSixFirstPairProduct index.1.1 := by
    simp only [sectionSixFirstPairProduct]
    exact Nat.mul_le_mul_left _ (hsr.trans hrq)
  have hqrNat : index.1.1.2 * index.1.2 <=
      index.1.1.2 * index.1.1.2 := Nat.mul_le_mul_left _ hrq
  have hqsNat : index.1.1.2 * index.2 <=
      index.1.1.2 * index.1.1.2 :=
    Nat.mul_le_mul_left _ (hsr.trans hrq)
  have hrsNat : index.1.2 * index.2 <=
      index.1.1.2 * index.1.1.2 := by
    exact Nat.mul_le_mul (hrq) (hsr.trans hrq)
  exact ⟨hpairData.2.1, hpairData.2.2.1, hprLower,
    (Nat.cast_le.2 hprUpperNat).trans_lt hpairData.2.2.1, hpsLower,
    (Nat.cast_le.2 hpsUpperNat).trans_lt hpairData.2.2.1,
    (Nat.cast_le.2 hqrNat).trans_lt hqSquare,
    (Nat.cast_le.2 hqsNat).trans_lt hqSquare,
    (Nat.cast_le.2 hrsNat).trans_lt hqSquare⟩
end
end PrimesRestrictedDigits
