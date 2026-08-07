import BoundedGaps.Maynard.MaynardYDiagonalBound
import BoundedGaps.Maynard.MaynardS1CrossPrime
import BoundedGaps.Maynard.MaynardYDiagonalPairExpansion

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

/-! The independent tuple support and its excluded coordinate collisions. -/

def preSievedSimplexTupleSupport
    (H : Finset ℕ) (R W : ℕ) : Finset (H → ℕ) :=
  (preSievedCommonTupleSupport H W R).filter fun u =>
    divisorTupleProduct H u < R

theorem mem_preSievedSimplexTupleSupport_iff
    {H : Finset ℕ} {R W : ℕ} {u : H → ℕ} :
    u ∈ preSievedSimplexTupleSupport H R W ↔
      u ∈ preSievedCommonTupleSupport H W R ∧
        divisorTupleProduct H u < R := by
  simp [preSievedSimplexTupleSupport]

theorem preSievedSimplexTupleSupport_coordinate
    {H : Finset ℕ} {R W : ℕ} {u : H → ℕ}
    (hu : u ∈ preSievedSimplexTupleSupport H R W) (h : H) :
    0 < u h ∧ Squarefree (u h) ∧ Nat.Coprime (u h) W := by
  have huCommon := (mem_preSievedSimplexTupleSupport_iff.mp hu).1
  have huh := Fintype.mem_piFinset.mp huCommon h
  exact (Finset.mem_filter.mp huh).2

theorem maynardDivisorTupleSupport_eq_preSievedSimplex_filter
    (H : Finset ℕ) (R W : ℕ) :
    maynardDivisorTupleSupport H R W =
      (preSievedSimplexTupleSupport H R W).filter fun u =>
        Squarefree (divisorTupleProduct H u) := by
  classical
  ext u
  rw [Finset.mem_filter]
  constructor
  · intro hu
    have huSupport := isMaynardDivisorTuple_of_mem_support hu
    exact ⟨mem_preSievedSimplexTupleSupport_iff.mpr
      ⟨maynardDivisorTupleSupport_subset_preSievedCommonTupleSupport H R W hu,
        huSupport.1⟩, huSupport.2.2⟩
  · intro hu
    have huIndependent := mem_preSievedSimplexTupleSupport_iff.mp hu.1
    have huCommon := huIndependent.1
    have huBox : u ∈ maynardDivisorTupleBox H R := by
      rw [mem_maynardDivisorTupleBox_iff]
      intro h
      have huh := Fintype.mem_piFinset.mp huCommon h
      have huhData := Finset.mem_filter.mp huh
      exact ⟨huhData.2.1, Finset.mem_range.mp huhData.1⟩
    have huCoprime : Nat.Coprime (divisorTupleProduct H u) W := by
      unfold divisorTupleProduct
      apply Nat.Coprime.prod_left
      intro h hh
      exact (preSievedSimplexTupleSupport_coordinate hu.1 h).2.2
    exact mem_maynardDivisorTupleSupport_iff.mpr
      ⟨huBox, ⟨huIndependent.2, huCoprime, hu.2⟩⟩

theorem exists_shared_prime_gt_of_independent_not_maynard
    {H : Finset ℕ} {R D : ℕ} {u : H → ℕ}
    (hu : u ∈ preSievedSimplexTupleSupport H R (primorial D))
    (huNot : u ∉ maynardDivisorTupleSupport H R (primorial D)) :
    ∃ a b : H, ∃ p : ℕ,
      a ≠ b ∧ p.Prime ∧ D < p ∧ p ∣ u a ∧ p ∣ u b := by
  classical
  have huNotSquarefree : ¬Squarefree (divisorTupleProduct H u) := by
    intro huSquarefree
    apply huNot
    rw [maynardDivisorTupleSupport_eq_preSievedSimplex_filter]
    exact Finset.mem_filter.mpr ⟨hu, huSquarefree⟩
  have hnotPairwise : ¬Pairwise (Function.onFun IsRelPrime u) := by
    intro hpairwise
    apply huNotSquarefree
    unfold divisorTupleProduct
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · simpa only [Finset.coe_univ] using Set.pairwise_univ.mpr hpairwise
    · intro h hh
      exact (preSievedSimplexTupleSupport_coordinate hu h).2.1
  have hbad : ∃ a b : H, a ≠ b ∧ ¬IsRelPrime (u a) (u b) := by
    by_contra hnone
    apply hnotPairwise
    intro a b hab
    by_contra hcop
    exact hnone ⟨a, b, hab, hcop⟩
  obtain ⟨a, b, hab, hcop⟩ := hbad
  have hcopNat : ¬Nat.Coprime (u a) (u b) := by
    intro hcopNat
    exact hcop (Nat.coprime_iff_isRelPrime.mp hcopNat)
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcopNat
  have hpGt := prime_gt_of_dvd_coprime_primorial hp hpa
    (preSievedSimplexTupleSupport_coordinate hu a).2.2
  exact ⟨a, b, p, hab, hp, hpGt, hpa, hpb⟩

theorem preSievedSimplexTupleSupport_coordinate_mem_squarefreeRoughUnitSupport
    {H : Finset ℕ} {R D : ℕ} {u : H → ℕ}
    (hu : u ∈ preSievedSimplexTupleSupport H R (primorial D)) (h : H) :
    u h ∈ squarefreeRoughUnitSupport D R := by
  have hdata := preSievedSimplexTupleSupport_coordinate hu h
  have hcommon := (mem_preSievedSimplexTupleSupport_iff.mp hu).1
  have hprodPos : 0 < divisorTupleProduct H u := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro i hi
    exact (preSievedSimplexTupleSupport_coordinate hu i).1
  have hcoordLe : u h ≤ divisorTupleProduct H u :=
    Nat.le_of_dvd hprodPos (divisorTupleCoordinate_dvd_product u h)
  have hcoordLt : u h < R :=
    lt_of_le_of_lt hcoordLe (mem_preSievedSimplexTupleSupport_iff.mp hu).2
  have hcoordPos : 0 < u h := hdata.1
  rw [squarefreeRoughUnitSupport, Finset.mem_insert]
  by_cases hone : u h = 1
  · exact Or.inl hone
  · right
    rw [squarefreeRoughSupport, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hcoordLt.le⟩, hdata.2.1, ?_⟩
    · omega
    · intro p hpMem
      have hpPrime := Nat.prime_of_mem_primeFactors hpMem
      have hpDvd := Nat.dvd_of_mem_primeFactors hpMem
      have hpGt := prime_gt_of_dvd_coprime_primorial hpPrime hpDvd hdata.2.2
      rw [roughPrimeSupport, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨by omega,
        (Nat.le_of_dvd hcoordPos hpDvd).trans hcoordLt.le⟩, hpPrime⟩

def preSievedSimplexCollisionSupport
    (H : Finset ℕ) (R W : ℕ) : Finset (H → ℕ) :=
  (preSievedSimplexTupleSupport H R W).filter fun u =>
    ¬Squarefree (divisorTupleProduct H u)

theorem sum_preSievedSimplex_eq_maynard_add_collision
    (H : Finset ℕ) (R W : ℕ) (f : (H → ℕ) → ℝ) :
    (∑ u ∈ preSievedSimplexTupleSupport H R W, f u) =
      (∑ u ∈ maynardDivisorTupleSupport H R W, f u) +
        ∑ u ∈ preSievedSimplexCollisionSupport H R W, f u := by
  classical
  rw [maynardDivisorTupleSupport_eq_preSievedSimplex_filter]
  unfold preSievedSimplexCollisionSupport
  exact (Finset.sum_filter_add_sum_filter_not
    (preSievedSimplexTupleSupport H R W)
    (fun u => Squarefree (divisorTupleProduct H u)) f).symm

def engelsmaIndependentQuadraticMomentSum
    (alpha : ℝ) (N b c : ℕ) : ℝ :=
  ∑ u ∈ preSievedSimplexTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
    simplexQuadraticIntegrand 105 b c (fun m =>
      normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) u (engelsmaIndexEquiv.symm m)) /
      ∏ h : BoundedGaps.engelsmaTuple,
        (Nat.totient (u h) : ℝ)

def engelsmaCollisionQuadraticMomentSum
    (alpha : ℝ) (N b c : ℕ) : ℝ :=
  ∑ u ∈ preSievedSimplexCollisionSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
    simplexQuadraticIntegrand 105 b c (fun m =>
      normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) u (engelsmaIndexEquiv.symm m)) /
      ∏ h : BoundedGaps.engelsmaTuple,
        (Nat.totient (u h) : ℝ)

theorem engelsmaIndependentQuadraticMomentSum_eq_maynard_add_collision
    (alpha : ℝ) (N b c : ℕ) :
    engelsmaIndependentQuadraticMomentSum alpha N b c =
      engelsmaMaynardYDiagonalQuadraticMomentSum alpha N b c +
        engelsmaCollisionQuadraticMomentSum alpha N b c := by
  exact sum_preSievedSimplex_eq_maynard_add_collision
    BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
    (engelsmaMaynardModulus N) _

theorem engelsmaMaynardYDiagonalQuadraticMomentSum_eq_independent_sub_collision
    (alpha : ℝ) (N b c : ℕ) :
    engelsmaMaynardYDiagonalQuadraticMomentSum alpha N b c =
      engelsmaIndependentQuadraticMomentSum alpha N b c -
        engelsmaCollisionQuadraticMomentSum alpha N b c := by
  rw [engelsmaIndependentQuadraticMomentSum_eq_maynard_add_collision]
  ring

def normalizedEngelsmaIndependentQuadraticMoment
    (alpha : ℝ) (N b c : ℕ) : ℝ :=
  (((N : ℝ) / engelsmaMaynardModulus N) *
      engelsmaIndependentQuadraticMomentSum alpha N b c) /
    engelsmaMaynardScale alpha N

def normalizedEngelsmaCollisionQuadraticMoment
    (alpha : ℝ) (N b c : ℕ) : ℝ :=
  (((N : ℝ) / engelsmaMaynardModulus N) *
      engelsmaCollisionQuadraticMomentSum alpha N b c) /
    engelsmaMaynardScale alpha N

theorem tendsto_normalizedEngelsmaMaynardQuadraticMoment_of_independent_collision
    {alpha L : ℝ} {b c : ℕ}
    (hIndependent : Filter.Tendsto (fun N : ℕ =>
      normalizedEngelsmaIndependentQuadraticMoment alpha N b c)
      Filter.atTop (nhds L))
    (hCollision : Filter.Tendsto (fun N : ℕ =>
      normalizedEngelsmaCollisionQuadraticMoment alpha N b c)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ =>
      normalizedEngelsmaMaynardYDiagonalQuadraticMoment alpha N b c)
      Filter.atTop (nhds L) := by
  have hdiff := hIndependent.sub hCollision
  simpa only [sub_zero] using hdiff.congr'
    (Filter.Eventually.of_forall fun N => by
      unfold normalizedEngelsmaMaynardYDiagonalQuadraticMoment
        normalizedEngelsmaIndependentQuadraticMoment
        normalizedEngelsmaCollisionQuadraticMoment
      rw [engelsmaMaynardYDiagonalQuadraticMomentSum_eq_independent_sub_collision]
      ring)

theorem tendsto_engelsmaMaynardYDiagonal_of_independent_collision_limits
    {alpha : ℝ} (halpha : 0 < alpha)
    (hIndependent : ∀ i j : Fin 42,
      Filter.Tendsto (fun N : ℕ =>
        normalizedEngelsmaIndependentQuadraticMoment alpha N
          (smallKExponentB i + smallKExponentB j)
          (smallKExponentC i + smallKExponentC j))
        Filter.atTop (nhds
          (∫ t in maynardSimplex 105,
            simplexQuadraticIntegrand 105
              (smallKExponentB i + smallKExponentB j)
              (smallKExponentC i + smallKExponentC j) t)))
    (hCollision : ∀ i j : Fin 42,
      Filter.Tendsto (fun N : ℕ =>
        normalizedEngelsmaCollisionQuadraticMoment alpha N
          (smallKExponentB i + smallKExponentB j)
          (smallKExponentC i + smallKExponentC j))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ =>
      (((N : ℝ) / engelsmaMaynardModulus N) *
        engelsmaMaynardYDiagonal alpha N) /
          engelsmaMaynardScale alpha N)
      Filter.atTop (nhds (maynardI 105 smallKCandidate)) := by
  apply tendsto_engelsmaMaynardYDiagonal_of_quadraticMoment_limits halpha
  intro i j
  exact tendsto_normalizedEngelsmaMaynardQuadraticMoment_of_independent_collision
    (hIndependent i j) (hCollision i j)

end BoundedGaps.Maynard
