import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankIntegralBounds
import PrimesRestrictedDigits.BasicEstimates.SlabBallIntegerPoints
import PrimesRestrictedDigits.ExceptionalMinorArcs.GeometryOfNumbersCoordinates
import PrimesRestrictedDigits.LatticeEstimates.GeneratingPointDilation
import PrimesRestrictedDigits.LatticeEstimates.RankTwoPullback
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Geometry-of-numbers concentration in a slab-ball

This is the repaired formalization of `MAYNARD-PRD-PUBLISHED`, Lemma 13.2,
pp. 193--195. The source's final image condition is corrected from
`phi(x) in R` to `x in phi(R)`, equivalently `phi^-1(x) in R`.
-/

noncomputable section

open scoped BigOperators

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The explicit absolute threshold obtained from the verified constant-nine
rank-three LLL coordinate estimate. -/
def geometryOfNumbersK0 : Real := 314928

/-- Points of a finite integer carrier lying in a rank-two integral lattice. -/
def pointsInRankTwoIntegralLattice (Lambda : RankTwoIntegralLattice)
    (S : Finset (Fin 3 -> Int)) : Finset (Fin 3 -> Int) :=
  by
    classical
    exact S.filter fun z => intVectorToEuclidean z ∈ Lambda.carrier

private theorem sum_real_smul_integralBasis_repr_finThree
    (L : Submodule Int E) (b : Module.Basis (Fin 3) Int L) (x : L) :
    (∑ i, ((b.repr x i : Int) : Real) • (b i : E)) = (x : E) := by
  calc
    (∑ i, ((b.repr x i : Int) : Real) • (b i : E)) =
        ∑ i, (((b.repr x i : Int) • b i : L) : E) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Int.cast_smul_eq_zsmul]
      rfl
    _ = ((∑ i, (b.repr x i : Int) • b i : L) : E) := by
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    _ = (x : E) := by rw [b.sum_repr]

private theorem basis_repr_mul_norm_le_eighteen
    (L : Submodule Int E) (b : Module.Basis (Fin 3) Int L)
    (hweighted : ∀ a : Fin 3 -> Real,
      ∑ i, ‖a i • (b i : E)‖ <=
        9 * ‖∑ i, a i • (b i : E)‖)
    (N : Real) (x : L) (hx : ‖(x : E)‖ <= 2 * N) (i : Fin 3) :
    ((|b.repr x i| : Int) : Real) * ‖(b i : E)‖ <= 18 * N := by
  let a : Fin 3 -> Real := fun j => (b.repr x j : Int)
  have hterm : ‖a i • (b i : E)‖ <=
      ∑ j, ‖a j • (b j : E)‖ := by
    exact Finset.single_le_sum (s := Finset.univ)
      (fun j _ => norm_nonneg (a j • (b j : E))) (Finset.mem_univ i)
  have hreconstruct : (∑ j, a j • (b j : E)) = (x : E) :=
    sum_real_smul_integralBasis_repr_finThree L b x
  calc
    ((|b.repr x i| : Int) : Real) * ‖(b i : E)‖ =
        ‖a i • (b i : E)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      simp [a, Int.cast_abs]
    _ <= ∑ j, ‖a j • (b j : E)‖ := hterm
    _ <= 9 * ‖∑ j, a j • (b j : E)‖ := hweighted a
    _ = 9 * ‖(x : E)‖ := by rw [hreconstruct]
    _ <= 9 * (2 * N) := mul_le_mul_of_nonneg_left hx (by norm_num)
    _ = 18 * N := by ring

private theorem one_le_cast_abs_of_ne_zero {z : Int} (hz : z ≠ 0) :
    (1 : Real) <= ((|z| : Int) : Real) := by
  have hnat : 1 <= z.natAbs := Int.natAbs_pos.mpr hz
  have hreal : (1 : Real) <= (z.natAbs : Real) := by
    exact_mod_cast hnat
  simpa [Nat.cast_natAbs, Int.cast_abs] using hreal

/-- Finite-carrier strengthening of Maynard's Lemma 13.2. At the explicit
threshold, one exact rank-two integral lattice contains every carrier point. -/
theorem exists_rankTwoIntegralLattice_geometryOfNumbers
    (t : E) (N delta K : Real)
    (ht : ‖t‖ = 1) (hN : 0 < N) (hdelta : 0 < delta)
    (hK : geometryOfNumbersK0 <= K)
    (S : Finset (Fin 3 -> Int))
    (hS : ∀ z ∈ S,
      ‖intVectorToEuclidean z‖ <= N ∧
        abs (inner Real t (intVectorToEuclidean z)) <= delta)
    (hcard : delta * K * N ^ 2 <= (S.card : Real)) :
    ∃ Lambda : RankTwoIntegralLattice,
      ∀ z ∈ S, intVectorToEuclidean z ∈ Lambda.carrier := by
  classical
  have ht0 : t ≠ 0 := by
    intro hzero
    simp [hzero] at ht
  let scale : Real := N / delta
  have hscale : 0 < scale := div_pos hN hdelta
  let L := dilatedFullIntegerLattice t scale ht0 hscale.ne'
  let pointMap : (Fin 3 -> Int) -> L :=
    intVectorInDilatedFullLattice t scale ht0 hscale.ne'
  let T : Finset L := S.image pointMap
  have hpointMap : Function.Injective pointMap :=
    intVectorInDilatedFullLattice_injective t scale ht0 hscale.ne'
  have hcardTS : T.card = S.card :=
    Finset.card_image_of_injective S hpointMap
  obtain ⟨b, hmono, hweighted⟩ :=
    exists_sortedIntegralBasis_finThree L
      (dilatedFullIntegerLatticeBasis t scale ht0 hscale.ne')
  let V : Fin 3 -> Real := fun i => ‖(b i : E)‖
  have hVpos : ∀ i, 0 < V i := by
    intro i
    apply norm_pos_iff.mpr
    intro hzero
    exact b.ne_zero i (Subtype.ext hzero)
  have hTnorm : ∀ x ∈ T, ‖(x : E)‖ <= 2 * N := by
    intro x hx
    simp only [T, Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [show ((pointMap z : L) : E) =
        directionalDilation t scale ht0 hscale.ne'
          (intVectorToEuclidean z) by
      simp [pointMap, L]]
    have hprojection :
        ‖lineProjection t (intVectorToEuclidean z)‖ <= delta := by
      rw [norm_lineProjection_eq_abs_inner_div_norm t ht0, ht, div_one]
      exact (hS z hz).2
    calc
      ‖directionalDilation t scale ht0 hscale.ne'
          (intVectorToEuclidean z)‖ <=
          ‖intVectorToEuclidean z‖ +
            scale * ‖lineProjection t (intVectorToEuclidean z)‖ :=
        norm_directionalDilation_le t scale ht0 hscale
          (intVectorToEuclidean z)
      _ <= N + scale * delta := by
        exact add_le_add (hS z hz).1
          (mul_le_mul_of_nonneg_left hprojection hscale.le)
      _ = 2 * N := by
        dsimp [scale]
        field_simp [hdelta.ne']
        ring
  have hcoord : ∀ x ∈ T, ∀ i,
      ((|b.repr x i| : Int) : Real) * V i <= 18 * N := by
    intro x hx i
    exact basis_repr_mul_norm_le_eighteen L b hweighted N x
      (hTnorm x hx) i
  have hprodLower : scale <= V 0 * V 1 * V 2 := by
    simpa [V, Fin.prod_univ_three] using
      dilationScale_le_prod_norm_integralBasis t scale ht0 hscale b
  have hcardT : delta * K * N ^ 2 <= (T.card : Real) := by
    rw [hcardTS]
    exact hcard
  have hlong : 18 * N < V 2 := by
    by_contra hnot
    have hV2 : V 2 <= 18 * N := le_of_not_gt hnot
    have hVB : ∀ i, V i <= 18 * N := by
      intro i
      fin_cases i
      · exact (hmono (by decide : (0 : Fin 3) <= 2)).trans hV2
      · exact (hmono (by decide : (1 : Fin 3) <= 2)).trans hV2
      · exact hV2
    have hbox : (T.card : Real) * (V 0 * V 1 * V 2) <=
        27 * (18 * N) ^ 3 :=
      card_mul_basisWeights_finThree_le b T V (18 * N)
        hVpos hVB hcoord
    have hscaleCount : (T.card : Real) * scale <=
        27 * (18 * N) ^ 3 :=
      (mul_le_mul_of_nonneg_left hprodLower (Nat.cast_nonneg T.card)).trans hbox
    have hscaleCountDelta :=
      mul_le_mul_of_nonneg_right hscaleCount hdelta.le
    have hupperMul : (T.card : Real) * N <=
        (157464 * delta * N ^ 2) * N := by
      calc
        (T.card : Real) * N = (T.card : Real) * scale * delta := by
          dsimp [scale]
          field_simp [hdelta.ne']
        _ <= (27 * (18 * N) ^ 3) * delta := hscaleCountDelta
        _ = (157464 * delta * N ^ 2) * N := by ring
    have hupper : (T.card : Real) <= 157464 * delta * N ^ 2 :=
      le_of_mul_le_mul_right hupperMul hN
    have hKexplicit : (314928 : Real) <= K := by
      simpa [geometryOfNumbersK0] using hK
    have hdeltaNnonneg : 0 <= delta * N ^ 2 :=
      mul_nonneg hdelta.le (sq_nonneg N)
    have hlower : 314928 * delta * N ^ 2 <= (T.card : Real) := by
      calc
        314928 * delta * N ^ 2 = 314928 * (delta * N ^ 2) := by ring
        _ <= K * (delta * N ^ 2) :=
          mul_le_mul_of_nonneg_right hKexplicit hdeltaNnonneg
        _ = delta * K * N ^ 2 := by ring
        _ <= (T.card : Real) := hcardT
    have hdeltaNpos : 0 < delta * N ^ 2 :=
      mul_pos hdelta (sq_pos_of_pos hN)
    nlinarith
  have hthird : ∀ x ∈ T, b.repr x 2 = 0 := by
    intro x hx
    by_contra hne
    have hone : (1 : Real) <= ((|b.repr x 2| : Int) : Real) :=
      one_le_cast_abs_of_ne_zero hne
    have hV2le : V 2 <=
        ((|b.repr x 2| : Int) : Real) * V 2 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hone (hVpos 2).le
    exact (not_le_of_gt hlong) (hV2le.trans (hcoord x hx 2))
  let Lambda := rankTwoPullbackOfDilatedBasis t scale ht0 hscale.ne' b
  refine ⟨Lambda, ?_⟩
  intro z hz
  apply intVector_mem_rankTwoPullbackOfDilatedBasis_of_repr_two_eq_zero
  apply hthird
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

/-- Source-range strengthening for an arbitrary finite carrier. -/
theorem exists_rankTwoIntegralLattice_geometryOfNumbers_of_strict
    (t : E) (N delta K : Real)
    (ht : ‖t‖ = 1) (hN : 1 < N)
    (hdelta : 0 < delta) (_hdeltaOne : delta < 1)
    (hK : geometryOfNumbersK0 < K)
    (S : Finset (Fin 3 -> Int))
    (hS : ∀ z ∈ S,
      ‖intVectorToEuclidean z‖ <= N ∧
        abs (inner Real t (intVectorToEuclidean z)) <= delta)
    (hcard : delta * K * N ^ 2 <= (S.card : Real)) :
    ∃ Lambda : RankTwoIntegralLattice,
      delta * K * N ^ 2 / 2 <=
        ((pointsInRankTwoIntegralLattice Lambda S).card : Real) := by
  classical
  obtain ⟨Lambda, hLambda⟩ :=
    exists_rankTwoIntegralLattice_geometryOfNumbers t N delta K ht
      (zero_lt_one.trans hN) hdelta hK.le S hS hcard
  refine ⟨Lambda, ?_⟩
  have hfilter : pointsInRankTwoIntegralLattice Lambda S = S :=
    by simpa [pointsInRankTwoIntegralLattice] using
      Finset.filter_eq_self.2 hLambda
  rw [hfilter]
  linarith

/-- Literal specialization to all integer points in the source's closed
slab-ball. -/
theorem exists_rankTwoIntegralLattice_slabBall_of_strict
    (t : E) (N delta K : Real)
    (ht : ‖t‖ = 1) (hN : 1 < N)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hK : geometryOfNumbersK0 < K)
    (hcard : delta * K * N ^ 2 <=
      ((integerPointsInSlabBall t N delta).card : Real)) :
    ∃ Lambda : RankTwoIntegralLattice,
      delta * K * N ^ 2 / 2 <=
        ((pointsInRankTwoIntegralLattice Lambda
          (integerPointsInSlabBall t N delta)).card : Real) := by
  apply exists_rankTwoIntegralLattice_geometryOfNumbers_of_strict
    t N delta K ht hN hdelta hdeltaOne hK
  · intro z hz
    exact (mem_integerPointsInSlabBall_iff t
      (zero_lt_one.trans hN).le z).1 hz
  · exact hcard

end PrimesRestrictedDigits
