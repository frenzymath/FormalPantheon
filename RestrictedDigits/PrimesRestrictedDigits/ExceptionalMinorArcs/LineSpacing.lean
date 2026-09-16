import PrimesRestrictedDigits.BasicEstimates.IntegerVectors
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spacing of integer points on a real line

This module proves the finite collinear-spacing repair for Lemma 15.1 of
`MAYNARD-PRD-PUBLISHED`, pp. 209--210. The published standalone lemma is false for a line
containing no nonzero integer point; the repaired statement assumes explicitly that the finite
carrier has at least two points.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem sum_fin_adjacent_sub
    {G : Type*} [AddCommGroup G] {n : Nat} (f : Fin (n + 1) -> G) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  cases n with
  | zero => simp
  | succ n =>
      have h := Fin.sum_Iic_sub (Fin.last n) f
      rw [show Finset.Iic (Fin.last n) = Finset.univ by
        apply Finset.eq_univ_of_forall
        intro i
        simpa using Fin.le_last i] at h
      simpa [Finset.sum_sub_distrib] using h

private theorem exists_scaled_coordinate_gap
    {alpha : Type*} [Fintype alpha] (e : alpha ↪ Real)
    (hcard : 2 <= Fintype.card alpha) :
    ∃ x y lower upper : alpha,
      e x < e y ∧ e lower < e upper ∧
        (e y - e x) *
            ((Fintype.card alpha - 1 : Nat) : Real) <=
          e upper - e lower := by
  let n := Fintype.card alpha - 2
  have hn : Fintype.card alpha = n + 2 := by
    dsimp [n]
    omega
  letI : LinearOrder alpha := LinearOrder.lift' e e.injective
  have huniv : (Finset.univ : Finset alpha).card = n + 2 := by
    simpa using hn
  let ordered : Fin (n + 2) ↪o alpha :=
    (Finset.univ : Finset alpha).orderEmbOfFin huniv
  let coordinate : Fin (n + 2) -> Real := fun i => e (ordered i)
  let gap : Fin (n + 1) -> Real := fun i =>
    coordinate i.succ - coordinate i.castSucc
  let span : Real := coordinate (Fin.last (n + 1)) - coordinate 0
  have hsum : ∑ i, gap i = span := by
    simpa [gap, span] using sum_fin_adjacent_sub coordinate
  have hsum_scaled :
      ∑ i, gap i * ((n + 1 : Nat) : Real) <=
        ∑ _i : Fin (n + 1), span := by
    apply le_of_eq
    calc
      ∑ i, gap i * ((n + 1 : Nat) : Real) =
          (∑ i, gap i) * ((n + 1 : Nat) : Real) := by
            rw [Finset.sum_mul]
      _ = span * ((n + 1 : Nat) : Real) := by rw [hsum]
      _ = ∑ _i : Fin (n + 1), span := by
        simp [nsmul_eq_mul]
        ring
  obtain ⟨i, _hi_mem, hi⟩ :=
    Finset.exists_le_of_sum_le (s := Finset.univ)
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
      hsum_scaled
  refine ⟨ordered i.castSucc, ordered i.succ, ordered 0,
    ordered (Fin.last (n + 1)), ?_, ?_, ?_⟩
  · exact ordered.strictMono Fin.castSucc_lt_succ
  · apply ordered.strictMono
    apply Fin.mk_lt_mk.mpr
    change 0 < n + 1
    omega
  · simpa [gap, span, coordinate, hn] using hi

/--
Among at least two integer points on a real line, one nonzero difference is simultaneously
short for the Euclidean norm and for any fixed integral linear functional. This is the
cardinal-sharp finite repair.
-/
theorem exists_collinear_intVector_spacing
    (line : Submodule Real (EuclideanSpace Real (Fin 3)))
    (hline : Module.finrank Real line = 1)
    (A : Fin 3 -> Int) (S : Finset (Fin 3 -> Int))
    (N Delta : Real) (_hN : 0 <= N) (_hDelta : 0 <= Delta)
    (hcard : 2 <= S.card)
    (hmem : ∀ z ∈ S, intVectorToEuclidean z ∈ line)
    (hnorm : ∀ z ∈ S, ‖intVectorToEuclidean z‖ <= N)
    (hdot : ∀ z ∈ S,
      |((intVectorDot z A : Int) : Real)| <= Delta) :
    ∃ v : Fin 3 -> Int,
      v ≠ 0 ∧
      ‖intVectorToEuclidean v‖ *
          ((S.card - 1 : Nat) : Real) <= 2 * N ∧
      |((intVectorDot v A : Int) : Real)| *
          ((S.card - 1 : Nat) : Real) <= 2 * Delta := by
  let E : Real ≃ₗ[Real] line :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one hline).some
  let point : S -> line := fun z =>
    ⟨intVectorToEuclidean z.1, hmem z.1 z.2⟩
  let coordinate : S -> Real := fun z => E.symm (point z)
  have hcoordinate : Function.Injective coordinate := by
    intro z w hzw
    have hp : point z = point w := E.symm.injective (by
      simpa [coordinate] using hzw)
    apply Subtype.ext
    apply intVectorToEuclidean_injective
    exact congrArg Subtype.val hp
  let coordinateEmbedding : S ↪ Real := ⟨coordinate, hcoordinate⟩
  have hcardS : 2 <= Fintype.card S := by
    simpa using hcard
  obtain ⟨x, y, lower, upper, hxy, _hlowerUpper, hgap⟩ :=
    exists_scaled_coordinate_gap coordinateEmbedding hcardS
  let u : EuclideanSpace Real (Fin 3) := (E 1 : line)
  have hembed (z : S) :
      intVectorToEuclidean z.1 = coordinate z • u := by
    have hp : point z = coordinate z • E 1 := by
      calc
        point z = E (coordinate z) := by
          change point z = E (E.symm (point z))
          exact (E.apply_symm_apply (point z)).symm
        _ = E (coordinate z • (1 : Real)) := by simp
        _ = coordinate z • E 1 := E.map_smul _ _
    exact congrArg Subtype.val hp
  let gap := coordinate y - coordinate x
  let span := coordinate upper - coordinate lower
  have hgap' :
      gap * ((S.card - 1 : Nat) : Real) <= span := by
    simpa [gap, span, Fintype.card_coe, coordinateEmbedding] using hgap
  have hgap_nonneg : 0 <= gap := sub_nonneg.mpr hxy.le
  have hspan_nonneg : 0 <= span :=
    (mul_nonneg hgap_nonneg (by positivity)).trans hgap'
  let v : Fin 3 -> Int := y.1 - x.1
  have hv_ne : v ≠ 0 := by
    intro hv
    have hyx : y.1 = x.1 := sub_eq_zero.mp hv
    have : y = x := Subtype.ext hyx
    exact hxy.ne (congrArg coordinate this).symm
  have hv_embed : intVectorToEuclidean v = gap • u := by
    rw [show intVectorToEuclidean v =
        intVectorToEuclidean y.1 - intVectorToEuclidean x.1 by
      simp [v]]
    rw [hembed y, hembed x]
    simp [gap, sub_smul]
  have hspan_embed :
      intVectorToEuclidean upper.1 - intVectorToEuclidean lower.1 =
        span • u := by
    rw [hembed upper, hembed lower]
    simp [span, sub_smul]
  have hnorm_scaled :
      ‖intVectorToEuclidean v‖ * ((S.card - 1 : Nat) : Real) <=
        ‖intVectorToEuclidean upper.1 -
          intVectorToEuclidean lower.1‖ := by
    rw [hv_embed, hspan_embed, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgap_nonneg,
      abs_of_nonneg hspan_nonneg]
    have h := mul_le_mul_of_nonneg_right hgap' (norm_nonneg u)
    nlinarith
  have hnorm_endpoints :
      ‖intVectorToEuclidean upper.1 -
          intVectorToEuclidean lower.1‖ <= 2 * N := by
    calc
      ‖intVectorToEuclidean upper.1 -
          intVectorToEuclidean lower.1‖ <=
          ‖intVectorToEuclidean upper.1‖ +
            ‖intVectorToEuclidean lower.1‖ := norm_sub_le _ _
      _ <= N + N := add_le_add
        (hnorm upper.1 upper.2) (hnorm lower.1 lower.2)
      _ = 2 * N := by ring
  have hdot_scaled :
      |((intVectorDot v A : Int) : Real)| *
          ((S.card - 1 : Nat) : Real) <=
        |((intVectorDot upper.1 A : Int) : Real) -
          ((intVectorDot lower.1 A : Int) : Real)| := by
    have hv_inner :
        inner Real (intVectorToEuclidean v) (intVectorToEuclidean A) =
          gap * inner Real u (intVectorToEuclidean A) := by
      rw [hv_embed]
      rw [inner_smul_left]
      norm_num
    have hspan_inner :
        inner Real (intVectorToEuclidean upper.1)
            (intVectorToEuclidean A) -
          inner Real (intVectorToEuclidean lower.1)
            (intVectorToEuclidean A) =
          span * inner Real u (intVectorToEuclidean A) := by
      rw [hembed upper, hembed lower]
      rw [inner_smul_left, inner_smul_left]
      norm_num
      dsimp [span]
      ring
    rw [intVectorDot_cast_eq_inner, intVectorDot_cast_eq_inner,
      intVectorDot_cast_eq_inner, hv_inner, hspan_inner, abs_mul, abs_mul,
      abs_of_nonneg hgap_nonneg, abs_of_nonneg hspan_nonneg]
    have h := mul_le_mul_of_nonneg_right hgap'
      (abs_nonneg (inner Real u (intVectorToEuclidean A)))
    nlinarith
  have hdot_endpoints :
      |((intVectorDot upper.1 A : Int) : Real) -
          ((intVectorDot lower.1 A : Int) : Real)| <= 2 * Delta := by
    calc
      |((intVectorDot upper.1 A : Int) : Real) -
          ((intVectorDot lower.1 A : Int) : Real)| <=
          |((intVectorDot upper.1 A : Int) : Real)| +
            |((intVectorDot lower.1 A : Int) : Real)| := abs_sub _ _
      _ <= Delta + Delta := add_le_add
        (hdot upper.1 upper.2) (hdot lower.1 lower.2)
      _ = 2 * Delta := by ring
  exact ⟨v, hv_ne, hnorm_scaled.trans hnorm_endpoints,
    hdot_scaled.trans hdot_endpoints⟩

end PrimesRestrictedDigits
