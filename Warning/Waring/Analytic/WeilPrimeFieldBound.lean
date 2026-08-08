import Waring.Analytic.WeilPrimeFieldIdentity
import Waring.Analytic.WeilRootRadius
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# The pure additive Weil bound over a prime field

The degree-one Euler identity writes the complete sum as the first power sum
of the Artin reciprocal roots.  Their square-root radius and the strict Artin
degree bound give the classical factor `d - 1`.
 -/

namespace Waring.Analytic

open scoped BigOperators

namespace Weil

/-- The standard pure-additive Weil estimate for a phase whose highest
nonzero exponent is `d < p`. -/
theorem norm_pointPhase_sum_le
    {p d : Nat} [Fact p.Prime] (hp : 1 < p)
    (hdpos : 0 < d) (hdp : d < p)
    (b : Fin 5 → ZMod p) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (pointPhase b x)‖ ≤
      ((d - 1 : Nat) : Real) * Real.sqrt (p : Real) := by
  letI : NeZero p := ⟨by omega⟩
  have hcharacter :
      (ZMod.stdAddChar : AddChar (ZMod p) Complex) ≠ 1 := by
    intro htrivial
    have hprimitive := ZMod.isPrimitive_stdAddChar p
    have hshift := hprimitive (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, htrivial] at hshift
    exact hshift rfl
  have hdcast : (d : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hdpos hdp
  let roots := (artinLPolynomial ZMod.stdAddChar b d).reverse.roots
  have hidentity := pointPhase_sum_eq_neg_artinRootSum
    ZMod.stdAddChar hcharacter b hdpos hd5 hbtop hb hdcast
  have hradius : ∀ z ∈ roots, ‖z‖ ≤ Real.sqrt (p : Real) :=
    norm_artinLPolynomial_reverse_root_le_sqrt
      hp hdpos hdp b hd5 hbtop hb
  have hcardLt : roots.card < d := by
    simpa only [roots] using
      (card_roots_reverse_artinLPolynomial_lt
        (K := ZMod p) ZMod.stdAddChar b hdpos)
  have hcard : roots.card ≤ d - 1 := by omega
  have hsumNorm :
      (roots.map fun z ↦ ‖z‖).sum ≤
        roots.card • Real.sqrt (p : Real) := by
    have hmapped := Multiset.sum_le_card_nsmul
      (roots.map fun z ↦ ‖z‖) (Real.sqrt (p : Real)) (by
        intro r hr
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
        exact hradius z hz)
    simpa only [Multiset.card_map] using hmapped
  have hidentity' :
      (∑ x : ZMod p, ZMod.stdAddChar (pointPhase b x)) =
        -roots.sum := by
    simpa only [roots, pow_one, Multiset.map_id'] using hidentity
  rw [hidentity', norm_neg]
  calc
    ‖roots.sum‖ ≤ (roots.map fun z ↦ ‖z‖).sum :=
      norm_multiset_sum_le roots
    _ ≤ roots.card • Real.sqrt (p : Real) := hsumNorm
    _ = (roots.card : Real) * Real.sqrt (p : Real) := by
      rw [nsmul_eq_mul]
    _ ≤ ((d - 1 : Nat) : Real) * Real.sqrt (p : Real) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Real.sqrt_nonneg _)

end Weil

end Waring.Analytic
