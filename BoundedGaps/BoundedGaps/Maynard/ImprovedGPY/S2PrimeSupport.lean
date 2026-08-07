import BoundedGaps.Maynard.ImprovedGPY.S2Pair

noncomputable section

/-!
# Non-reduced shifted progression support for S2

Maynard2013v3, in the proof of `lmm:S2Expression1` (source lines 351--360),
observes that a shift contribution vanishes unless the corresponding divisor
coordinates are both one. This file proves the finite prime-divisibility
version under an explicit scale inequality.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem isMaynard_coordinate_lt_of_R_le
    {H : Finset ℕ} {R N W : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (hRN : R ≤ N) (h : H) : d h < N + h.1 := by
  classical
  have hprod_pos : 0 < divisorTupleProduct H d := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro i hi
    exact Nat.pos_of_ne_zero (hd.coordinate_squarefree i).ne_zero
  have hcoord_le : d h ≤ divisorTupleProduct H d :=
    Nat.le_of_dvd hprod_pos (divisorTupleCoordinate_dvd_product d h)
  have hcoord_R : d h < R := lt_of_le_of_lt hcoord_le hd.1
  exact lt_of_lt_of_le hcoord_R (by omega)

theorem shiftedPrimeProgressionCount_eq_zero_of_coordinate_ne_one
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (hRN : R ≤ N) (h : H)
    (hcoord : d h ≠ 1 ∨ e h ≠ 1) :
    shiftedPrimeProgressionCount N (divisorPairModulus H W d e)
      (divisorPairCrtResidue H R W v d e hd he hcross) h.1 = 0 := by
  classical
  unfold shiftedPrimeProgressionCount
  apply Finset.card_eq_zero.mpr
  ext n
  simp only [Finset.mem_filter]
  constructor
  · intro hn
    have hnrange := Finset.mem_Ico.mp hn.1
    have hmod := hn.2.1
    have hprime := hn.2.2
    have hpair := (modEq_divisorPairCrtResidue_iff hd he hcross n).mp hmod
    rcases hcoord with hdh | heh
    · have hdiv : d h ∣ n + h.1 := hpair.2.1 h
      obtain hone | hsame := (Nat.dvd_prime hprime).mp hdiv
      · exact (hdh hone).elim
      · have hlt : d h < n + h.1 := by
          apply lt_of_lt_of_le
          · exact isMaynard_coordinate_lt_of_R_le hd hRN h
          · omega
        exact (by omega : False).elim
    · have hdiv : e h ∣ n + h.1 := hpair.2.2 h
      obtain hone | hsame := (Nat.dvd_prime hprime).mp hdiv
      · exact (heh hone).elim
      · have hlt : e h < n + h.1 := by
          apply lt_of_lt_of_le
          · exact isMaynard_coordinate_lt_of_R_le he hRN h
          · omega
        exact (by omega : False).elim
  · intro hn
    simp at hn

end BoundedGaps.Maynard
