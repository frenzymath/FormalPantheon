import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Bounded power sums

A finite weighted sum of distinct geometric sequences cannot remain bounded
unless every base with nonzero weight has norm at most one.  This is the
finite-dimensional Vandermonde argument used to turn the even-extension
Stepanov estimate into a bound on the reciprocal roots of the Artin
`L`-polynomial.
-/

namespace Waring.Analytic

open scoped BigOperators

namespace Weil

/-- If all sufficiently late weighted power sums of an injective finite
family of complex numbers are uniformly bounded, then every base carrying a
nonzero weight has norm at most one. -/
theorem norm_le_one_of_bounded_weighted_powerSums {N : Nat}
    (z w : Fin N → Complex) (hz : Function.Injective z)
    (hw : ∀ i, w i ≠ 0) (C : Real) (n0 : Nat)
    (hbound : ∀ n, n0 ≤ n →
      norm (∑ i, w i * z i ^ n) ≤ C) :
    ∀ i, norm (z i) ≤ 1 := by
  let V : Matrix (Fin N) (Fin N) Complex := Matrix.vandermonde z
  have hdet : V.det ≠ 0 := by
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hz
  intro i
  have hC : 0 ≤ C :=
    (norm_nonneg (∑ k, w k * z k ^ n0)).trans (hbound n0 le_rfl)
  let D : Real := ∑ j : Fin N, C * norm (V.adjugate j i)
  have hwindow (n : Nat) :
      (fun j : Fin N => ∑ k, w k * z k ^ (n + (j : Nat))) =
        Matrix.vecMul (fun k => w k * z k ^ n) V := by
    funext j
    simp only [Matrix.vecMul_apply_eq_sum, V, Matrix.vandermonde_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add]
    ring
  have hisolate (n : Nat) :
      Matrix.vecMul
          (fun j : Fin N => ∑ k, w k * z k ^ (n + (j : Nat)))
          V.adjugate i = V.det * (w i * z i ^ n) := by
    rw [hwindow, Matrix.vecMul_vecMul, Matrix.mul_adjugate]
    rw [Matrix.vecMul_smul, Matrix.vecMul_one]
    rfl
  have hlinear (n : Nat) :
      V.det * (w i * z i ^ n) =
        ∑ j : Fin N,
          (∑ k, w k * z k ^ (n + (j : Nat))) * V.adjugate j i := by
    rw [← hisolate n]
    rfl
  have hfinite (n : Nat) (hn : n0 ≤ n) :
      norm (V.det * (w i * z i ^ n)) ≤ D := by
    rw [hlinear]
    calc
      norm (∑ j : Fin N,
          (∑ k, w k * z k ^ (n + (j : Nat))) * V.adjugate j i) ≤
          ∑ j : Fin N,
            norm ((∑ k, w k * z k ^ (n + (j : Nat))) *
              V.adjugate j i) := norm_sum_le _ _
      _ = ∑ j : Fin N,
          norm (∑ k, w k * z k ^ (n + (j : Nat))) *
            norm (V.adjugate j i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul]
      _ ≤ ∑ j : Fin N, C * norm (V.adjugate j i) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (hbound (n + (j : Nat)) (by omega)) (norm_nonneg _)
      _ = D := rfl
  by_contra hi
  have hiOne : 1 < norm (z i) := lt_of_not_ge hi
  have hdetNorm : 0 < norm V.det := norm_pos_iff.mpr hdet
  have hwNorm : 0 < norm (w i) := norm_pos_iff.mpr (hw i)
  have hscale : 0 < norm V.det * norm (w i) := mul_pos hdetNorm hwNorm
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt
    (D / (norm V.det * norm (w i))) hiOne
  let n := m + n0
  have hm_le_n : m ≤ n := by omega
  have hn0_le_n : n0 ≤ n := by omega
  have hpow : norm (z i) ^ m ≤ norm (z i) ^ n :=
    pow_le_pow_right₀ hiOne.le hm_le_n
  have hgrowth : D < (norm V.det * norm (w i)) * norm (z i) ^ n := by
    have hm' : D < norm (z i) ^ m * (norm V.det * norm (w i)) :=
      (div_lt_iff₀ hscale).mp hm
    nlinarith
  have hupper := hfinite n hn0_le_n
  rw [norm_mul, norm_mul, norm_pow] at hupper
  nlinarith

/-- The unweighted specialization of
`norm_le_one_of_bounded_weighted_powerSums`. -/
theorem norm_le_one_of_bounded_powerSums {N : Nat}
    (z : Fin N → Complex) (hz : Function.Injective z)
    (C : Real) (n0 : Nat)
    (hbound : ∀ n, n0 ≤ n → norm (∑ i, z i ^ n) ≤ C) :
    ∀ i, norm (z i) ≤ 1 := by
  simpa using norm_le_one_of_bounded_weighted_powerSums z (fun _ => 1)
    hz (fun _ => one_ne_zero) C n0 (by simpa using hbound)

/-- The finite-type form of
`norm_le_one_of_bounded_weighted_powerSums`. -/
theorem norm_le_one_of_bounded_weighted_powerSums_fintype
    {ι : Type*} [Fintype ι] (z w : ι → Complex)
    (hz : Function.Injective z) (hw : ∀ i, w i ≠ 0)
    (C : Real) (n0 : Nat)
    (hbound : ∀ n, n0 ≤ n → norm (∑ i, w i * z i ^ n) ≤ C) :
    ∀ i, norm (z i) ≤ 1 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let z' : Fin (Fintype.card ι) → Complex := fun j => z (e.symm j)
  let w' : Fin (Fintype.card ι) → Complex := fun j => w (e.symm j)
  have hz' : Function.Injective z' := by
    intro a b hab
    exact e.symm.injective (hz hab)
  have hw' : ∀ j, w' j ≠ 0 := fun j => hw (e.symm j)
  have hbound' : ∀ n, n0 ≤ n →
      norm (∑ j, w' j * z' j ^ n) ≤ C := by
    intro n hn
    have hsum := e.sum_comp (fun j => w' j * z' j ^ n)
    rw [← hsum]
    simpa [z', w'] using hbound n hn
  have hcore := norm_le_one_of_bounded_weighted_powerSums
    z' w' hz' hw' C n0 hbound'
  intro i
  simpa [z'] using hcore (e i)

/-- If the power sums of a finite multiset of complex numbers are uniformly
bounded from some index onward, every member of the multiset has norm at most
one. Repeated values are combined into their positive multiplicity weights
before applying the Vandermonde argument. -/
theorem norm_le_one_of_bounded_multisetPowerSums
    (s : Multiset Complex) (C : Real) (n0 : Nat)
    (hbound : ∀ n, n0 ≤ n →
      norm ((s.map fun z => z ^ n).sum) ≤ C) :
    ∀ z ∈ s, norm z ≤ 1 := by
  classical
  let t := s.toFinset
  let w : t → Complex := fun z => (s.count (z : Complex) : Complex)
  have hw : ∀ z : t, w z ≠ 0 := by
    intro z
    dsimp [w]
    exact Nat.cast_ne_zero.mpr
      (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp z.property)).ne'
  have hbound' : ∀ n, n0 ≤ n →
      norm (∑ z : t, w z * (z : Complex) ^ n) ≤ C := by
    intro n hn
    have hgroup :
        (∑ z ∈ s.toFinset, (s.count z : Complex) * z ^ n) =
          (s.map fun z => z ^ n).sum := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_multiset_map_count s (fun z : Complex => z ^ n)).symm
    rw [show (∑ z : t, w z * (z : Complex) ^ n) =
        ∑ z ∈ s.toFinset, (s.count z : Complex) * z ^ n by
      simpa [t, w] using
        (s.toFinset.sum_attach
          (fun z => (s.count z : Complex) * z ^ n))]
    rw [hgroup]
    exact hbound n hn
  have hcore := norm_le_one_of_bounded_weighted_powerSums_fintype
    (fun z : t => (z : Complex)) w Subtype.val_injective hw C n0 hbound'
  intro z hz
  exact hcore ⟨z, Multiset.mem_toFinset.mpr hz⟩

/-- A square-root-scaled form of the bounded-power-sum argument.  A uniform
bound of size `C * q ^ m` for all sufficiently late even power sums forces
each base to have norm at most `sqrt q`. -/
theorem norm_le_sqrt_of_bounded_even_multisetPowerSums
    (s : Multiset Complex) {q C : Real} (hq : 0 < q) (n0 : Nat)
    (hbound : ∀ m, n0 ≤ m →
      norm ((s.map fun z => z ^ (2 * m)).sum) ≤ C * q ^ m) :
    ∀ z ∈ s, norm z ≤ Real.sqrt q := by
  let u : Multiset Complex := s.map fun z => z ^ 2 / (q : Complex)
  have huBound : ∀ m, n0 ≤ m →
      norm ((u.map fun z => z ^ m).sum) ≤ C := by
    intro m hm
    have hpower :
        (u.map fun z => z ^ m).sum =
          (s.map fun z => z ^ (2 * m)).sum / (q : Complex) ^ m := by
      dsimp [u]
      rw [Multiset.map_map]
      rw [show ((fun z : Complex => z ^ m) ∘
          fun z => z ^ 2 / (q : Complex)) =
          fun z => z ^ (2 * m) / (q : Complex) ^ m by
        funext z
        rw [Function.comp_apply, div_pow, ← pow_mul]]
      exact Multiset.sum_map_div s (fun z => z ^ (2 * m)) ((q : Complex) ^ m)
    rw [hpower, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hq.le]
    rw [div_le_iff₀ (pow_pos hq m)]
    simpa [mul_comm] using hbound m hm
  have hu := norm_le_one_of_bounded_multisetPowerSums u C n0 huBound
  intro z hz
  have hzMem : z ^ 2 / (q : Complex) ∈ u := by
    exact Multiset.mem_map.mpr ⟨z, hz, rfl⟩
  have hzNorm := hu _ hzMem
  rw [norm_div, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hq.le] at hzNorm
  exact Real.le_sqrt_of_sq_le ((div_le_one₀ hq).mp hzNorm)

end Weil

end Waring.Analytic
