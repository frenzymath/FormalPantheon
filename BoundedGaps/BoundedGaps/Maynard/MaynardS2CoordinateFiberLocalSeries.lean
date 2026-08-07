import BoundedGaps.Maynard.ConcreteRoughModulusPrimeLogMass
import BoundedGaps.Maynard.MaynardS2CoordinateFiberAbel

noncomputable section

/-!
Prime-local data for the S2 coordinate fiber.
Maynard2013v3, source lines 522--528, uses the off-coordinate product as an
extra modulus in the one-dimensional partial-summation lemma.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real
open scoped BigOperators

theorem maynardS2OffCoordinateProduct_dvd_divisorTupleProduct
    {H : Finset ℕ} (m : H) (r : H → ℕ) :
    maynardS2OffCoordinateProduct H m r ∣ divisorTupleProduct H r := by
  unfold maynardS2OffCoordinateProduct divisorTupleProduct
  exact Finset.prod_dvd_prod_of_subset
    (Finset.univ.erase m) Finset.univ r (Finset.erase_subset _ _)

theorem maynardS2OffCoordinateProduct_squarefree
    {H : Finset ℕ} {R W : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R W r) :
    Squarefree (maynardS2OffCoordinateProduct H m r) := by
  exact hr.2.2.squarefree_of_dvd
    (maynardS2OffCoordinateProduct_dvd_divisorTupleProduct m r)

theorem maynardS2OffCoordinateProduct_coprime
    {H : Finset ℕ} {R W : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R W r) :
    Nat.Coprime W (maynardS2OffCoordinateProduct H m r) := by
  exact (Nat.Coprime.of_dvd_left
    (maynardS2OffCoordinateProduct_dvd_divisorTupleProduct m r)
    hr.2.1).symm

theorem maynardS2OffCoordinateProduct_lt
    {H : Finset ℕ} {R W : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R W r) :
    maynardS2OffCoordinateProduct H m r < R := by
  have htotalPos : 0 < divisorTupleProduct H r :=
    Nat.pos_of_ne_zero hr.2.2.ne_zero
  exact (Nat.le_of_dvd htotalPos
    (maynardS2OffCoordinateProduct_dvd_divisorTupleProduct m r)).trans_lt
      hr.1

noncomputable def maynardS2CoordinateFiberSingularSeries
    (D : ℕ) {H : Finset ℕ} (m : H) (r : H → ℕ) : ℝ :=
  augmentedPreSieveSingularSeries D
    (maynardS2OffCoordinateProduct H m r)

theorem maynardS2CoordinateFiberSingularSeries_eq_preSieve_mul
    {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R (primorial D) r) :
    maynardS2CoordinateFiberSingularSeries D m r =
      preSieveSingularSeries D *
        ((Nat.totient (maynardS2OffCoordinateProduct H m r) : ℝ) /
          maynardS2OffCoordinateProduct H m r) := by
  exact augmentedPreSieveSingularSeries_eq_preSieve_mul
    (maynardS2OffCoordinateProduct_pos m r hr)
    (maynardS2OffCoordinateProduct_coprime m r hr)

theorem maynardS2CoordinateFiberSingularSeries_pos
    {H : Finset ℕ} {D R : ℕ} (m : H) (r : H → ℕ)
    (hr : IsMaynardDivisorTuple H R (primorial D) r) :
    0 < maynardS2CoordinateFiberSingularSeries D m r := by
  have hP := maynardS2OffCoordinateProduct_pos m r hr
  have hM : 0 < primorial D * maynardS2OffCoordinateProduct H m r :=
    Nat.mul_pos (primorial_pos D) hP
  have hphi : 0 < Nat.totient
      (primorial D * maynardS2OffCoordinateProduct H m r) :=
    Nat.totient_pos.mpr hM
  unfold maynardS2CoordinateFiberSingularSeries
  rw [augmentedPreSieveSingularSeries_eq_totient_div hP]
  exact div_pos (by exact_mod_cast hphi) (by exact_mod_cast hM)

theorem maynardS2CoordinateFiberCoefficient_prime_eq_augmentedGammaWeight
    {H : Finset ℕ} (D : ℕ) (m : H) (r : H → ℕ)
    {p : ℕ} (hp : p.Prime) :
    maynardS2CoordinateFiberCoefficient H (primorial D) m r p =
      augmentedPreSieveGamma D
          (maynardS2OffCoordinateProduct H m r) p /
        ((p : ℝ) - augmentedPreSieveGamma D
          (maynardS2OffCoordinateProduct H m r) p) := by
  exact squarefreeCoprimeInvTotientAF_prime_eq_augmentedGammaWeight
    D (maynardS2OffCoordinateProduct H m r) hp

theorem exists_uniform_maynardS2CoordinateFiberPrimeLogInterval_bounds :
    ∃ K C : ℝ, 0 < K ∧
      ∀ {H : Finset ℕ} {D R w z : ℕ} (m : H) {r : H → ℕ},
        IsMaynardDivisorTuple H R (primorial D) r →
        2 ≤ Real.log R → 2 ≤ w → w ≤ z →
        -(K + Real.log D + (Real.log (Real.log R) + C + 2)) ≤
            augmentedPreSievedPrimeLogIntervalSum D
                (maynardS2OffCoordinateProduct H m r) w z -
              Real.log ((z : ℝ) / (w : ℝ)) ∧
          augmentedPreSievedPrimeLogIntervalSum D
                (maynardS2OffCoordinateProduct H m r) w z -
              Real.log ((z : ℝ) / (w : ℝ)) ≤ K := by
  obtain ⟨K, C, hK, hinterval⟩ :=
    exists_uniform_augmentedPreSievedPrimeLogInterval_logarithmic_bounds
  refine ⟨K, C, hK, ?_⟩
  intro H D R w z m r hr hlogR hw hwz
  exact hinterval
    (maynardS2OffCoordinateProduct_pos m r hr)
    (maynardS2OffCoordinateProduct_squarefree m r hr)
    (maynardS2OffCoordinateProduct_lt m r hr) hlogR hw hwz

end BoundedGaps.Maynard
