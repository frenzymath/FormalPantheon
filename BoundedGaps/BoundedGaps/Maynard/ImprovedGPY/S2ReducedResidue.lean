import BoundedGaps.Maynard.ImprovedGPY.S2Restricted
import Mathlib.Data.Nat.GCD.Prime

noncomputable section

/-!
# Reduced CRT residues for shifted S2 progressions

Maynard2013v3, in the proof of `lmm:S2Expression1` (source lines 351--360),
uses that the translated CRT class is reduced precisely on the surviving
`d_h=e_h=1` contribution. This file proves the needed forward implication with
the pre-sieve and shift-difference hypotheses explicit.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem shiftedDivisorPairCrtResidue_coprime
    {H : Finset ℕ} {R W v : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (h : H) (hdh : d h = 1) (heh : e h = 1) :
    Nat.Coprime
      (divisorPairCrtResidue H R W v d e hd he hcross + h.1)
      (divisorPairModulus H W d e) := by
  classical
  let a := divisorPairCrtResidue H R W v d e hd he hcross
  have haCrt : a ≡ divisorPairCrtResidue H R W v d e hd he hcross
      [MOD divisorPairModulus H W d e] := Nat.ModEq.refl _
  obtain ⟨haW, haPair⟩ :=
    (modEq_divisorPairCrtResidue_iff hd he hcross a).mp haCrt
  have hcopW : Nat.Coprime (a + h.1) W :=
    preSieve_coprime_of_modEq haW (hv h h.property)
  have hcopProduct : Nat.Coprime (a + h.1)
      (∏ j : H, divisorTupleLcm H d e j) := by
    apply Nat.Coprime.prod_right
    intro j hj
    by_cases hjh : j = h
    · subst j
      simp [divisorTupleLcm, hdh, heh]
    · by_contra hnot
      obtain ⟨p, hp, hpa, hplcm⟩ :=
        Nat.Prime.not_coprime_iff_dvd.mp hnot
      have hpde : p ∣ d j ∨ p ∣ e j := hp.dvd_or_dvd_of_dvd_lcm hplcm
      have hpaj : p ∣ a + j.1 := by
        rcases hpde with hpd | hpe
        · exact dvd_trans hpd (haPair.1 j)
        · exact dvd_trans hpe (haPair.2 j)
      have hpdist : p ∣ Nat.dist h.1 j.1 := by
        by_cases hle : h.1 ≤ j.1
        · have hsub : p ∣ (a + j.1) - (a + h.1) := Nat.dvd_sub hpaj hpa
          rw [Nat.dist_eq_sub_of_le hle]
          simpa [Nat.add_sub_add_left] using hsub
        · have hle' : j.1 ≤ h.1 := le_of_not_ge hle
          have hsub : p ∣ (a + h.1) - (a + j.1) := Nat.dvd_sub hpa hpaj
          rw [Nat.dist_comm h.1 j.1, Nat.dist_eq_sub_of_le hle']
          simpa [Nat.add_sub_add_left] using hsub
      have hpW : p ∣ W := hcoverage (Ne.symm hjh) p hp hpdist
      have hpcopW : Nat.Coprime p W := by
        rcases hpde with hpd | hpe
        · exact (hd.coordinate_coprime_W j).coprime_dvd_left hpd
        · exact (he.coordinate_coprime_W j).coprime_dvd_left hpe
      exact (hp.coprime_iff_not_dvd.mp hpcopW) hpW
  simpa [a, divisorPairModulus] using hcopW.mul_right hcopProduct

theorem shiftedDivisorPairCrtResidue_mod_mem_coprimeResidues
    {H : Finset ℕ} {R W v : ℕ} {d e : H → ℕ}
    (hW : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (h : H) (hdh : d h = 1) (heh : e h = 1) :
    (divisorPairCrtResidue H R W v d e hd he hcross + h.1) %
        divisorPairModulus H W d e ∈
      coprimeResidues (divisorPairModulus H W d e) := by
  have hq := divisorPairModulus_pos hW hd he
  have hcop := shiftedDivisorPairCrtResidue_coprime
    hd he hcross hcoverage hv h hdh heh
  simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact Nat.mod_lt _ hq
  · simpa [Nat.coprime_iff_gcd_eq_one] using hcop

theorem shiftedDivisorPairCrtResidue_intervalDiscrepancy_le_global_max
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hW : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (h : H) (hdh : d h = 1) (heh : e h = 1)
    (hN : 0 < N) :
    shiftedPrimeProgressionIntervalDiscrepancy N
        (divisorPairModulus H W d e)
        (divisorPairCrtResidue H R W v d e hd he hcross) h.1 ≤
      maxProgressionDiscrepancy (2 * N + h.1 - 1)
          (divisorPairModulus H W d e) +
        maxProgressionDiscrepancy (N + h.1 - 1)
          (divisorPairModulus H W d e) := by
  apply shiftedPrimeProgressionIntervalDiscrepancy_le_global_max hN
    (divisorPairModulus_pos hW hd he)
  exact shiftedDivisorPairCrtResidue_mod_mem_coprimeResidues
    hW hd he hcross hcoverage hv h hdh heh

end BoundedGaps.Maynard
