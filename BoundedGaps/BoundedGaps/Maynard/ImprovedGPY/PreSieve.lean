import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Primorial

import BoundedGaps.Foundations.Admissible

/-!
# The pre-sieving residue class

Maynard2013v3, Section 5 outline (source lines 193--200), uses admissibility
and the Chinese remainder theorem to choose `v₀` with every `v₀+h` coprime to
the product of the small primes.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators Function

theorem exists_preSieveResidueClass
    {H P : Finset ℕ} (hH : BoundedGaps.IsAdmissible H)
    (hP : ∀ p ∈ P, p.Prime) :
    ∃ v : ℕ, v < ∏ p ∈ P, p ∧
      ∀ h ∈ H, Nat.Coprime (v + h) (∏ p ∈ P, p) := by
  classical
  have havoided : ∀ p ∈ P, ∃ a < p, ∀ h ∈ H, h % p ≠ a := by
    intro p hp
    exact (BoundedGaps.isAdmissible_iff_avoids_residue H).mp hH p (hP p hp)
  choose chosen chosen_lt chosen_avoid using havoided
  let a : ℕ → ℕ := fun p => if hp : p ∈ P then chosen p hp else 0
  have ha_lt : ∀ p ∈ P, a p < p := by
    intro p hp
    simp [a, hp, chosen_lt p hp]
  have ha_avoid : ∀ p ∈ P, ∀ h ∈ H, h % p ≠ a p := by
    intro p hp
    simpa [a, hp] using chosen_avoid p hp
  let residue : ℕ → ℕ := fun p => p - a p
  have hnonzero : ∀ p ∈ P, p ≠ 0 := by
    intro p hp
    exact (hP p hp).ne_zero
  have hpairwise : Set.Pairwise (P : Set ℕ) (Nat.Coprime on id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  let v : ℕ := Nat.chineseRemainderOfFinset residue id P hnonzero hpairwise
  refine ⟨v, Nat.chineseRemainderOfFinset_lt_prod residue id hnonzero hpairwise,
    ?_⟩
  intro h hh
  apply Nat.Coprime.prod_right
  intro p hp
  apply Nat.Coprime.symm
  apply (hP p hp).coprime_iff_not_dvd.mpr
  intro hpdiv
  have hv : v ≡ residue p [MOD p] :=
    (Nat.chineseRemainderOfFinset residue id P hnonzero hpairwise).property p hp
  have hzero : v + h ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpdiv
  have hzero_residue : 0 ≡ residue p + h [MOD p] :=
    hzero.symm.trans (hv.add_right h)
  have hadd := hzero_residue.add_right (a p)
  have ha_le : a p ≤ p := (ha_lt p hp).le
  have ha_ph : a p ≡ p + h [MOD p] := by
    dsimp [residue] at hadd
    convert hadd using 1 <;> omega
  have hph_h : p + h ≡ h [MOD p] := by
    simp [Nat.ModEq]
  have hah : a p ≡ h [MOD p] := ha_ph.trans hph_h
  have hmod : h % p = a p := by
    unfold Nat.ModEq at hah
    simpa [Nat.mod_eq_of_lt (ha_lt p hp)] using hah.symm
  exact ha_avoid p hp h hh hmod

theorem exists_preSieveResidueClass_primorial
    {H : Finset ℕ} (hH : BoundedGaps.IsAdmissible H) (D₀ : ℕ) :
    ∃ v : ℕ, v < primorial D₀ ∧
      ∀ h ∈ H, Nat.Coprime (v + h) (primorial D₀) := by
  simpa [primorial_eq_prod_primesLE] using
    exists_preSieveResidueClass (H := H) (P := D₀.primesLE) hH
      (fun p hp => Nat.prime_of_mem_primesLE hp)

theorem preSieve_coprime_of_modEq
    {v W n h : ℕ} (hnv : n ≡ v [MOD W])
    (hv : Nat.Coprime (v + h) W) :
    Nat.Coprime (n + h) W := by
  by_contra hnot
  obtain ⟨p, hp, hpn, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hnh : n + h ≡ v + h [MOD W] := hnv.add_right h
  have hnhp : n + h ≡ v + h [MOD p] := Nat.ModEq.of_dvd hpW hnh
  have hvzero : v + h ≡ 0 [MOD p] :=
    hnhp.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpn)
  have hp_coprime : Nat.Coprime p (v + h) :=
    (Nat.Coprime.of_dvd_right hpW hv).symm
  exact (hp.coprime_iff_not_dvd.mp hp_coprime)
    (Nat.modEq_zero_iff_dvd.mp hvzero)

theorem preSieve_divisor_coprime_of_modEq
    {v W n h d : ℕ} (hnv : n ≡ v [MOD W])
    (hv : Nat.Coprime (v + h) W) (hd : d ∣ n + h) :
    Nat.Coprime d W :=
  Nat.Coprime.of_dvd_left hd (preSieve_coprime_of_modEq hnv hv)

end BoundedGaps.Maynard
