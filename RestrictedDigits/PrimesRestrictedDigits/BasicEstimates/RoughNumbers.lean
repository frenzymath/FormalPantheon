import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Positive integers with all prime factors above a threshold

This is the source-exact finite carrier. It differs from Mathlib's non-smooth-number carrier
by requiring every prime factor to be large and by including one.
-/

namespace PrimesRestrictedDigits

def weakRoughNumbersUpTo (N k : Nat) : Finset Nat :=
  (Finset.Icc 1 N).filter fun n => ∀ p ∈ n.primeFactors, k <= p

@[simp] theorem mem_weakRoughNumbersUpTo {N k n : Nat} :
    n ∈ weakRoughNumbersUpTo N k ↔
      1 <= n ∧ n <= N ∧ ∀ p, p.Prime → p ∣ n → k <= p := by
  simp only [weakRoughNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hnOne, hnN⟩, hprimeFactors⟩
    refine ⟨hnOne, hnN, ?_⟩
    intro p hp hdvd
    exact hprimeFactors p (hp.mem_primeFactors hdvd (Nat.ne_of_gt hnOne))
  · rintro ⟨hnOne, hnN, hprimeDivisors⟩
    refine ⟨⟨hnOne, hnN⟩, ?_⟩
    intro p hp
    exact hprimeDivisors p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)

@[simp] theorem mem_weakRoughNumbersUpTo_iff_minFac {N k n : Nat} :
    n ∈ weakRoughNumbersUpTo N k ↔
      1 <= n ∧ n <= N ∧ (n = 1 ∨ k <= n.minFac) := by
  rw [mem_weakRoughNumbersUpTo]
  exact and_congr_right fun _ => and_congr_right fun _ => Nat.le_minFac.symm

noncomputable def buchstabRoughNumbers (x y : Real) : Finset Nat :=
  weakRoughNumbersUpTo (Nat.floor x) (Nat.ceil y)

@[simp] theorem mem_buchstabRoughNumbers {x y : Real} {n : Nat} :
    n ∈ buchstabRoughNumbers x y ↔
      1 <= n ∧ (n : Real) <= x ∧
        ∀ p, p.Prime → p ∣ n → y <= (p : Real) := by
  rw [buchstabRoughNumbers, mem_weakRoughNumbersUpTo]
  constructor
  · rintro ⟨hnOne, hnFloor, hprimeFactors⟩
    have hnNe : n ≠ 0 := Nat.ne_of_gt hnOne
    refine ⟨hnOne, (Nat.le_floor_iff' hnNe).mp hnFloor, ?_⟩
    intro p hp hdvd
    exact Nat.ceil_le.mp (hprimeFactors p hp hdvd)
  · rintro ⟨hnOne, hnx, hprimeFactors⟩
    have hnNe : n ≠ 0 := Nat.ne_of_gt hnOne
    refine ⟨hnOne, (Nat.le_floor_iff' hnNe).mpr hnx, ?_⟩
    intro p hp hdvd
    exact Nat.ceil_le.mpr (hprimeFactors p hp hdvd)

@[simp] theorem buchstabRoughNumbers_natCast (N k : Nat) :
    buchstabRoughNumbers (N : Real) (k : Real) =
      weakRoughNumbersUpTo N k := by
  simp [buchstabRoughNumbers]

noncomputable def buchstabPhi (x y : Real) : Nat :=
  (buchstabRoughNumbers x y).card

@[simp] theorem zero_not_mem_buchstabRoughNumbers (x y : Real) :
    0 ∉ buchstabRoughNumbers x y := by
  simp

theorem one_mem_buchstabRoughNumbers {x y : Real} (hx : 1 <= x) :
    1 ∈ buchstabRoughNumbers x y := by
  rw [mem_buchstabRoughNumbers]
  refine ⟨le_rfl, by simpa using hx, ?_⟩
  intro p hp hdvd
  exact (hp.not_dvd_one hdvd).elim

end PrimesRestrictedDigits
