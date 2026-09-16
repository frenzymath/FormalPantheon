import Mathlib.Data.Vector.Basic

/-!
# Definitions for exact fractional-moment certificates

This module contains only common constants and proof-carrying indices. Concrete
vector data and finite checks remain in separate modules.
-/

namespace PrimesRestrictedDigits

def moment235CertificateDenominator : Nat := 10 ^ 18

def moment235CertificateGrowthNumerator : Nat := 136854

def moment235CertificateGrowthDenominator : Nat := 100000

def moment235RepresentativeDigit (a : Fin 5) : Fin 10 :=
  ⟨a.val, lt_trans a.isLt (by omega)⟩

private def moment235ReflectedIndex (state : Fin 10000) : Fin 5000 :=
  if hstate : state.val < 5000 then ⟨state.val, hstate⟩
  else
    ⟨9999 - state.val, by
      have hlt := state.isLt
      omega⟩

def moment235HalfVectorEntry
    (values : Vector (Vector Nat 100) 50) (index : Fin 5000) : Nat :=
  let block : Fin 50 := ⟨index.val / 100, by
    have hindex := index.isLt
    omega⟩
  let offset : Fin 100 :=
    ⟨index.val % 100, Nat.mod_lt _ (by omega)⟩
  (values.get block).get offset

def moment235ReflectedHalfVectorEntry
    (values : Vector (Vector Nat 100) 50) (state : Fin 10000) : Nat :=
  moment235HalfVectorEntry values (moment235ReflectedIndex state)

theorem moment235ReflectedHalfVectorEntry_reflect
    (values : Vector (Vector Nat 100) 50) (state : Fin 10000) :
    moment235ReflectedHalfVectorEntry values
        ⟨9999 - state.val, by omega⟩ =
      moment235ReflectedHalfVectorEntry values state := by
  unfold moment235ReflectedHalfVectorEntry
  apply congrArg (moment235HalfVectorEntry values)
  apply Fin.ext
  simp only [moment235ReflectedIndex]
  split_ifs <;> simp only [] <;> omega

theorem moment235ReflectedHalfVectorEntry_le_of_blocked
    (values : Vector (Vector Nat 100) 50) (scale : Nat)
    (hblocked : forall (block : Fin 50) (offset : Fin 100),
      scale <= moment235HalfVectorEntry values
        ⟨block.val * 100 + offset.val, by omega⟩)
    (state : Fin 10000) :
    scale <= moment235ReflectedHalfVectorEntry values state := by
  let index := moment235ReflectedIndex state
  let block : Fin 50 := ⟨index.val / 100, by
    have hindex := index.isLt
    omega⟩
  let offset : Fin 100 :=
    ⟨index.val % 100, Nat.mod_lt _ (by omega)⟩
  have h := hblocked block offset
  have hindex :
      (⟨block.val * 100 + offset.val, by omega⟩ : Fin 5000) = index := by
    apply Fin.ext
    dsimp [block, offset]
    omega
  rw [hindex] at h
  exact h

def moment235IncomingPreviousIndex
    (first : Fin 10) (future : Fin 10000) : Fin 10000 :=
  ⟨1000 * first.val + future.val / 10, by
    have hfirst := first.isLt
    have hfuture := future.isLt
    omega⟩

end PrimesRestrictedDigits
