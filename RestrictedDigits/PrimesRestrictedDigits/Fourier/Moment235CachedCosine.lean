import PrimesRestrictedDigits.Fourier.CertificateData.Moment235CosineValues4

/-!
# Exact small-denominator cosine lookup

This module assembles the checked 100-entry cache blocks into one
proof-carrying lookup and derives its signed rational upper bound.
-/

set_option maxRecDepth 1000000

namespace PrimesRestrictedDigits

def moment235CosineGroupValue
    (group : Fin 50) (block : Fin 10) (offset : Fin 100) : Int :=
  match group.val with
  | 0 => moment235CosineGroup00Value block offset
  | 1 => moment235CosineGroup01Value block offset
  | 2 => moment235CosineGroup02Value block offset
  | 3 => moment235CosineGroup03Value block offset
  | 4 => moment235CosineGroup04Value block offset
  | 5 => moment235CosineGroup05Value block offset
  | 6 => moment235CosineGroup06Value block offset
  | 7 => moment235CosineGroup07Value block offset
  | 8 => moment235CosineGroup08Value block offset
  | 9 => moment235CosineGroup09Value block offset
  | 10 => moment235CosineGroup10Value block offset
  | 11 => moment235CosineGroup11Value block offset
  | 12 => moment235CosineGroup12Value block offset
  | 13 => moment235CosineGroup13Value block offset
  | 14 => moment235CosineGroup14Value block offset
  | 15 => moment235CosineGroup15Value block offset
  | 16 => moment235CosineGroup16Value block offset
  | 17 => moment235CosineGroup17Value block offset
  | 18 => moment235CosineGroup18Value block offset
  | 19 => moment235CosineGroup19Value block offset
  | 20 => moment235CosineGroup20Value block offset
  | 21 => moment235CosineGroup21Value block offset
  | 22 => moment235CosineGroup22Value block offset
  | 23 => moment235CosineGroup23Value block offset
  | 24 => moment235CosineGroup24Value block offset
  | 25 => moment235CosineGroup25Value block offset
  | 26 => moment235CosineGroup26Value block offset
  | 27 => moment235CosineGroup27Value block offset
  | 28 => moment235CosineGroup28Value block offset
  | 29 => moment235CosineGroup29Value block offset
  | 30 => moment235CosineGroup30Value block offset
  | 31 => moment235CosineGroup31Value block offset
  | 32 => moment235CosineGroup32Value block offset
  | 33 => moment235CosineGroup33Value block offset
  | 34 => moment235CosineGroup34Value block offset
  | 35 => moment235CosineGroup35Value block offset
  | 36 => moment235CosineGroup36Value block offset
  | 37 => moment235CosineGroup37Value block offset
  | 38 => moment235CosineGroup38Value block offset
  | 39 => moment235CosineGroup39Value block offset
  | 40 => moment235CosineGroup40Value block offset
  | 41 => moment235CosineGroup41Value block offset
  | 42 => moment235CosineGroup42Value block offset
  | 43 => moment235CosineGroup43Value block offset
  | 44 => moment235CosineGroup44Value block offset
  | 45 => moment235CosineGroup45Value block offset
  | 46 => moment235CosineGroup46Value block offset
  | 47 => moment235CosineGroup47Value block offset
  | 48 => moment235CosineGroup48Value block offset
  | 49 => moment235CosineGroup49Value block offset
  | _ => 0

theorem moment235CosineGroupValue_certificate
    (group : Fin 50) (block : Fin 10) (offset : Fin 100) :
    (moment235CosineScale : Int) *
        rationalCosineUpper20D20FixedNumerator
          ((group.val * 10 + block.val) * 100 + offset.val) <=
      (rationalCosineUpper20D20FixedDenominator : Int) *
        moment235CosineGroupValue group block offset := by
  fin_cases group
  · convert moment235CosineGroup00_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup00Value];
      exact Or.inl rfl
  · convert moment235CosineGroup01_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup01Value];
      exact Or.inl rfl
  · convert moment235CosineGroup02_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup02Value];
      exact Or.inl rfl
  · convert moment235CosineGroup03_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup03Value];
      exact Or.inl rfl
  · convert moment235CosineGroup04_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup04Value];
      exact Or.inl rfl
  · convert moment235CosineGroup05_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup05Value];
      exact Or.inl rfl
  · convert moment235CosineGroup06_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup06Value];
      exact Or.inl rfl
  · convert moment235CosineGroup07_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup07Value];
      exact Or.inl rfl
  · convert moment235CosineGroup08_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup08Value];
      exact Or.inl rfl
  · convert moment235CosineGroup09_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup09Value];
      exact Or.inl rfl
  · convert moment235CosineGroup10_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup10Value];
      exact Or.inl rfl
  · convert moment235CosineGroup11_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup11Value];
      exact Or.inl rfl
  · convert moment235CosineGroup12_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup12Value];
      exact Or.inl rfl
  · convert moment235CosineGroup13_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup13Value];
      exact Or.inl rfl
  · convert moment235CosineGroup14_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup14Value];
      exact Or.inl rfl
  · convert moment235CosineGroup15_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup15Value];
      exact Or.inl rfl
  · convert moment235CosineGroup16_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup16Value];
      exact Or.inl rfl
  · convert moment235CosineGroup17_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup17Value];
      exact Or.inl rfl
  · convert moment235CosineGroup18_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup18Value];
      exact Or.inl rfl
  · convert moment235CosineGroup19_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup19Value];
      exact Or.inl rfl
  · convert moment235CosineGroup20_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup20Value];
      exact Or.inl rfl
  · convert moment235CosineGroup21_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup21Value];
      exact Or.inl rfl
  · convert moment235CosineGroup22_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup22Value];
      exact Or.inl rfl
  · convert moment235CosineGroup23_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup23Value];
      exact Or.inl rfl
  · convert moment235CosineGroup24_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup24Value];
      exact Or.inl rfl
  · convert moment235CosineGroup25_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup25Value];
      exact Or.inl rfl
  · convert moment235CosineGroup26_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup26Value];
      exact Or.inl rfl
  · convert moment235CosineGroup27_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup27Value];
      exact Or.inl rfl
  · convert moment235CosineGroup28_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup28Value];
      exact Or.inl rfl
  · convert moment235CosineGroup29_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup29Value];
      exact Or.inl rfl
  · convert moment235CosineGroup30_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup30Value];
      exact Or.inl rfl
  · convert moment235CosineGroup31_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup31Value];
      exact Or.inl rfl
  · convert moment235CosineGroup32_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup32Value];
      exact Or.inl rfl
  · convert moment235CosineGroup33_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup33Value];
      exact Or.inl rfl
  · convert moment235CosineGroup34_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup34Value];
      exact Or.inl rfl
  · convert moment235CosineGroup35_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup35Value];
      exact Or.inl rfl
  · convert moment235CosineGroup36_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup36Value];
      exact Or.inl rfl
  · convert moment235CosineGroup37_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup37Value];
      exact Or.inl rfl
  · convert moment235CosineGroup38_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup38Value];
      exact Or.inl rfl
  · convert moment235CosineGroup39_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup39Value];
      exact Or.inl rfl
  · convert moment235CosineGroup40_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup40Value];
      exact Or.inl rfl
  · convert moment235CosineGroup41_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup41Value];
      exact Or.inl rfl
  · convert moment235CosineGroup42_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup42Value];
      exact Or.inl rfl
  · convert moment235CosineGroup43_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup43Value];
      exact Or.inl rfl
  · convert moment235CosineGroup44_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup44Value];
      exact Or.inl rfl
  · convert moment235CosineGroup45_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup45Value];
      exact Or.inl rfl
  · convert moment235CosineGroup46_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup46Value];
      exact Or.inl rfl
  · convert moment235CosineGroup47_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup47Value];
      exact Or.inl rfl
  · convert moment235CosineGroup48_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup48Value];
      exact Or.inl rfl
  · convert moment235CosineGroup49_certificate block offset using 1 <;>
      simp [moment235CosineGroupValue, moment235CosineGroup49Value];
      exact Or.inl rfl

def moment235CosineBlockLookup (index : Fin 50000) : Int :=
  let group : Fin 50 := ⟨index.val / 1000, by
    have hindex := index.isLt
    omega⟩
  let block : Fin 10 := ⟨index.val / 100 % 10, Nat.mod_lt _ (by omega)⟩
  let offset : Fin 100 := ⟨index.val % 100, Nat.mod_lt _ (by omega)⟩
  moment235CosineGroupValue group block offset

theorem moment235CosineBlockLookup_certificate (index : Fin 50000) :
    (moment235CosineScale : Int) *
        rationalCosineUpper20D20FixedNumerator index.val <=
      (rationalCosineUpper20D20FixedDenominator : Int) *
        moment235CosineBlockLookup index := by
  let group : Fin 50 := ⟨index.val / 1000, by
    have hindex := index.isLt
    omega⟩
  let block : Fin 10 := ⟨index.val / 100 % 10, Nat.mod_lt _ (by omega)⟩
  let offset : Fin 100 := ⟨index.val % 100, Nat.mod_lt _ (by omega)⟩
  have h := moment235CosineGroupValue_certificate group block offset
  have hindex :
      (group.val * 10 + block.val) * 100 + offset.val = index.val := by
    dsimp [group, block, offset]
    omega
  change (moment235CosineScale : Int) *
      rationalCosineUpper20D20FixedNumerator index.val <=
    (rationalCosineUpper20D20FixedDenominator : Int) *
      moment235CosineGroupValue group block offset
  rw [← hindex]
  exact h

def moment235CosineUpperNumerator (index : Fin 50001) : Int :=
  if hindex : index.val < 50000 then
    moment235CosineBlockLookup ⟨index.val, hindex⟩
  else
    moment235CosineEndpoint

theorem moment235CosineUpperNumerator_certificate (index : Fin 50001) :
    (moment235CosineScale : Int) *
        rationalCosineUpper20D20FixedNumerator index.val <=
      (rationalCosineUpper20D20FixedDenominator : Int) *
        moment235CosineUpperNumerator index := by
  by_cases hindex : index.val < 50000
  · simpa [moment235CosineUpperNumerator, hindex] using
      moment235CosineBlockLookup_certificate
        (⟨index.val, hindex⟩ : Fin 50000)
  · have hvalue : index.val = 50000 := by
      have hlt := index.isLt
      omega
    simpa [moment235CosineUpperNumerator, hindex, hvalue] using
      moment235CosineEndpoint_certificate

theorem rationalCosineUpper20D20FixedNumerator_neg
    (x : Int) :
    rationalCosineUpper20D20FixedNumerator (-x) =
      rationalCosineUpper20D20FixedNumerator x := by
  simp [rationalCosineUpper20D20FixedNumerator]

end PrimesRestrictedDigits
