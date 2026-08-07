import BoundedGaps.Maynard.SmallKCertificate

/-!
# Small-degree composition-weight table

This file kernel-checks the finite composition sums used by the archived
`smallKGFormula` for degrees at most ten.  Isolating the executable list
calculation keeps the later symbolic dimension recurrence compact.
-/

namespace BoundedGaps.Maynard

set_option maxRecDepth 100000

def smallKCompositionWeightTable : Fin 11 → Fin 11 → ℕ := ![
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 12, 4, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 120, 48, 8, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1680, 624, 144, 16, 0, 0, 0, 0, 0, 0],
  ![0, 30240, 9600, 2304, 384, 32, 0, 0, 0, 0, 0],
  ![0, 665280, 175680, 39168, 7296, 960, 64, 0, 0, 0, 0],
  ![0, 17297280, 3790080, 743040, 136704, 21120, 2304, 128, 0, 0, 0],
  ![0, 518918400, 95235840, 16001280, 2716416, 433920, 57600, 5376, 256, 0, 0],
  ![0, 17643225600, 2752081920, 393154560, 59166720, 9077760, 1290240,
    150528, 12288, 512, 0],
  ![0, 670442572800, 90328089600, 11008327680, 1437143040, 201848832,
    28477440, 3655680, 380928, 27648, 1024]
]

theorem smallKCompositionWeight_sum_eq_table (b r : Fin 11) :
    ((smallKPositiveCompositions b.1 r.1).map smallKCompositionWeight).sum =
      smallKCompositionWeightTable b r := by
  fin_cases b <;> fin_cases r <;> decide

theorem smallKCompositionWeight_sum_eq_table_nat (b r : ℕ)
    (hb : b < 11) (hr : r < 11) :
    ((smallKPositiveCompositions b r).map smallKCompositionWeight).sum =
      smallKCompositionWeightTable ⟨b, hb⟩ ⟨r, hr⟩ := by
  exact smallKCompositionWeight_sum_eq_table ⟨b, hb⟩ ⟨r, hr⟩

theorem smallKCompositionWeight_cast_sum_eq_table_nat (b r : ℕ)
    (hb : b < 11) (hr : r < 11) :
    (List.map (Nat.cast ∘ smallKCompositionWeight)
        (smallKPositiveCompositions b r)).sum =
      (smallKCompositionWeightTable ⟨b, hb⟩ ⟨r, hr⟩ : ℚ) := by
  rw [← List.map_map]
  change (List.map (Nat.castRingHom ℚ)
      (List.map smallKCompositionWeight
        (smallKPositiveCompositions b r))).sum = _
  rw [List.sum_hom]
  exact congrArg (Nat.castRingHom ℚ)
    (smallKCompositionWeight_sum_eq_table_nat b r hb hr)

end BoundedGaps.Maynard
