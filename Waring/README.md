# WaringMathlib

A Lean 4 and Mathlib formalization of Chen Jingrun's theorem `g(5) = 37`,
without project-specific axioms. In other words, every positive integer is a
sum of at most 37 fifth powers of nonnegative integers, and 37 is the smallest
uniform bound with this property. The formalization has passed the independent
[`leanprover/comparator`](https://github.com/leanprover/comparator) check.

## Statement

`Waring.Statement.HasPowerSumRepresentation k s n` says that `n` is a sum of
`s` natural-number `k`th powers. Zero summands are allowed, so fixed slots are
equivalent to a sum of at most `s` positive powers. The main result is:

```lean
theorem Waring.Main.g_five_eq_thirtySeven :
    Waring.Statement.MainTheorem
```

`MainTheorem` unfolds to `IsLeastUniversalWaringBound 5 37`: every positive
natural number is a sum of at most 37 fifth powers, and no smaller uniform bound
works.

## Proof

The lower bound is obtained from the elementary obstruction at 223. The upper
bound combines a checked finite certificate and Dickson ascent below the large
number threshold with a formalization of Chen's circle-method argument above
it. `Waring/Main.lean` performs the final finite/large split and assembles both
bounds.

## Primary reference

The proof primarily follows Chen Jingrun's 1964 result:

- 陈景润，《华林问题中 `g(5) = 37`》，《数学学报》14(5) (1964),
  715--734, [doi:10.12386/A1964sxxb0065](https://doi.org/10.12386/A1964sxxb0065).
- Jing-Run Chen, *Waring's Problem for `g(5) = 37`*, *Scientia Sinica* 13
  (1964), 1547--1568,
  [doi:10.1360/ya1964-13-10-1547](https://doi.org/10.1360/ya1964-13-10-1547).

## Verification

The project has passed `leanprover/comparator`'s independent statement, kernel,
and axiom checks for the single declaration listed in `Comparator/config.json`,
namely `Waring.Comparator.g_five_eq_thirtySeven`. The checked solution uses
only `propext`, `Quot.sound`, and `Classical.choice`.

The project pins Lean through `lean-toolchain` and Mathlib through
`lakefile.toml` and `lake-manifest.json`. Build the production proof and the
review interface with:

```sh
lake build Waring Comparator
```

`Comparator/` follows the standard comparator layout:

- `Challenge.lean` contains the frozen definitions and the single theorem
  statement.
- `Solution.lean` repeats those definitions and closes that theorem from the
  production proof.
- `config.json` lists the compared declaration and permits only `propext`,
  `Quot.sound`, and `Classical.choice`.

With compatible `comparator`, `lean4export`, and `landrun` binaries available,
run the independent statement, kernel, and axiom check with:

```sh
lake env /path/to/comparator Comparator/config.json
```
