# Chess

A [Lean 4](https://lean-lang.org) library of definitions and proofs about chess.

The board, pieces, and empty-board attack geometry are specified as Lean
types and predicates. Theorems in the library are machine-checked: `lake build`
fails if any of them stops being true of the definitions.

## Requirements

* [elan](https://github.com/leanprover/elan), which will install the Lean
  toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.33.0`)
* this package depends on [mathlib](https://github.com/leanprover-community/mathlib4)
  at the matching `v4.33.0` tag

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

## Build

From the repository root:

```bash
lake exe cache get   # download prebuilt mathlib (strongly recommended)
lake build
```

CI runs the same `lake build` via [lean-action](https://github.com/leanprover/lean-action).

## Library layout

| Module | Contents |
| --- | --- |
| `Chess.Color` | White and black, and the involution swapping them |
| `Chess.Square` | Files, ranks, the 64 squares, and square colors |
| `Chess.Piece` | Piece kinds and colored pieces |
| `Chess.Board` | Placements, including the standard starting position |
| `Chess.Geometry` | Empty-board attacks (bishop, rook, queen, king, knight) |

Import the whole library with `import Chess`, or import a single module.

Sample facts already in the library:

* there are 64 squares and 12 distinct colored pieces
* `a1` is a black square; opposite corners have the same color
* the starting position has 32 pieces, 16 per side, with unique kings on `e1` and `e8`
* bishops stay on one square-color; knights always change square-color
* a knight on `a1` attacks exactly `b3` and `c2`

## Adding proofs

1. Put new definitions and theorems in the existing module they belong to, or
   add a file `Chess/YourTopic.lean` and `import` it from `Chess.lean`.
2. Prefer hypotheses that match the current geometry: empty-board attacks do
   not yet account for blocking pieces, pins, or check.
3. Run `lake build` before opening a pull request.
