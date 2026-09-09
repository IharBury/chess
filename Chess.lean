import Chess.Color
import Chess.Square
import Chess.Piece
import Chess.Board
import Chess.Geometry

/-!
# Chess

A Lean 4 library of definitions and proofs about chess.

The modules are layered so that later files can depend on earlier ones
without circular imports:

* `Chess.Color` — player colors
* `Chess.Square` — files, ranks, and the 64 squares
* `Chess.Piece` — piece kinds and colored pieces
* `Chess.Board` — placements of pieces, including the starting position
* `Chess.Geometry` — empty-board attack geometry and its basic theorems
-/
