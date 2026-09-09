import Chess.Color
import Chess.Square
import Chess.Piece
import Chess.Board
import Chess.Geometry
import Chess.Position
import Chess.GameState
import Chess.FinishedGame

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
* `Chess.Position` — board, side to move, castling rights, and en passant
* `Chess.GameState` — current position together with the historical positions
* `Chess.FinishedGame` — completed games: positions, repetition claims, and outcomes
-/
