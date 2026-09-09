import Chess.Color
import Chess.Square
import Chess.Piece
import Chess.Board
import Chess.Geometry
import Chess.Valid
import Chess.Position
import Chess.PositionValid
import Chess.Check
import Chess.Move
import Chess.Checkmate
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
* `Chess.Valid` — occupied-board attacks and whether a placement is valid
* `Chess.Position` — board, side to move, castling rights, and en passant
* `Chess.PositionValid` — whether a position (board, turn, castling, en passant) is valid
* `Chess.Check` — whether the player to move is in check or double check
* `Chess.Move` — moves (including distinct promotions), playing them, and legal-move enumeration
* `Chess.Checkmate` — whether the player to move is checkmated
* `Chess.GameState` — current position together with the historical positions
* `Chess.FinishedGame` — completed games: positions, declarations, technical ends, and outcomes
-/
